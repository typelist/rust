// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use abi::{FnType, FnTypeExt};
use callee;
use common::*;
use builder::Builder;
use consts;
use monomorphize;
use type_::Type;
use value::Value;

use rustc::ty::{self, Ty, ToPolyTraitRef};
use rustc::ty::layout::HasDataLayout;
use rustc::traits::own_vtable_methods;
use debuginfo;

use std::cmp::Ordering;

#[derive(Copy, Clone, Debug)]
pub struct VirtualIndex(u64);

pub const DESTRUCTOR: VirtualIndex = VirtualIndex(0);
pub const SIZE: VirtualIndex = VirtualIndex(1);
pub const ALIGN: VirtualIndex = VirtualIndex(2);

impl<'a, 'tcx> VirtualIndex {
    pub fn from_index(index: usize) -> Self {
        VirtualIndex(index as u64 + 3)
    }

    pub fn get_fn(self, bx: &Builder<'a, 'll, 'tcx>,
                  llvtable: &'ll Value,
                  fn_ty: &FnType<'tcx, Ty<'tcx>>) -> &'ll Value {
        // Load the data pointer from the object.
        debug!("get_fn({:?}, {:?})", llvtable, self);

        let llvtable = bx.pointercast(llvtable, fn_ty.llvm_type(bx.cx).ptr_to().ptr_to());
        let ptr_align = bx.tcx().data_layout.pointer_align;
        let ptr = bx.load(bx.inbounds_gep(llvtable, &[C_usize(bx.cx, self.0)]), ptr_align);
        bx.nonnull_metadata(ptr);
        // Vtable loads are invariant
        bx.set_invariant_load(ptr);
        ptr
    }

    pub fn get_usize(self, bx: &Builder<'a, 'll, 'tcx>, llvtable: &'ll Value) -> &'ll Value {
        // Load the data pointer from the object.
        debug!("get_int({:?}, {:?})", llvtable, self);

        let llvtable = bx.pointercast(llvtable, Type::isize(bx.cx).ptr_to());
        let usize_align = bx.tcx().data_layout.pointer_align;
        let ptr = bx.load(bx.inbounds_gep(llvtable, &[C_usize(bx.cx, self.0)]), usize_align);
        // Vtable loads are invariant
        bx.set_invariant_load(ptr);
        ptr
    }
}

/// Creates a dynamic vtable for the given type and vtable origin.
/// This is used only for objects.
///
/// The vtables are cached instead of created on every call.
///
/// The `trait_ref` encodes the erased self type. Hence if we are
/// making an object `Foo<Trait>` from a value of type `Foo<T>`, then
/// `trait_ref` would map `T:Trait`.
pub fn get_vtable(
    cx: &CodegenCx<'ll, 'tcx>,
    ty: Ty<'tcx>,
    trait_ref: Option<ty::PolyExistentialTraitRef<'tcx>>,
) -> &'ll Value {
    let tcx = cx.tcx;

    debug!("get_vtable(ty={:?}, trait_ref={:?})", ty, trait_ref);

    // Check the cache.
    if let Some(&val) = cx.vtables.borrow().get(&(ty, trait_ref)) {
        return val;
    }

    // Not in the cache. Build it.
    let nullptr = C_null(Type::i8p(cx));

    let (size, align) = cx.size_and_align_of(ty);
    let glue_size_align = [
        callee::get_fn(cx, monomorphize::resolve_drop_in_place(cx.tcx, ty)),
        C_usize(cx, size.bytes()),
        C_usize(cx, align.abi())
    ];

    if let Some(trait_ref) = trait_ref {

        fn get_supertraits(
            cx: &CodegenCx<'ll, 'tcx>,
            trait_ref_with_self: ty::PolyTraitRef<'tcx>)
            //-> impl Iterator<Item = ty::PolyTraitRef<'tcx>> + 'll
            -> Vec<ty::PolyTraitRef<'tcx>>
        {
            let tcx = cx.tcx;
            tcx.super_predicates_of(trait_ref_with_self.def_id())
                .predicates.iter()
                .map(|(p, _)| p.subst_supertrait(tcx, &trait_ref_with_self))
                .map(|p| {
                    // Unwrap ty::Predicate to ty::PolyTraitPredicate,
                    // extract ty::PolyTraitRef
                    if let ty::Predicate::Trait(poly_trait_predicate) = p {
                        poly_trait_predicate.to_poly_trait_ref()
                    } else {
                        bug!("expected trait, got {:?}", p)
                    }
                })
                .collect()
        }

        // Recurse through supertraits
        // TODO: Issue with cycles? Mentioned in traits::... comment
        // TODO: Avoid redundant vtables, traversals, and duplication in a
        //       single vtable
        fn recurse_through_supertraits<'ll, 'tcx, F>(
            cx: &CodegenCx<'ll, 'tcx>,
            trait_ref_with_self: ty::PolyTraitRef<'tcx>,
            closure: &mut F)
            where F: FnMut(&CodegenCx<'ll, 'tcx>, ty::PolyTraitRef<'tcx>, bool)
        {
            let supertraits = get_supertraits(cx, trait_ref_with_self);

            closure(cx, trait_ref_with_self, supertraits.is_empty());

            // TODO: Is this step necessary or is the order already deterministic?
            //       (including across compilation units)
            let mut supertraits = supertraits;
            supertraits.sort_by(|a, b| {
                let (a, b) = (a.skip_binder(), b.skip_binder());
                match a.def_id.cmp(&b.def_id) {
                    ord @ Ordering::Less | ord @ Ordering::Greater => { return ord; }
                    _ => ()
                }
                a.substs.cmp(&b.substs)
            });
            let supertraits = supertraits;
            for supertrait in supertraits {
                recurse_through_supertraits(cx, supertrait, closure);
            }
        }

        let trait_ref_with_self = trait_ref.with_self_ty(tcx, ty);
        let mut v = Vec::new();

        recurse_through_supertraits(cx, trait_ref_with_self,
            &mut |cx, trait_ref_with_self, is_leaf| {
            if is_leaf {
                debug!("get_vtable: Adding [glue, size, align]");
                v.extend(glue_size_align.iter());
            }
            debug!("get_vtable: Adding methods from {:?}", trait_ref_with_self);
            let starting_len = v.len();
            v.extend(
                own_vtable_methods(cx.tcx, trait_ref_with_self)
                .map(|opt| { opt.map_or(nullptr, |(def_id, substs)| {
                    callee::resolve_and_get_fn(cx, def_id, substs)
                })}));
            debug!("get_vtable: Added {:?} methods", v.len() - starting_len);
        });

        let vtable_const = C_struct(cx, &v, false);
        let align = cx.data_layout().pointer_align;
        let vtable = consts::addr_of(cx, vtable_const, align, Some("vtable"));

        // TODO: Fix this, I'm sure it's wrong now
        //debuginfo::create_vtable_metadata(cx, ty, vtable);

        cx.vtables.borrow_mut().insert((ty, Some(trait_ref)), vtable);
        vtable
    } else {
        let vtable_const = C_struct(cx, &glue_size_align, false);
        let align = cx.data_layout().pointer_align;
        let vtable = consts::addr_of(cx, vtable_const, align, Some("vtable"));
        debuginfo::create_vtable_metadata(cx, ty, vtable);
        cx.vtables.borrow_mut().insert((ty, trait_ref), vtable);
        vtable
    }
}
