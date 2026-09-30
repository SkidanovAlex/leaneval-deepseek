/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# (K2) Section equations and the points of the special fibre

This file collects the *elementary commutative-algebra* steps of the reading-off step (K2) of
`Work.SpecLin.Core.coreDivCore`: given the chart ring `B = Γ(C,W) ⊗_K R`, the section prime
`I_m = sectionPrime R W φ_m` of the `m`-th section, the fibre prime `P = m_R·B`, and a maximal
ideal `N` of `B` with `P ≤ N`:

* `mem_iff_eq_sup_of_span_eq`: if `f` generates `I_m` and `N ⊇ P` is maximal, then `f ∈ N` if and
  only if `N = I_m ⊔ P` — i.e. the section passes through the point of the special fibre
  corresponding to `N` exactly when `N` is the specialisation of the section's own ideal.

Together with `Work.SpecLin.Core.sectionPrime_sup_fibrePrime_eq_ker`
(`ker ev ⊔ m_R·B = ker (residue R ∘ ev)`, hence `B ⧸ (I_m ⊔ P) ≅ κ`) and the order dictionary
`Work.SpecLin.Core.ord_germ_eq_iff_mem_pow`, this computes the order of the reduction of `f_m` at
the point of `C_κ` attached to `N`: it is `1` when `N = I_m ⊔ P`, and `0` otherwise.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

namespace Work.SpecLin.Core

/-- **The section equation vanishes at a point of the special fibre exactly when the point is the
specialisation of the section.**  If `I = (f)` and `I ⊔ P` is maximal, and `N ⊇ P` is a maximal
ideal, then `f ∈ N ↔ N = I ⊔ P`. -/
theorem mem_iff_eq_sup_of_span_eq {B : Type u} [CommRing B] (I P N : Ideal B)
    (hN : N.IsMaximal) (hPN : P ≤ N) (hIP : (I ⊔ P).IsMaximal) (f : B)
    (hf : I = Ideal.span {f}) :
    f ∈ N ↔ N = I ⊔ P := by
  constructor
  · intro hfN
    have h1 : I ≤ N := by
      rw [hf]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfN)
    have h2 : I ⊔ P ≤ N := sup_le h1 hPN
    exact (hIP.eq_of_le hN.ne_top h2).symm
  · intro h
    rw [h, hf]
    exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton f))

end Work.SpecLin.Core
