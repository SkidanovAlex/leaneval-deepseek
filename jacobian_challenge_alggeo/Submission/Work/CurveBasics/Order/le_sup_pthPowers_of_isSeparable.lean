/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `L` is generated over `K` by its `p`-th powers when `L / K` is separable

Let `k` be a perfect field of exponential characteristic `p`, `F / k` a field extension and
`K ≤ L` intermediate fields.  If every element of `L` is separable over `K`, then `L` lies in the
compositum of `K` with the `p`-th powers of `L`:

`L ≤ K ⊔ L^p`.

Since `K ≤ L` and `L ^ p ≤ L`, that inclusion is in fact an equality `L = K ⊔ L ^ p`.

The point is that a separable element `x` satisfies `K(x) = K(x ^ p)`
(`IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable`), so `x ∈ K ⊔ k⟮x ^ p⟯`,
and `x ^ p ∈ L ^ p`.
-/
import Mathlib
import Submission.Work.CurveBasics.Order.PthPowers

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.CurveBasics.Order

theorem le_sup_pthPowers_of_isSeparable {k F : Type u} [Field k] [PerfectField k] [Field F] [Algebra k F]
    {p : ℕ} [ExpChar k p] [ExpChar F p] {K L : IntermediateField k F} (hKL : K ≤ L)
    (hsep : ∀ x ∈ L, IsSeparable ↥K x) :
    L ≤ K ⊔ Work.CurveBasics.Order.pthPowers p L := by
  -- The reverse inclusion is immediate from `K ≤ L` and `L ^ p ≤ L`.
  have hML : K ⊔ Work.CurveBasics.Order.pthPowers p L ≤ L :=
    sup_le hKL (Work.CurveBasics.Order.pthPowers_le p L)
  have hLM : L ≤ K ⊔ Work.CurveBasics.Order.pthPowers p L := by
    intro x hx
    -- `x` is separable over `K`, hence `K⟮x⟯ = K⟮x ^ p⟯`.
    have ha : IsSeparable ↥K x := hsep x hx
    have hadj : IntermediateField.adjoin (↥K) ({x} : Set F) =
        IntermediateField.adjoin (↥K) ({x ^ p} : Set F) :=
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable (↥K) F ha p
    have hx1 : x ∈ IntermediateField.adjoin (↥K) ({x ^ p} : Set F) := by
      rw [← hadj]
      exact IntermediateField.mem_adjoin_simple_self ↥K x
    -- View `K⟮x ^ p⟯` as a `k`-intermediate field: it is `K ⊔ k⟮x ^ p⟯`.
    have hx2 : x ∈ IntermediateField.restrictScalars k
        (IntermediateField.adjoin (↥K) ({x ^ p} : Set F)) := by
      rw [IntermediateField.mem_restrictScalars]
      exact hx1
    rw [IntermediateField.restrictScalars_adjoin_eq_sup] at hx2
    -- `x ^ p ∈ L ^ p`, so `k⟮x ^ p⟯ ≤ L ^ p` and hence `x ∈ K ⊔ L ^ p`.
    have hle : IntermediateField.adjoin k ({x ^ p} : Set F) ≤
        Work.CurveBasics.Order.pthPowers p L :=
      IntermediateField.adjoin_le_iff.mpr
        (Set.singleton_subset_iff.mpr (Work.CurveBasics.Order.pow_mem_pthPowers hx))
    exact (sup_le le_sup_left (hle.trans le_sup_right)) hx2
  exact (le_antisymm hML hLM).ge

end Work.CurveBasics.Order
