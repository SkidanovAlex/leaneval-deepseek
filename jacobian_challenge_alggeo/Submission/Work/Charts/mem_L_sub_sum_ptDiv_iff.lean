/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subtracting a sum of point divisors from a Riemann–Roch space

Let `x : Fin n → CurveFPt C F` be a family of `F`-points of a curve `C` over `K` whose places
`ptPlace (x m)` on `C_F` are pairwise distinct, and let `A` be a divisor on `C_F` whose support
avoids all of them (`A (ptPlace (x m)) = 0`).  Then for a nonzero rational function `h` that
already lies in `L A`, membership in `L (A - ∑ m, ptDiv (x m))` is exactly the requirement that
`h` vanish to order at least one at each of the points `ptPlace (x m)`.

This is the "specialisation" form of `mem_L_sub_iff_ord` for the concrete divisor
`∑ m, ptDiv (x m)`.
-/
import Mathlib
import Submission.Work.Charts.Core
import Submission.Work.SpecLin.Points.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

/-- The value at `ptPlace (x m)` of the sum of the point divisors `∑ m', ptDiv (x m')` is `1`,
provided the places `ptPlace (x m')` are pairwise distinct. -/
lemma sum_ptDiv_apply_self {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {n : ℕ} (x : Fin n → Work.SpecLin.CurveFPt C F)
    (hinj : Function.Injective fun m => Work.SpecLin.ptPlace (x m)) (m : Fin n) :
    (∑ m', Work.SpecLin.ptDiv (x m')) (Work.SpecLin.ptPlace (x m)) = 1 := by
  rw [Finsupp.finsetSum_apply,
    Finset.sum_eq_single m (fun b _ hbm => by
      rw [Work.SpecLin.ptDiv_apply, ite_eq_right]
      exact fun hc => hbm (hinj hc))
    (fun hm => absurd (Finset.mem_univ m) hm)]
  rw [Work.SpecLin.ptDiv_apply, ite_eq_left rfl]

/-- A sum of point divisors is effective. -/
lemma sum_ptDiv_nonneg {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {n : ℕ} (x : Fin n → Work.SpecLin.CurveFPt C F)
    (Q : (C.baseChange F).Place) : 0 ≤ (∑ m', Work.SpecLin.ptDiv (x m')) Q := by
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro m _
  rw [Work.SpecLin.ptDiv_apply]
  split <;> norm_num

/-- If the sum `∑ m, ptDiv (x m)` is positive at a place `Q`, then `Q` is one of the places
`ptPlace (x m)`.  (This does not need injectivity of the family.) -/
lemma exists_of_sum_ptDiv_pos {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {n : ℕ} (x : Fin n → Work.SpecLin.CurveFPt C F)
    {Q : (C.baseChange F).Place} (h : 0 < (∑ m', Work.SpecLin.ptDiv (x m')) Q) :
    ∃ m, Work.SpecLin.ptPlace (x m) = Q := by
  by_contra hc
  have hc' : ∀ m, Work.SpecLin.ptPlace (x m) ≠ Q := fun m hm => hc ⟨m, hm⟩
  have hz : (∑ m', Work.SpecLin.ptDiv (x m')) Q = 0 := by
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro m _
    rw [Work.SpecLin.ptDiv_apply, ite_eq_right (hc' m)]
  linarith

theorem mem_L_sub_sum_ptDiv_iff {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C] {F : Type u} [Field F]
    [Algebra K F] (A : Work.GCBasics.Dv C F) {n : ℕ} (x : Fin n → Work.SpecLin.CurveFPt C F)
    (hinj : Function.Injective fun m => Work.SpecLin.ptPlace (x m))
    (hdisj : ∀ m, A (Work.SpecLin.ptPlace (x m)) = 0)
    {h : (C.baseChange F).functionField} (hh : h ≠ 0)
    (hmem : h ∈ Work.CurveBasics.Curve.L (C.baseChange F) A) :
    h ∈ Work.CurveBasics.Curve.L (C.baseChange F) (A - ∑ m, Work.SpecLin.ptDiv (x m)) ↔
      ∀ m, 1 ≤ Work.CurveBasics.Curve.ordAt (C.baseChange F) h
        (Work.SpecLin.ptPlace (x m)) := by
  have hL : h ∈ Work.CurveBasics.Curve.L (C.baseChange F)
        (A - ∑ m, Work.SpecLin.ptDiv (x m)) ↔
      (Work.CurveBasics.Curve.div (C.baseChange F) h +
        (A - ∑ m, Work.SpecLin.ptDiv (x m))).IsEffective := by
    rw [Work.CurveBasics.Curve.mem_L_iff]
    constructor
    · rintro (h0 | hP) <;> [exact absurd h0 hh; exact hP]
    · exact Or.inr
  have hMem_ord : ∀ Q, 0 ≤ (C.baseChange F).ordAt h Q + A Q := by
    have hA : (Work.CurveBasics.Curve.div (C.baseChange F) h + A).IsEffective := by
      rw [Work.CurveBasics.Curve.mem_L_iff] at hmem
      rcases hmem with h0 | hP
      · exact absurd h0 hh
      · exact hP
    intro Q
    have := hA Q
    simp only [Finsupp.add_apply, Work.CurveBasics.Curve.div_apply] at this
    exact this
  rw [hL]
  simp only [Work.CurveBasics.Curve.Div.isEffective_iff, Finsupp.add_apply, Finsupp.sub_apply,
    Work.CurveBasics.Curve.div_apply]
  constructor
  · intro hLHS m
    have h' := hLHS (Work.SpecLin.ptPlace (x m))
    rw [sum_ptDiv_apply_self x hinj m, hdisj m] at h'
    linarith
  · intro hRHS Q
    by_cases hpos : 0 < (∑ m', Work.SpecLin.ptDiv (x m')) Q
    · obtain ⟨m, hm⟩ := exists_of_sum_ptDiv_pos x hpos
      have h1 : (∑ m', Work.SpecLin.ptDiv (x m')) Q = 1 := by
        rw [← hm]; exact sum_ptDiv_apply_self x hinj m
      have hA : A Q = 0 := by rw [← hm]; exact hdisj m
      have hord : 1 ≤ (C.baseChange F).ordAt h Q := by rw [← hm]; exact hRHS m
      rw [h1, hA]; linarith
    · have h0 : (∑ m', Work.SpecLin.ptDiv (x m')) Q = 0 :=
        le_antisymm (le_of_not_gt hpos) (sum_ptDiv_nonneg x Q)
      rw [h0]
      have := hMem_ord Q
      linarith

end Work.Charts
