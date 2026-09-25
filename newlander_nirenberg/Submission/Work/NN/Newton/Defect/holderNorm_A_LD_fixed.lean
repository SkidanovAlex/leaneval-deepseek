import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.opNorm_A_bounds
import Submission.Work.NN.Newton.Defect.vecHolder_deriv_field

namespace Work.NN.Newton.Defect

open scoped ENNReal
open Set

/-!
# `C^{0,α}` bound for `z ↦ λ_l(A z ((DA_z X) Y))` with `X`, `Y` fixed

Fix `X`, `Y : ℂⁿ` with `‖X‖ ≤ 1`, `‖Y‖ ≤ 1` and a coordinate `l`.  For a `C^{1,α}`-small
perturbation `A` (`CVBound A α a P`, `P` the polydisc of radius `r`) we bound the
`C^{0,α}(P)`-norm of

  `f z = λ_l (A z ((DA_z X) Y))`

by `4 a²`.

The function is a *product* of the perturbation `A` with its own derivative `DA`, so each
factor contributes one power of `a`:

* `‖A z‖ ≤ a` and `‖A x - A y‖ ≤ a ‖x - y‖^α` on `P` (`opNorm_A_bounds`);
* the field `z ↦ (DA_z) X` is `C^{0,α}` of norm ≤ `a` (`vecHolder_deriv_field`), so
  `v z = (DA_z X) Y` satisfies `‖v z‖ ≤ a` and `‖v x - v y‖ ≤ a ‖x - y‖^α`
  (evaluation at the fixed `Y`, `‖Y‖ ≤ 1`).

Hence `‖f z‖ ≤ a · a = a²`, and, splitting
`A x (v x) - A y (v y) = A x (v x - v y) + (A x - A y) (v y)`,
also `‖f x - f y‖ ≤ a·a‖x-y‖^α + a‖x-y‖^α·a = 2a²‖x-y‖^α`.  Since
`holderNorm 0 α f P = iterDerivNorm 0 f P + holderSeminorm 0 α f P`, the conclusion follows
from `ofReal (a²) + ofReal (2a²) = ofReal (3a²) ≤ ofReal (4a²)`.
-/

theorem holderNorm_A_LD_fixed {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r))
    {X Y : Work.NN.Core.Cn n} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.lamC l (A z ((fderiv ℝ A z X) Y)))
        (Work.NN.Newton.polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
  set f : Work.NN.Core.Cn n → ℂ := fun z => Work.NN.Newton.lamC l (A z ((fderiv ℝ A z X) Y))
    with hf
  set P : Set (Work.NN.Core.Cn n) := Work.NN.Newton.polydiscR n r with hP
  obtain ⟨hAop₀, hAlip₀⟩ := opNorm_A_bounds A hα0 ha0 hA
  have hAop : ∀ z ∈ P, ‖A z‖ ≤ a := hAop₀
  have hAlip : ∀ x ∈ P, ∀ y ∈ P, ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α := hAlip₀
  have hv : Work.NN.Final.VecHolder (fun z => (fderiv ℝ A z) X) α a P :=
    vecHolder_deriv_field A hα0 ha0 hAc hA hX
  -- `v z = (DA_z X) Y` is bounded by `a`, and is `α`-Hölder with constant `a`
  have hv1 : ∀ z ∈ P, ‖(fderiv ℝ A z X) Y‖ ≤ a := by
    intro z hz
    have h1 : ‖(fderiv ℝ A z) X‖ ≤ a := hv.1 z hz
    calc ‖(fderiv ℝ A z X) Y‖ ≤ ‖(fderiv ℝ A z) X‖ * ‖Y‖ := ContinuousLinearMap.le_opNorm _ Y
      _ ≤ a * 1 := mul_le_mul h1 hY (norm_nonneg Y) ha0
      _ = a := by ring
  have hv2 : ∀ x ∈ P, ∀ y ∈ P,
      ‖(fderiv ℝ A x X) Y - (fderiv ℝ A y X) Y‖ ≤ a * ‖x - y‖ ^ α := by
    intro x hx y hy
    have h1 : ‖(fderiv ℝ A x) X - (fderiv ℝ A y) X‖ ≤ a * ‖x - y‖ ^ α := hv.2 x hx y hy
    have h2 : (fderiv ℝ A x X) Y - (fderiv ℝ A y X) Y
        = ((fderiv ℝ A x) X - (fderiv ℝ A y) X) Y := by
      rw [sub_apply]
    rw [h2]
    calc ‖((fderiv ℝ A x) X - (fderiv ℝ A y) X) Y‖
        ≤ ‖(fderiv ℝ A x) X - (fderiv ℝ A y) X‖ * ‖Y‖ := ContinuousLinearMap.le_opNorm _ Y
      _ ≤ (a * ‖x - y‖ ^ α) * 1 := mul_le_mul h1 hY (norm_nonneg Y)
          (mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α))
      _ = a * ‖x - y‖ ^ α := by ring
  -- sup-norm bound: `‖f z‖ ≤ a * a = a²`
  have hsup : ∀ z ∈ P, ‖f z‖ ≤ a ^ 2 := by
    intro z hz
    have h1 : ‖A z ((fderiv ℝ A z X) Y)‖ ≤ ‖A z‖ * ‖(fderiv ℝ A z X) Y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    calc ‖f z‖ = ‖Work.NN.Newton.lamC l (A z ((fderiv ℝ A z X) Y))‖ := rfl
      _ ≤ ‖A z ((fderiv ℝ A z X) Y)‖ := by
          simpa only [Work.NN.Newton.lamC_apply] using
            norm_le_pi_norm (A z ((fderiv ℝ A z X) Y)) l
      _ ≤ ‖A z‖ * ‖(fderiv ℝ A z X) Y‖ := h1
      _ ≤ a * a := mul_le_mul (hAop z hz) (hv1 z hz) (norm_nonneg _) ha0
      _ = a ^ 2 := by ring
  -- Hölder bound: `‖f x - f y‖ ≤ 2 a² ‖x - y‖^α`
  have hlip : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y‖ ≤ (2 * a ^ 2) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hdecomp : A x ((fderiv ℝ A x X) Y) - A y ((fderiv ℝ A y X) Y)
        = A x ((fderiv ℝ A x X) Y - (fderiv ℝ A y X) Y)
          + (A x - A y) ((fderiv ℝ A y X) Y) := by
      rw [map_sub, sub_apply]
      abel
    have hfl : f x - f y = Work.NN.Newton.lamC l
        (A x ((fderiv ℝ A x X) Y) - A y ((fderiv ℝ A y X) Y)) := by
      rw [hf]
      exact (map_sub (Work.NN.Newton.lamC l) _ _).symm
    calc ‖f x - f y‖
        = ‖Work.NN.Newton.lamC l
            (A x ((fderiv ℝ A x X) Y) - A y ((fderiv ℝ A y X) Y))‖ := by rw [hfl]
      _ ≤ ‖A x ((fderiv ℝ A x X) Y) - A y ((fderiv ℝ A y X) Y)‖ := by
          simpa only [Work.NN.Newton.lamC_apply] using
            norm_le_pi_norm (A x ((fderiv ℝ A x X) Y) - A y ((fderiv ℝ A y X) Y)) l
      _ = ‖A x ((fderiv ℝ A x X) Y - (fderiv ℝ A y X) Y)
            + (A x - A y) ((fderiv ℝ A y X) Y)‖ := by rw [hdecomp]
      _ ≤ ‖A x ((fderiv ℝ A x X) Y - (fderiv ℝ A y X) Y)‖
            + ‖(A x - A y) ((fderiv ℝ A y X) Y)‖ := norm_add_le _ _
      _ ≤ ‖A x‖ * ‖(fderiv ℝ A x X) Y - (fderiv ℝ A y X) Y‖
            + ‖A x - A y‖ * ‖(fderiv ℝ A y X) Y‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ a * (a * ‖x - y‖ ^ α) + (a * ‖x - y‖ ^ α) * a := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hAop x hx) (hv2 x hx y hy) (norm_nonneg _) ha0
          · exact mul_le_mul (hAlip x hx y hy) (hv1 y hy) (norm_nonneg _)
              (mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α))
      _ = (2 * a ^ 2) * ‖x - y‖ ^ α := by ring
  -- assemble the two pieces of `holderNorm 0`
  have hiter : Work.CR.Flat.iterDerivNorm 0 f P ≤ ENNReal.ofReal (a ^ 2) := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    exact iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal (hsup z hz)
  have hsem : Work.CR.Flat.holderSeminorm 0 α f P ≤ ENNReal.ofReal (2 * a ^ 2) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [show ‖iteratedFDerivWithin ℝ 0 f P x - iteratedFDerivWithin ℝ 0 f P y‖ = ‖f x - f y‖
        from by
      simpa [dist_eq_norm] using dist_iteratedFDerivWithin_zero (𝕜 := ℝ) f P x f P y]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [div_le_iff₀ hpos]
    exact hlip x hx y hy
  have hsum : Work.CR.Flat.holderNorm 0 α f P
      = Work.CR.Flat.iterDerivNorm 0 f P + Work.CR.Flat.holderSeminorm 0 α f P := by
    simp [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  rw [hsum]
  refine (add_le_add hiter hsem).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg a]

end Work.NN.Newton.Defect
