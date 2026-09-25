import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Final

/-! ## Submultiplicativity of the `C^{0,α}`-norm

The `C^{0,α}`-norm of a pointwise product `x ↦ f x * g x` is controlled by the product
of the `C^{0,α}`-norms of the factors.  The pointwise ingredients are the elementary
estimates
`‖f x * g x‖ ≤ ‖f x‖ * ‖g x‖` for the sup part and
`‖f x * g x - f y * g y‖ ≤ ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖`
for the Hölder part (writing `f x g x - f y g y = f x (g x - g y) + (f x - f y) g y`). -/

/-- At order `0` the "derivative" is the function itself, so the norm of the difference of the
two `0`-th iterated derivatives is the norm of the difference of the values. -/
private lemma norm_iteratedFDerivWithin_zero_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (f : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [sub_apply, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y)
      (fun _ : Fin 0 => (0 : X))
    simpa only [sub_apply, iteratedFDerivWithin_zero_apply,
      Finset.univ_eq_empty, Finset.prod_empty, mul_one] using h

/-- The sup-part of the `C^{0,α}`-norm is submultiplicative. -/
private lemma iterDerivNorm_zero_mul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.iterDerivNorm 0 (fun x => f x * g x) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω := by
  rw [Work.CR.Flat.iterDerivNorm_zero f Ω, Work.CR.Flat.iterDerivNorm_zero g Ω,
      Work.CR.Flat.iterDerivNorm_zero (fun x => f x * g x) Ω]
  refine iSup₂_le fun x hx => ?_
  rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul' (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)

/-- The Hölder-part of the `C^{0,α}`-norm of a product is bounded by
`‖f‖_∞ · [g]_α + ‖g‖_∞ · [f]_α`. -/
private lemma holderSeminorm_zero_mul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (α : ℝ) (f g : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderSeminorm 0 α (fun x => f x * g x) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω
        + Work.CR.Flat.iterDerivNorm 0 g Ω * Work.CR.Flat.holderSeminorm 0 α f Ω := by
  rw [Work.CR.Flat.iterDerivNorm_zero f Ω, Work.CR.Flat.iterDerivNorm_zero g Ω]
  conv_lhs => rw [Work.CR.Flat.holderSeminorm]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [norm_iteratedFDerivWithin_zero_sub]
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hDpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hpos α
  have hN : ‖f x * g x - f y * g y‖ ≤ ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ := by
    have heq : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, mul_comm ‖f x - f y‖ ‖g y‖]
  calc
    ENNReal.ofReal (‖f x * g x - f y * g y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (‖f x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
            + ‖g y‖ * (‖f x - f y‖ / ‖x - y‖ ^ α)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (div_le_div_of_nonneg_right hN hDpos.le).trans_eq ?_
          rw [add_div, mul_div_assoc, mul_div_assoc]
    _ = ENNReal.ofReal ‖f x‖ * ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
          + ENNReal.ofReal ‖g y‖ * ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) := by
          rw [ENNReal.ofReal_add
                (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hDpos.le))
                (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hDpos.le)),
              ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖) * Work.CR.Flat.holderSeminorm 0 α g Ω
          + (⨆ x ∈ Ω, ENNReal.ofReal ‖g x‖) * Work.CR.Flat.holderSeminorm 0 α f Ω := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul' (le_iSup₂_of_le x hx le_rfl) ?_
            rw [← norm_iteratedFDerivWithin_zero_sub g Ω x y]
            exact Work.CR.Flat.le_holderSeminorm 0 α g Ω hx hy hxy
          · refine mul_le_mul' (le_iSup₂_of_le y hy le_rfl) ?_
            rw [← norm_iteratedFDerivWithin_zero_sub f Ω x y]
            exact Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy

/-- **Submultiplicativity of the `C^{0,α}`-norm.** -/
theorem holderNorm_zero_mul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} (f g : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α (fun x => f x * g x) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω * Work.CR.Flat.holderNorm 0 α g Ω := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  rw [Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one]
  refine le_trans (add_le_add (iterDerivNorm_zero_mul_le f g Ω)
    (holderSeminorm_zero_mul_le α f g Ω)) ?_
  calc Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω
        + (Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω
           + Work.CR.Flat.iterDerivNorm 0 g Ω * Work.CR.Flat.holderSeminorm 0 α f Ω)
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω
        + (Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω
           + Work.CR.Flat.iterDerivNorm 0 g Ω * Work.CR.Flat.holderSeminorm 0 α f Ω)
        + Work.CR.Flat.holderSeminorm 0 α f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω :=
          le_self_add
    _ = (Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.holderSeminorm 0 α f Ω)
          * (Work.CR.Flat.iterDerivNorm 0 g Ω + Work.CR.Flat.holderSeminorm 0 α g Ω) := by ring

end Work.NN.Final
