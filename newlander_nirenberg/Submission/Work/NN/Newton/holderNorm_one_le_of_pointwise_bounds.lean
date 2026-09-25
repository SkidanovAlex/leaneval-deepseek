import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds

/-!
# `C^{1,α}` bound from pointwise bounds

This is the pointwise version of
`Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds`: instead of asking for
`ContDiff ℝ 1 g` on the whole space and a Lipschitz bound `M₂ ‖x - y‖` on the
derivative, we only assume `g` is differentiable at the points of the (open,
convex) set `Ω`, and that the derivative satisfies a Hölder bound
`‖fderiv g x - fderiv g y‖ ≤ M₂ ‖x - y‖^α` there.  The conclusion is the same
quantitative bound `3 M₀ + 4 M₁ + M₂` on `holderNorm 1 α g Ω`.
-/

namespace Work.NN.Newton

open scoped NNReal ENNReal
open Set

theorem holderNorm_one_le_of_pointwise_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {g : X → ℂ} {M₀ M₁ M₂ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ g x)
    (h0 : ∀ x ∈ Ω, ‖g x‖ ≤ M₀) (h1 : ∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ M₁)
    (h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M₂ * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 1 α g Ω ≤ ENNReal.ofReal (3 * M₀ + 4 * M₁ + M₂) := by
  -- Order `0`: bound on `‖g‖`.
  have hiter0 : Work.CR.Flat.iterDerivNorm 0 g Ω ≤ ENNReal.ofReal M₀ := by
    refine iSup₂_le fun x hx => ?_
    rw [norm_iteratedFDerivWithin_zero]
    exact ENNReal.ofReal_le_ofReal (h0 x hx)
  -- Order `1`: bound on `‖Dg‖`.
  have hiter1 : Work.CR.Flat.iterDerivNorm 1 g Ω ≤ ENNReal.ofReal M₁ := by
    refine iSup₂_le fun x hx => ?_
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := g) 1 hΩ hx,
      norm_iteratedFDeriv_one]
    exact ENNReal.ofReal_le_ofReal (h1 x hx)
  -- Order `0` Hölder seminorm: mean value theorem on the convex set plus the
  -- elementary comparison of `‖x - y‖` and `‖x - y‖ ^ α`.
  have hsem0 : Work.CR.Flat.holderSeminorm 0 α g Ω ≤ ENNReal.ofReal (2 * M₀ + M₁) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.Lev.norm_iteratedFDerivWithin_zero_sub_eq g Ω x y]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmvt : ‖g x - g y‖ ≤ M₁ * ‖x - y‖ := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hdiff h1 hconv hy hx
      simpa only [norm_sub_rev] using this
    have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have ha : 0 ≤ ‖g x - g y‖ := norm_nonneg _
    by_cases hd : ‖x - y‖ ≤ 1
    · have hdα : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
        have h2' : ‖x - y‖ ^ (1 : ℝ) ≤ ‖x - y‖ ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos hd hα1.le
        rwa [Real.rpow_one] at h2'
      have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
      rw [div_le_iff₀ hdαpos]
      calc ‖g x - g y‖ ≤ M₁ * ‖x - y‖ := hmvt
        _ ≤ M₁ * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hdα hM₁
        _ ≤ (2 * M₀ + M₁) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdαpos)
    · have h1d : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hd)
      have hdα1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow h1d hα0.le
      have h2' : ‖g x - g y‖ ≤ 2 * M₀ := by
        calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
          _ ≤ M₀ + M₀ := add_le_add (h0 x hx) (h0 y hy)
          _ = 2 * M₀ := by ring
      calc ‖g x - g y‖ / ‖x - y‖ ^ α ≤ ‖g x - g y‖ / 1 :=
            div_le_div_of_nonneg_left ha one_pos hdα1
        _ = ‖g x - g y‖ := by rw [div_one]
        _ ≤ 2 * M₀ := h2'
        _ ≤ 2 * M₀ + M₁ := by linarith
  -- Order `1` Hölder seminorm: the hypothesis `h2` divided by `‖x - y‖ ^ α`.
  have hsem1 : Work.CR.Flat.holderSeminorm 1 α g Ω ≤ ENNReal.ofReal (2 * M₁ + M₂) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.Lev.norm_iteratedFDerivWithin_one_sub_eq hΩ g hx hy]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
    rw [div_le_iff₀ hdαpos]
    calc ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M₂ * ‖x - y‖ ^ α := h2 x hx y hy
      _ ≤ (2 * M₁ + M₂) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdαpos)
  -- Assemble the four pieces.
  have hsum : Work.CR.Flat.holderNorm 1 α g Ω
      = (Work.CR.Flat.iterDerivNorm 0 g Ω + Work.CR.Flat.holderSeminorm 0 α g Ω)
        + (Work.CR.Flat.iterDerivNorm 1 g Ω + Work.CR.Flat.holderSeminorm 1 α g Ω) := by
    simp [Work.CR.Flat.holderNorm, Finset.sum_range_succ]
  rw [hsum]
  refine le_trans (add_le_add (add_le_add hiter0 hsem0) (add_le_add hiter1 hsem1)) ?_
  have hA : ENNReal.ofReal M₀ + ENNReal.ofReal (2 * M₀ + M₁)
      = ENNReal.ofReal (M₀ + (2 * M₀ + M₁)) :=
    (ENNReal.ofReal_add hM₀ (by linarith)).symm
  have hB : ENNReal.ofReal M₁ + ENNReal.ofReal (2 * M₁ + M₂)
      = ENNReal.ofReal (M₁ + (2 * M₁ + M₂)) :=
    (ENNReal.ofReal_add hM₁ (by linarith)).symm
  have hC : ENNReal.ofReal (M₀ + (2 * M₀ + M₁)) + ENNReal.ofReal (M₁ + (2 * M₁ + M₂))
      = ENNReal.ofReal ((M₀ + (2 * M₀ + M₁)) + (M₁ + (2 * M₁ + M₂))) :=
    (ENNReal.ofReal_add (by linarith) (by linarith)).symm
  have hchain : ENNReal.ofReal M₀ + ENNReal.ofReal (2 * M₀ + M₁)
        + (ENNReal.ofReal M₁ + ENNReal.ofReal (2 * M₁ + M₂))
      = ENNReal.ofReal (3 * M₀ + 4 * M₁ + M₂) := by
    rw [hA, hB, hC]
    congr 1
    ring
  exact le_of_eq hchain

end Work.NN.Newton
