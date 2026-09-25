import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal
open Set

/-! ## Auxiliary: norms of differences of iterated derivatives

The `C^{1,α}` norm is built from the *within* iterated derivatives
`iteratedFDerivWithin ℝ i g Ω`, while the hypotheses bound the Fréchet derivative
`fderiv ℝ g`.  On an open set the two agree, and the norm of a difference of
first iterated derivatives agrees with the norm of the difference of the Fréchet
derivatives (the two are identified by the linear isometry
`continuousMultilinearCurryFin1`).  The corresponding order-`0` statement uses
`ContinuousMultilinearMap.uncurry0`. -/

lemma norm_iteratedFDeriv_one_sub_eq_gen {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : X → ℂ) (x y : X) :
    ‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖ = ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
  have key : ∀ z : X, continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDeriv ℝ 1 u z)
      = fderiv ℝ u z := by
    intro z
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  have hx : iteratedFDeriv ℝ 1 u x
      = (continuousMultilinearCurryFin1 ℝ X ℂ).symm (fderiv ℝ u x) := by
    rw [← key x, LinearIsometryEquiv.symm_apply_apply]
  have hy : iteratedFDeriv ℝ 1 u y
      = (continuousMultilinearCurryFin1 ℝ X ℂ).symm (fderiv ℝ u y) := by
    rw [← key y, LinearIsometryEquiv.symm_apply_apply]
  rw [hx, hy, ← map_sub, LinearIsometryEquiv.norm_map]

lemma norm_iteratedFDerivWithin_zero_sub_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 u Ω x - iteratedFDerivWithin ℝ 0 u Ω y‖ = ‖u x - u y‖ := by
  have key : ∀ z : X, iteratedFDerivWithin ℝ 0 u Ω z
      = ContinuousMultilinearMap.uncurry0 ℝ X (u z) := by
    intro z
    ext m
    rw [iteratedFDerivWithin_zero_apply, ContinuousMultilinearMap.uncurry0_apply]
  have hsub : ContinuousMultilinearMap.uncurry0 ℝ X (u x)
        - ContinuousMultilinearMap.uncurry0 ℝ X (u y)
      = ContinuousMultilinearMap.uncurry0 ℝ X (u x - u y) := by
    ext m
    simp [ContinuousMultilinearMap.uncurry0_apply]
  rw [key x, key y, hsub, ContinuousMultilinearMap.uncurry0_norm]

lemma norm_iteratedFDerivWithin_one_sub_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : IsOpen Ω) (u : X → ℂ) {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ 1 u Ω x - iteratedFDerivWithin ℝ 1 u Ω y‖
      = ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := u) 1 hΩ hx,
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := u) 1 hΩ hy,
    norm_iteratedFDeriv_one_sub_eq_gen]

/-- Pointwise `C^{0,α}` estimate: `‖g x - g y‖ ≤ (2 M₀ + M₁) ‖x - y‖^α`. -/
lemma holderSeminorm_zero_pointwise {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hconv : Convex ℝ Ω) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {g : X → ℂ} (hg : ContDiff ℝ 1 g) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h0 : ∀ x ∈ Ω, ‖g x‖ ≤ M₀) (h1 : ∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ M₁)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ‖g x - g y‖ / ‖x - y‖ ^ α ≤ 2 * M₀ + M₁ := by
  have hdiff : ∀ z ∈ Ω, DifferentiableAt ℝ g z :=
    fun z _ => (hg.differentiable (by norm_num)).differentiableAt
  have hmvt : ‖g x - g y‖ ≤ M₁ * ‖x - y‖ := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff h1 hconv hy hx
    simpa only [norm_sub_rev] using this
  have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ha : 0 ≤ ‖g x - g y‖ := norm_nonneg _
  by_cases hd : ‖x - y‖ ≤ 1
  · have hdα : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
      have h2 : ‖x - y‖ ^ (1:ℝ) ≤ ‖x - y‖ ^ α :=
        Real.rpow_le_rpow_of_exponent_ge hdpos hd hα1.le
      rwa [Real.rpow_one] at h2
    have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
    rw [div_le_iff₀ hdαpos]
    calc ‖g x - g y‖ ≤ M₁ * ‖x - y‖ := hmvt
      _ ≤ M₁ * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hdα hM₁
      _ ≤ (2 * M₀ + M₁) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdαpos)
  · have h1d : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hd)
    have hdα1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow h1d hα0.le
    have h2 : ‖g x - g y‖ ≤ 2 * M₀ := by
      calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
        _ ≤ M₀ + M₀ := add_le_add (h0 x hx) (h0 y hy)
        _ = 2 * M₀ := by ring
    calc ‖g x - g y‖ / ‖x - y‖ ^ α ≤ ‖g x - g y‖ / 1 :=
          div_le_div_of_nonneg_left ha one_pos hdα1
      _ = ‖g x - g y‖ := by rw [div_one]
      _ ≤ 2 * M₀ := h2
      _ ≤ 2 * M₀ + M₁ := by linarith

/-- Pointwise `C^{1,α}` estimate: `‖Dg x - Dg y‖ ≤ (2 M₁ + M₂) ‖x - y‖^α`. -/
lemma holderSeminorm_one_pointwise {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {g : X → ℂ} {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h1 : ∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ M₁)
    (h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M₂ * ‖x - y‖)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ‖fderiv ℝ g x - fderiv ℝ g y‖ / ‖x - y‖ ^ α ≤ 2 * M₁ + M₂ := by
  have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ha : 0 ≤ ‖fderiv ℝ g x - fderiv ℝ g y‖ := norm_nonneg _
  by_cases hd : ‖x - y‖ ≤ 1
  · have hdα : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
      have h2' : ‖x - y‖ ^ (1:ℝ) ≤ ‖x - y‖ ^ α :=
        Real.rpow_le_rpow_of_exponent_ge hdpos hd hα1.le
      rwa [Real.rpow_one] at h2'
    have hdαpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
    rw [div_le_iff₀ hdαpos]
    calc ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M₂ * ‖x - y‖ := h2 x hx y hy
      _ ≤ M₂ * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hdα hM₂
      _ ≤ (2 * M₁ + M₂) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdαpos)
  · have h1d : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hd)
    have hdα1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow h1d hα0.le
    have h2' : ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ 2 * M₁ := by
      calc ‖fderiv ℝ g x - fderiv ℝ g y‖
            ≤ ‖fderiv ℝ g x‖ + ‖fderiv ℝ g y‖ := norm_sub_le _ _
        _ ≤ M₁ + M₁ := add_le_add (h1 x hx) (h1 y hy)
        _ = 2 * M₁ := by ring
    calc ‖fderiv ℝ g x - fderiv ℝ g y‖ / ‖x - y‖ ^ α
          ≤ ‖fderiv ℝ g x - fderiv ℝ g y‖ / 1 :=
            div_le_div_of_nonneg_left ha one_pos hdα1
      _ = ‖fderiv ℝ g x - fderiv ℝ g y‖ := by rw [div_one]
      _ ≤ 2 * M₁ := h2'
      _ ≤ 2 * M₁ + M₂ := by linarith

/-- **Derivative bounds give a `C^{1,α}` bound.**  On a convex open set `Ω`, a `C¹` function
`g` whose value, first derivative and derivative's modulus of continuity are bounded by
`M₀, M₁, M₂` on `Ω` has `C^{1,α}` norm at most `3 M₀ + 4 M₁ + M₂` (for `0 < α < 1`). -/
theorem holderNorm_one_le_of_deriv_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {g : X → ℂ} (hg : ContDiff ℝ 1 g) {M₀ M₁ M₂ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h0 : ∀ x ∈ Ω, ‖g x‖ ≤ M₀) (h1 : ∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ M₁)
    (h2 : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M₂ * ‖x - y‖) :
    Work.CR.Flat.holderNorm 1 α g Ω ≤ ENNReal.ofReal (3 * M₀ + 4 * M₁ + M₂) := by
  have hiter0 : Work.CR.Flat.iterDerivNorm 0 g Ω ≤ ENNReal.ofReal M₀ := by
    refine iSup₂_le fun x hx => ?_
    rw [norm_iteratedFDerivWithin_zero]
    exact ENNReal.ofReal_le_ofReal (h0 x hx)
  have hiter1 : Work.CR.Flat.iterDerivNorm 1 g Ω ≤ ENNReal.ofReal M₁ := by
    refine iSup₂_le fun x hx => ?_
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := g) 1 hΩ hx,
      norm_iteratedFDeriv_one]
    exact ENNReal.ofReal_le_ofReal (h1 x hx)
  have hsem0 : Work.CR.Flat.holderSeminorm 0 α g Ω ≤ ENNReal.ofReal (2 * M₀ + M₁) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_zero_sub_eq g Ω x y]
    exact ENNReal.ofReal_le_ofReal
      (holderSeminorm_zero_pointwise hconv hα0 hα1 hg hM₀ hM₁ h0 h1 hx hy hxy)
  have hsem1 : Work.CR.Flat.holderSeminorm 1 α g Ω ≤ ENNReal.ofReal (2 * M₁ + M₂) := by
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_one_sub_eq hΩ g hx hy]
    exact ENNReal.ofReal_le_ofReal
      (holderSeminorm_one_pointwise hα0 hα1 hM₁ hM₂ h1 h2 hx hy hxy)
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

end Work.NN.Core.Lev
