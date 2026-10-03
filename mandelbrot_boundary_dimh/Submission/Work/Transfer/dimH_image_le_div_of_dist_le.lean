import Mathlib

/-!
# A Hölder relation between two maps `X → ℂ` and Hausdorff dimension

If `F, G : X → ℂ` satisfy `‖F x - F y‖ ≤ C * ‖G x - G y‖ ^ a` on a set `S ⊆ X` (a "one-sided"
Hölder relation with exponent `a > 0`), then the image of `S` under `F` has Hausdorff dimension
at most `dimH (G '' S) / a`.

The proof observes that the correspondence `G x ↦ F x` is well defined on the set `G '' S`
(points with the same `G`-image have the same `F`-image, because `‖F x - F y‖ ≤ C * 0 ^ a = 0`),
and that the induced map `φ : ℂ → ℂ` is Hölder continuous with exponent `a` and constant `C` on
`G '' S`.  The result is then Mathlib's `HolderOnWith.dimH_image_le`.  Note that the hypothesis
is one-sided, so `φ` is only Hölder on `G '' S`, and only there is well defined.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Work.Transfer

/-- Convert a real Hölder-type estimate `‖u - v‖ ≤ C * ‖z - w‖ ^ a` (with `0 ≤ a`) into the
`ℝ≥0∞`-valued statement `edist u v ≤ C * edist z w ^ a` used by `HolderOnWith`. -/
private lemma edist_of_norm_le {C : NNReal} {a : ℝ} (ha : 0 ≤ a) {u v z w : ℂ}
    (h : ‖u - v‖ ≤ (C : ℝ) * ‖z - w‖ ^ a) :
    edist u v ≤ (C : ℝ≥0∞) * edist z w ^ ((Real.toNNReal a : ℝ≥0) : ℝ) := by
  have hz : (0 : ℝ) ≤ ‖z - w‖ := norm_nonneg _
  calc edist u v = ENNReal.ofReal ‖u - v‖ := by rw [edist_dist, dist_eq_norm]
  _ ≤ ENNReal.ofReal ((C : ℝ) * ‖z - w‖ ^ a) := ENNReal.ofReal_le_ofReal h
  _ = (C : ℝ≥0∞) * (ENNReal.ofReal ‖z - w‖) ^ a := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.coe_nnreal_eq,
            ENNReal.ofReal_rpow_of_nonneg hz ha]
  _ = (C : ℝ≥0∞) * (ENNReal.ofReal ‖z - w‖) ^ ((Real.toNNReal a : ℝ≥0) : ℝ) := by
        rw [Real.coe_toNNReal a ha]
  _ = (C : ℝ≥0∞) * edist z w ^ ((Real.toNNReal a : ℝ≥0) : ℝ) := by
        rw [edist_dist, dist_eq_norm]

theorem dimH_image_le_div_of_dist_le {X : Type*} {S : Set X} {F G : X → ℂ}
    {C : NNReal} {a : ℝ} (ha : 0 < a)
    (h : ∀ x ∈ S, ∀ y ∈ S, ‖F x - F y‖ ≤ (C : ℝ) * ‖G x - G y‖ ^ a) :
    dimH (F '' S) ≤ dimH (G '' S) / (Real.toNNReal a : ENNReal) := by
  classical
  -- Two points of `S` with the same image under `G` have the same image under `F`.
  have hwell : ∀ x ∈ S, ∀ y ∈ S, G x = G y → F x = F y := by
    intro x hx y hy hxy
    have hle : ‖F x - F y‖ ≤ 0 := by
      have h1 := h x hx y hy
      rw [hxy, sub_self, norm_zero, Real.zero_rpow ha.ne', mul_zero] at h1
      exact h1
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))
  -- The map sending `G x` to `F x`, extended arbitrarily off `G '' S`.
  let φ : ℂ → ℂ := fun z => if hz : ∃ x, x ∈ S ∧ G x = z then F (Classical.choose hz) else 0
  have hφ : ∀ z (hz : ∃ x, x ∈ S ∧ G x = z), φ z = F (Classical.choose hz) := by
    intro z hz
    simp only [φ, dite_eq_left hz]
  -- `φ` is Hölder with exponent `a` and constant `C` on `G '' S`.
  have hholder : HolderOnWith C (Real.toNNReal a) φ (G '' S) := by
    intro z hz w hw
    rw [hφ z hz, hφ w hw]
    have hzc := Classical.choose_spec hz
    have hwc := Classical.choose_spec hw
    refine edist_of_norm_le ha.le ?_
    have h1 := h (Classical.choose hz) hzc.1 (Classical.choose hw) hwc.1
    rw [hzc.2, hwc.2] at h1
    exact h1
  -- ... and its image of `G '' S` is exactly `F '' S`.
  have himg : φ '' (G '' S) = F '' S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨Classical.choose hz, (Classical.choose_spec hz).1, (hφ z hz).symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hz : ∃ y, y ∈ S ∧ G y = G x := ⟨x, hx, rfl⟩
      refine ⟨G x, ⟨x, hx, rfl⟩, ?_⟩
      rw [hφ (G x) hz]
      exact hwell _ (Classical.choose_spec hz).1 x hx (Classical.choose_spec hz).2
  have hmain := hholder.dimH_image_le (Real.toNNReal_pos.mpr ha)
  rwa [himg] at hmain

end Work.Transfer
