import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- Inversion `w ↦ w⁻¹` maps the inner half `annulus ρ ∩ ball 0 1 = {ρ < ‖w‖ < 1}` of the
inversion-symmetric annulus `annulus ρ = {ρ < ‖w‖ < ρ⁻¹}` bijectively onto its outer half
`annulus ρ \ closedBall 0 1 = {1 < ‖z‖ < ρ⁻¹}`.

This is pure bookkeeping in the modulus: `‖w⁻¹‖ = ‖w‖⁻¹` and `x ↦ x⁻¹` is an order-reversing
involution of `(0, ∞)` exchanging `(ρ, 1)` with `(1, ρ⁻¹)` (because `ρ < 1` and hence
`1 < ρ⁻¹`). -/
theorem inv_image_annulus_inter_ball {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (fun w : ℂ => w⁻¹) '' (annulus ρ ∩ ball 0 1) = annulus ρ \ closedBall 0 1 := by
  have hρinv : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).2 hρ1
  ext z
  simp only [annulus, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_image, Set.mem_sdiff,
    Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le]
  constructor
  · rintro ⟨w, ⟨⟨hw1, hw2⟩, hwb⟩, hwz⟩
    rw [← hwz]
    have hwpos : 0 < ‖w‖ := lt_trans hρ0 hw1
    have hinv : 1 < ‖w‖⁻¹ := (one_lt_inv₀ hwpos).2 hwb
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [norm_inv]; exact lt_trans hρ1 hinv
    · rw [norm_inv]; exact (inv_lt_inv₀ hwpos hρ0).2 hw1
    · rw [norm_inv]; exact hinv
  · rintro ⟨⟨hz1, hz2⟩, hzcb⟩
    have hzpos : 0 < ‖z‖ := lt_trans hρ0 hz1
    have key : ‖z‖⁻¹ < 1 := by
      simpa using (inv_lt_inv₀ hzpos one_pos).2 hzcb
    have key2 : ρ < ‖z‖⁻¹ := by
      simpa using (inv_lt_inv₀ (inv_pos.mpr hρ0) hzpos).2 hz2
    refine ⟨z⁻¹, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [norm_inv]; exact key2
    · rw [norm_inv]; exact lt_trans key hρinv
    · rw [norm_inv]; exact key
    · exact inv_inv z

end Work.RPB1a
