/-
# Density of the contact set (the base case of the decay lemma)

Fan, arXiv:2509.01138, Corollary "density corollary" -- the first step of the iteration that
produces the weak Harnack inequality.  If a non-negative solution `φ` of `Fop C ε = 0` satisfies
`inf φ ≤ 1` on a small ball, then the contact set of the (large but universal) opening `16`
occupies a definite proportion of `closedBall 0 (1/2)`.

The constants are adjusted to this formalisation: the contact points of `contactPt` live in
`closedBall 0 (1/2)`, so the vertex ball is taken to be `closedBall 0 (1/16)` and the opening `16`.
With `‖y‖ ≤ 1/16`, `‖x₁‖ ≤ 1/16`, `φ x₁ ≤ 1` and `φ ≥ 0` on `closedBall 0 1`:
* for `‖z‖ = 1`, `‖z - y‖ ≥ 15/16` so `φ z + 8 ‖z - y‖² ≥ 8·(15/16)² > 9/8`;
* at `x₁`, `φ x₁ + 8‖x₁ - y‖² ≤ 1 + 8/64 = 9/8`.
Hence the minimum of `z ↦ φ z + 8‖z-y‖²` over `closedBall 0 1` is attained at an interior point
`x` with `8‖x - y‖² ≤ 9/8`, so `‖x - y‖ ≤ 3/8` and `‖x‖ ≤ 7/16 < 1/2`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Enlarge

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **Density of the contact set** (base case of the decay lemma). -/
theorem density_contactPt {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    (hε16 : 3 * ε * 16 ≤ c / 2)
    (hpos : ∀ x ∈ closedBall 0 1, 0 ≤ φ x)
    (hinf : ∃ x₁ ∈ closedBall 0 (1 / 16), φ x₁ ≤ 1) :
    ENNReal.ofReal ((1 / 8 : ℝ) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4)
        * volume (closedBall (0 : ℝ⁴) (1 / 2))
      ≤ volume (contactPt 16 φ ∩ closedBall (0 : ℝ⁴) (1 / 2)) := by
  obtain ⟨x₁, hx₁mem, hx₁le⟩ := hinf
  have hx₁1 : x₁ ∈ closedBall (0 : ℝ⁴) 1 :=
    closedBall_subset_closedBall (by norm_num) hx₁mem
  have hcontφ : ContinuousOn φ (closedBall (0 : ℝ⁴) 1) :=
    hφ.continuousOn.mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 3 / 2))
  have hcontact : ∀ y ∈ closedBall (0 : ℝ⁴) (1 / 16), ∃ x ∈ closedBall (0 : ℝ⁴) (1 / 2),
      ∀ z ∈ closedBall 0 1, φ x + 16 / 2 * ‖x - y‖ ^ 2 ≤ φ z + 16 / 2 * ‖z - y‖ ^ 2 := by
    intro y hy
    have hcont : ContinuousOn (fun z : ℝ⁴ => φ z + 16 / 2 * ‖z - y‖ ^ 2)
        (closedBall (0 : ℝ⁴) 1) :=
      hcontφ.add ((continuous_const.mul
        ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn)
    obtain ⟨x, hxmem, hxmin⟩ := (isCompact_closedBall (0 : ℝ⁴) 1).exists_isMinOn
      ⟨0, by simp⟩ hcont
    have h8 : (16 : ℝ) / 2 = 8 := by norm_num
    have hle : φ x + 8 * ‖x - y‖ ^ 2 ≤ φ x₁ + 8 * ‖x₁ - y‖ ^ 2 := by
      have h := hxmin hx₁1
      simpa only [h8, Set.mem_ofPred_eq] using h
    have hy1 : ‖y‖ ≤ 1 / 16 := by
      have := mem_closedBall.mp hy; rwa [dist_zero_right] at this
    have hx₁n : ‖x₁‖ ≤ 1 / 16 := by
      have := mem_closedBall.mp hx₁mem; rwa [dist_zero_right] at this
    have h1 : ‖x₁ - y‖ ≤ 1 / 8 := by
      calc ‖x₁ - y‖ ≤ ‖x₁‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 1 / 8 := by linarith
    have hsq : ‖x₁ - y‖ ^ 2 ≤ 1 / 64 := by
      nlinarith [h1, norm_nonneg (x₁ - y)]
    have h0 : 0 ≤ φ x := hpos x hxmem
    have hxy : ‖x - y‖ ^ 2 ≤ 9 / 64 := by nlinarith [hle, hx₁le, hsq, h0]
    have hxy' : ‖x - y‖ ≤ 3 / 8 := by
      have h2 : 0 ≤ ‖x - y‖ := norm_nonneg _
      nlinarith [hxy, h2, sq_nonneg (‖x - y‖ - 3 / 8)]
    refine ⟨x, ?_, fun z hz => hxmin hz⟩
    rw [mem_closedBall, dist_zero_right]
    have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      have h5 : ‖x - y + y‖ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      rwa [show x - y + y = x by abel] at h5
    linarith
  have hmeas := contactSet_measure hφ hC hc hcq hε (by norm_num : (0 : ℝ) < 16) hε16 heq
    isClosed_closedBall hcontact
  have hsub : contactSet 16 φ (closedBall (0 : ℝ⁴) (1 / 16))
      ⊆ contactPt 16 φ ∩ closedBall (0 : ℝ⁴) (1 / 2) := fun x hx =>
    ⟨contactSet_subset_contactPt (closedBall_subset_closedBall (by norm_num)) hx,
      closedBall_subset_closedBall (by norm_num) (contactSet_subset_closedBall hx)⟩
  have hvolV : volume (closedBall (0 : ℝ⁴) (1 / 16))
      = ENNReal.ofReal ((1 / 16 : ℝ) ^ 4) * volume (ball (0 : ℝ⁴) 1) := by
    have h := Measure.addHaar_closedBall (volume : Measure ℝ⁴) (0 : ℝ⁴)
      (by norm_num : (0 : ℝ) ≤ 1 / 16)
    simpa using h
  have hvol0 : volume (closedBall (0 : ℝ⁴) (1 / 2))
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ 4) * volume (ball (0 : ℝ⁴) 1) := by
    have h := Measure.addHaar_closedBall (volume : Measure ℝ⁴) (0 : ℝ⁴)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using h
  have hratio : ENNReal.ofReal ((1 / 8 : ℝ) ^ 4) * volume (closedBall (0 : ℝ⁴) (1 / 2))
      = volume (closedBall (0 : ℝ⁴) (1 / 16)) := by
    rw [hvolV, hvol0, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (1 / 8) ^ 4),
      show ((1 / 8 : ℝ) ^ 4 * (1 / 2) ^ 4) = (1 / 16) ^ 4 by norm_num]
  set K' : ℝ := (1 + (2 * trOp C / c + 3)) ^ 4 with hK'def
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2]
  have hKpos : 0 < 1 + (2 * trOp C / c + 3) := by
    have h2 : 0 ≤ 2 * trOp C / c := div_nonneg (by linarith) hc.le
    linarith
  have hK'pos : 0 < K' := by rw [hK'def]; positivity
  have hofK : ENNReal.ofReal (K'⁻¹) = (ENNReal.ofReal K')⁻¹ := ENNReal.ofReal_inv_of_pos hK'pos
  calc ENNReal.ofReal ((1 / 8 : ℝ) ^ 4 / K') * volume (closedBall (0 : ℝ⁴) (1 / 2))
      = (ENNReal.ofReal ((1 / 8 : ℝ) ^ 4) * ENNReal.ofReal (K'⁻¹))
          * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (1 / 8) ^ 4)]
    _ = ENNReal.ofReal (K'⁻¹)
          * (ENNReal.ofReal ((1 / 8 : ℝ) ^ 4) * volume (closedBall (0 : ℝ⁴) (1 / 2))) := by
        rw [mul_comm (ENNReal.ofReal ((1 / 8 : ℝ) ^ 4)) (ENNReal.ofReal (K'⁻¹)), mul_assoc]
    _ = ENNReal.ofReal (K'⁻¹) * volume (closedBall (0 : ℝ⁴) (1 / 16)) := by rw [hratio]
    _ ≤ ENNReal.ofReal (K'⁻¹)
          * (ENNReal.ofReal K' * volume (contactSet 16 φ (closedBall (0 : ℝ⁴) (1 / 16)))) :=
        mul_le_mul_of_nonneg_left hmeas (by simp)
    _ = volume (contactSet 16 φ (closedBall (0 : ℝ⁴) (1 / 16))) := by
        rw [← mul_assoc, hofK,
          ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hK'pos))
            ENNReal.ofReal_ne_top, one_mul]
    _ ≤ volume (contactPt 16 φ ∩ closedBall (0 : ℝ⁴) (1 / 2)) := measure_mono hsub

end

end Submission
