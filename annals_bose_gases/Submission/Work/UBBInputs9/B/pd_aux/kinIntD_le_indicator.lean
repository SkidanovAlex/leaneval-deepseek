import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.UBBInputs9.B.fderiv_chiScale_eq_zero_of_norm_gt
import Submission.Work.UBBInputs9.B.kinWordW_le_sup
import Submission.Work.UBBInputs9.B.pd_aux.kinIntD_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The bump `chiScale s` vanishes strictly outside its ball of radius `s/2`. -/
lemma kinIntD_chiScale_vanishes {s : ℝ} (hs : 0 < s) {y : ℝ³} (h : s / 2 < ‖y‖) :
    chiScale s y = 0 := by
  rw [chiScale]
  apply chi_eq_zero_of_norm_gt
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hs))]
  rw [show (1 : ℝ) / 2 = s⁻¹ * (s / 2) by field_simp]
  exact mul_lt_mul_of_pos_left h (inv_pos.mpr hs)

/-- A point of the centred cube `acube ℓ` (`ℓ > 0`) has norm at most `ℓ`. -/
lemma kinIntD_norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℝ³} (hz : z ∈ acube ℓ) :
    ‖z‖ ≤ ℓ := by
  have hsq : ‖z‖ ^ 2 ≤ ℓ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ m : Fin 3, z.ofLp m ^ 2 ≤ ∑ _m : Fin 3, (ℓ / 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro m _
          have hm := (mem_acube_iff ℓ z).1 hz m
          rw [Set.mem_Icc] at hm
          nlinarith [hm.1, hm.2]
      _ = 3 * (ℓ / 2) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
      _ ≤ ℓ ^ 2 := by nlinarith
  have h2 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg hℓ.le] at h2

/-- For `‖u‖` large, the window-derivative integrand `kinIntD ℓ d u x` vanishes for every
`x` in the big box: the whole lifted cutoff `y ↦ chiB ℓ d u (y 0)` is *identically zero* in a
neighbourhood of `x`, because `‖x 0 − (ℓd)•u‖ > ℓd/2` there. -/
lemma kinIntD_eq_zero_of_norm_gt {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³}
    (hu : 1 / d + 1 < ‖u‖) {x : X1} (hx : x ∈ Submission.BoseGases.abox 1 ℓ) :
    kinIntD ℓ d u x = 0 := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hx0 : x 0 ∈ acube ℓ := (mem_abox_iff 1 ℓ x).1 hx 0
  have hx0norm : ‖x 0‖ ≤ ℓ := kinIntD_norm_le_of_mem_acube hℓ hx0
  -- Distance lower bound for the shifted point `x 0 - (ℓd)•u`.
  have hbig : (ℓ * d) / 2 < ‖x 0 - (ℓ * d) • u‖ := by
    have hnormu : ‖(ℓ * d) • u‖ = ℓ * d * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hld]
    have hle : ℓ * d * ‖u‖ - ‖x 0‖ ≤ ‖x 0 - (ℓ * d) • u‖ := by
      have h1 : ‖(ℓ * d) • u‖ - ‖x 0‖ ≤ ‖(ℓ * d) • u - x 0‖ :=
        le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
      have h2 : ‖(ℓ * d) • u - x 0‖ = ‖x 0 - (ℓ * d) • u‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [hnormu, h2] at h1
      exact h1
    have hkey : 1 + d < d * ‖u‖ := by
      have hdt : d * (1 / d + 1) < d * ‖u‖ := mul_lt_mul_of_pos_left hu hd
      have hdt' : d * (1 / d + 1) = 1 + d := by
        rw [mul_add, mul_one_div_cancel (ne_of_gt hd), mul_one]
      linarith
    have hkey2 : ℓ + ℓ * d < ℓ * (d * ‖u‖) := by
      have := mul_lt_mul_of_pos_left hkey hℓ
      nlinarith [this]
    have hmid : (ℓ * d) / 2 < ℓ * d * ‖u‖ - ℓ := by nlinarith [hkey2, hℓ, hd]
    linarith [hmid, hle]
  -- The lifted cutoff is eventually zero near `x`.
  have hzero : fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0)) x = 0 := by
    have hδ : 0 < ‖x 0 - (ℓ * d) • u‖ - (ℓ * d) / 2 := by linarith
    have hev : (fun y : X1 => chiB ℓ d u (y 0)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
      rw [Metric.mem_ball] at hy
      have hy0 : (ℓ * d) / 2 < ‖y 0 - (ℓ * d) • u‖ := by
        have hdiff : ‖y 0 - x 0‖ ≤ ‖y - x‖ := by
          have := norm_le_pi_norm (ι := Fin 1) (y - x) 0
          simpa using this
        rw [dist_eq_norm] at hy
        have htri : ‖x 0 - (ℓ * d) • u‖ - ‖y 0 - x 0‖ ≤ ‖y 0 - (ℓ * d) • u‖ := by
          have h2 : ‖y 0 - (ℓ * d) • u - (y 0 - x 0)‖ ≤ ‖y 0 - (ℓ * d) • u‖ + ‖y 0 - x 0‖ :=
            norm_sub_le _ _
          have heq : y 0 - (ℓ * d) • u - (y 0 - x 0) = x 0 - (ℓ * d) • u := by abel
          rw [heq] at h2
          linarith
        linarith
      have hchi : chiScale (ℓ * d) (y 0 - (ℓ * d) • u) = 0 :=
        kinIntD_chiScale_vanishes hld hy0
      simp only [chiB, hchi, mul_zero]
    rw [hev.fderiv_eq]
    simp
  unfold kinIntD
  rw [hzero]
  simp

lemma kinIntD_le_indicator {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) : ∃ R C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X 1), x ∈ Submission.BoseGases.abox 1 ℓ → Work.UBBInputs9.B.kinIntD ℓ d u x ≤ C * (Metric.closedBall 0 R).indicator (fun _ => (1 : ℝ)) u := by
  obtain ⟨C, hC0, hC⟩ := kinIntD_le (ℓ := ℓ) (d := d) hℓ hd
  refine ⟨1 / d + 1, C, hC0, ?_⟩
  intro u x hx
  by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) (1 / d + 1)
  · rw [Set.indicator_of_mem hu]
    simpa using hC u x
  · rw [Set.indicator_of_notMem hu, mul_zero]
    have hlt : 1 / d + 1 < ‖u‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
      exact not_le.mp hu
    rw [kinIntD_eq_zero_of_norm_gt hℓ hd hlt hx]

end Work.UBBInputs9.B.pd_aux
