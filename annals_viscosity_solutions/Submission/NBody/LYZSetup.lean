import Submission.NBody.LYZIntegral
import Submission.NBody.LYZGeometry
import Mathlib

/-!
# The numerical set-up of the Liu--Yan--Zhou proof

This module converts the potential-integral estimate (`potentialIntegral_le_log`) into the
concrete form needed for the construction of the `h`-minimisers: for every direction `b` in a
small cone around the asymptotic direction `a`,

    `∫₀^T U(z + t b) dt ≤ (2h) B log(2T + 2M + 1)`,

with an explicit constant `B` depending only on the masses, `N`, `ν`, `M` and `h`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The constant `B` multiplying `log(2T + 2M + 1)` in the potential-integral bound. -/
noncomputable def lyzB (m : Fin N → ℝ) (h N ν M : ℝ) : ℝ :=
  (2 * h)⁻¹ * (∑ i, m i) ^ 2 * N ^ 2 * ν⁻¹ *
    (1 + (Real.log M + |Real.log ν|) / Real.log (2 * M + 1))

/-- **The potential integral along a ray, in the form used by the construction.** -/
theorem potentialIntegral_le_logB {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (hN : 2 ≤ N)
    {z b : EN E N} {ν K M T : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hK : 1 ≤ K) (hKM : K ≤ M)
    (hM1 : 1 ≤ M) (hKb : ‖b‖ ≤ K) (hKz : ‖z‖ ≤ M) (hT : 0 ≤ T)
    (hsepz : ∀ i j, i ≠ j → ν ≤ ‖z i - z j‖)
    (hsepb : ∀ i j, i ≠ j → ν ≤ ‖b i - b j‖)
    (hangle : ∀ i j, i ≠ j →
      (1 / 2) * (‖z i - z j‖ * ‖b i - b j‖) ≤ inner ℝ (z i - z j) (b i - b j))
    (hνz : ν ≤ 2 * K * T + 2 * ‖z‖) (hνM : ν ≤ 2 * K * T + 2 * M) :
    ∫ t in (0:ℝ)..T, U m (z + t • b) ≤ (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * ν⁻¹ *
      (1 + (Real.log M + |Real.log ν|) / Real.log (2 * M + 1)) * Real.log (2 * T + 2 * M + 1) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hlogM : 0 < Real.log (2 * M + 1) := by
    apply Real.log_pos
    linarith
  have hmain := potentialIntegral_le_log (m := m) hm hN (z := z) (b := b) (ν := ν) (K := K)
    (Msz := M) (T := T) hν hKpos hKb hKz hsepz hsepb hangle hT hνz hνM
  have hlogM0 : 0 ≤ Real.log (2 * M + 1) := hlogM.le
  have hT0 : 0 ≤ Real.log (2 * T + 2 * M + 1) := by
    apply Real.log_nonneg
    linarith
  -- bounds on the two logarithms
  have h1 : Real.log (2 * K * T + 2 * M) ≤ Real.log (2 * T + 2 * M + 1) + Real.log M := by
    have h2 : 2 * K * T + 2 * M ≤ M * (2 * T + 2 * M + 1) := by
      have h3 : 2 * K * T ≤ 2 * M * T := by nlinarith
      nlinarith [hM1, hT]
    have h4 : (0:ℝ) < 2 * K * T + 2 * M := by nlinarith [hM1, hT]
    calc Real.log (2 * K * T + 2 * M) ≤ Real.log (M * (2 * T + 2 * M + 1)) :=
          Real.log_le_log h4 h2
      _ = Real.log M + Real.log (2 * T + 2 * M + 1) :=
          Real.log_mul (by linarith) (by linarith)
      _ = Real.log (2 * T + 2 * M + 1) + Real.log M := by ring
  have hνlog : -Real.log ν = |Real.log ν| := by
    rw [abs_of_nonpos (Real.log_nonpos hν.le hν1)]
  have hlogle : Real.log (2 * M + 1) ≤ Real.log (2 * T + 2 * M + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : -Real.log ν ≤ |Real.log ν| / Real.log (2 * M + 1) * Real.log (2 * T + 2 * M + 1) := by
    rw [hνlog, div_mul_eq_mul_div, le_div_iff₀ hlogM]
    exact mul_le_mul_of_nonneg_left hlogle (abs_nonneg _)
  have h3 : Real.log M ≤ Real.log M / Real.log (2 * M + 1) * Real.log (2 * T + 2 * M + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlogM]
    exact mul_le_mul_of_nonneg_left hlogle (Real.log_nonneg hM1)
  have hkey : Real.log (2 * K * T + 2 * M) - Real.log ν
      ≤ (1 + (Real.log M + |Real.log ν|) / Real.log (2 * M + 1)) * Real.log (2 * T + 2 * M + 1) := by
    have h5 : (Real.log M + |Real.log ν|) / Real.log (2 * M + 1) * Real.log (2 * T + 2 * M + 1)
        = Real.log M / Real.log (2 * M + 1) * Real.log (2 * T + 2 * M + 1)
          + |Real.log ν| / Real.log (2 * M + 1) * Real.log (2 * T + 2 * M + 1) := by ring
    linarith
  refine hmain.trans ?_
  have hnn : 0 ≤ Real.log (2 * T + 2 * M + 1) := hT0
  have hfac : 0 ≤ 1 + (Real.log M + |Real.log ν|) / Real.log (2 * M + 1) := by
    have h6 : 0 ≤ (Real.log M + |Real.log ν|) / Real.log (2 * M + 1) :=
      div_nonneg (add_nonneg (Real.log_nonneg hM1) (abs_nonneg _)) hlogM0
    linarith
  calc (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * ν⁻¹ * (Real.log (2 * K * T + 2 * M) - Real.log ν)
      ≤ (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * ν⁻¹ *
          ((1 + (Real.log M + |Real.log ν|) / Real.log (2 * M + 1)) * Real.log (2 * T + 2 * M + 1)) := by
        refine mul_le_mul_of_nonneg_left hkey ?_
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr hν.le)
    _ = (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * ν⁻¹ *
          (1 + (Real.log M + |Real.log ν|) / Real.log (2 * M + 1)) * Real.log (2 * T + 2 * M + 1) := by
        ring

end Submission.NBody
