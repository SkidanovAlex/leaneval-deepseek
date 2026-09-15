import Submission.FUP.PSHToFourier2
import Submission.Commons.Analysis.Real.exists_mul_log_le_mul_self_add
import Submission.Commons.Analysis.Real.exists_log_sub_div_log_sq_bound
import Submission.Commons.Measure.EuclideanSpace.integrable_exp_neg_smoothTransition_log_sq

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# §5 of Cohen's paper, part 3: the four estimates of `prop:psh_to_bounded_fourier`

This module completes the proof of `psh_to_bounded_fourier_statement` (given Hörmander's
`∂̄` theorem, formalised as an interface in `Submission.FUP.Hormander`).
-/

namespace Submission.FUP

/-! ### Local upper bounds for the weight `φ` -/

/-- The constant bounding `φ` on a polydisc of radius `1/8` around a point of norm `≤ 1/4`. -/
noncomputable def Bsmall (ρ CLip : ℝ) (d : ℕ) : ℝ :=
  2 * (ρ * (Real.sqrt d * (3 / 8))) + 10 * (d : ℝ) * max 0 (Real.log (9 * (d : ℝ) / 64))
    + ρ * (Real.sqrt d * (3 / 8))

lemma norm_imVec_le_sqrt_mul (z : ℂᵈ) : ‖imVec z‖ ≤ Real.sqrt (d : ℝ) * ‖z‖ :=
  norm_imVec_le z

lemma section5Phi_le_small {ρ CLip : ℝ} (hρ : 0 < ρ) (hCLip : 0 ≤ CLip)
    {u u0 : ℂᵈ → ℝ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0nonpos : ∀ x : ℝᵈ, u0 (toCpx x) ≤ 0)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    {z : ℂᵈ} (hz : ‖z‖ ≤ 1 / 4) :
    ∀ w ∈ Metric.closedBall z (1 / 8), section5Phi ρ u u0 w ≤ Bsmall ρ CLip d := by
  intro w hw
  have hw1 : ‖w‖ ≤ 3 / 8 := by
    have h : dist w z ≤ 1 / 8 := by simpa [Metric.mem_closedBall] using hw
    have h2 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      have := norm_le_add_norm_add w (-z)
      simpa [sub_eq_add_neg] using this
    have h3 : ‖w - z‖ ≤ 1 / 8 := by simpa [dist_eq_norm] using h
    linarith
  have him : ‖imVec w‖ ≤ Real.sqrt (d : ℝ) * (3 / 8) := by
    calc ‖imVec w‖ ≤ Real.sqrt (d : ℝ) * ‖w‖ := norm_imVec_le w
      _ ≤ Real.sqrt (d : ℝ) * (3 / 8) :=
          mul_le_mul_of_nonneg_left hw1 (Real.sqrt_nonneg _)
  have hsum : ∑ j, ‖w j‖ ^ 2 ≤ (d : ℝ) * (3 / 8) ^ 2 := by
    calc ∑ j : Fin d, ‖w j‖ ^ 2 ≤ ∑ _j : Fin d, (3 / 8) ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h1 : ‖w j‖ ≤ ‖w‖ := norm_le_pi_norm w j
            nlinarith [norm_nonneg (w j), norm_nonneg w]
      _ = (d : ℝ) * (3 / 8) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlog : Real.log (∑ j, ‖w j‖ ^ 2)
      ≤ max 0 (Real.log (9 * (d : ℝ) / 64)) := by
    rcases eq_or_lt_of_le (sum_sq_nonneg w) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact le_max_left _ _
    · refine le_trans (Real.log_le_log h0 ?_) (le_max_right _ _)
      nlinarith [hsum]
  have h1 : 2 * u w ≤ 2 * (ρ * (Real.sqrt d * (3 / 8))) := by
    have h := (hugrowth w).2
    have h2 : u (toCpx (reVec w)) ≤ 0 := hunonpos (reVec w)
    nlinarith [h, h2, him, hρ.le]
  have h2 : ρ * u0 w ≤ (ρ / 2) * (Real.sqrt d * (3 / 8)) := by
    have h := (hu0growth w).2
    have h3 : u0 (toCpx (reVec w)) ≤ 0 := hu0nonpos (reVec w)
    have h4 : u0 w ≤ (1 / 2) * ‖imVec w‖ := by linarith
    calc ρ * u0 w ≤ ρ * ((1 / 2) * ‖imVec w‖) := mul_le_mul_of_nonneg_left h4 hρ.le
      _ ≤ ρ * ((1 / 2) * (Real.sqrt d * (3 / 8))) := by
          refine mul_le_mul_of_nonneg_left ?_ hρ.le
          linarith [him]
      _ = (ρ / 2) * (Real.sqrt d * (3 / 8)) := by ring
  have h3 : (ρ / 2) * (imNorm w - 1) ≤ (ρ / 2) * (Real.sqrt d * (3 / 8)) := by
    have h := imNorm_sub_one_le w
    have h4 : 0 ≤ ρ / 2 := by positivity
    calc (ρ / 2) * (imNorm w - 1) ≤ (ρ / 2) * ‖imVec w‖ :=
          mul_le_mul_of_nonneg_left h h4
      _ ≤ (ρ / 2) * (Real.sqrt d * (3 / 8)) := mul_le_mul_of_nonneg_left him h4
  have h4 : logWeight w ≤ 10 * (d : ℝ) * max 0 (Real.log (9 * (d : ℝ) / 64)) := by
    rw [logWeight]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [section5Phi, Bsmall]
  linarith [h1, h2, h3, h4]

end Submission.FUP

namespace Submission.FUP

/-- The constant bounding `φ` on the polydisc `P(x,1/8)` in terms of `u(x)`, `u₀(x)` and
`log(1+|x|)`. -/
noncomputable def Bsmall2 (ρ CLip : ℝ) (d : ℕ) : ℝ :=
  2 * (CLip * (Real.sqrt d / 8)) + 2 * (ρ * (Real.sqrt d / 8))
    + 40 * (d : ℝ) * Real.log (1 + Real.sqrt d / 8) + ρ * (Real.sqrt d / 8)
    + ρ * (Real.sqrt d / 8)

lemma norm_le_add_norm_add' (a b : ℂᵈ) : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
  have h : ‖a‖ = ‖b + (a - b)‖ := by
    congr 1
    abel
  rw [h]
  exact norm_add_le _ _

lemma reVec_sub (a b : ℂᵈ) : reVec (a - b) = reVec a - reVec b := by
  ext i; simp [reVec]

lemma imVec_sub (a b : ℂᵈ) : imVec (a - b) = imVec a - imVec b := by
  ext i; simp [imVec]

/-- **The local bound on `φ`**: on `P(x,1/8)` the weight is at most
`2u(x) + ρu₀(x) + 20d log(1+|x|)` plus a constant depending only on `ρ, C_Lip, d`. -/
lemma section5Phi_le_at {ρ CLip : ℝ} (hρ : 0 < ρ) (hCLip : 0 ≤ CLip)
    {u u0 : ℂᵈ → ℝ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    {x : ℝᵈ} :
    ∀ w ∈ Metric.closedBall (toCpx x) (1 / 8),
      section5Phi ρ u u0 w ≤ 2 * u (toCpx x) + ρ * u0 (toCpx x)
        + 20 * (d : ℝ) * Real.log (1 + ‖x‖) + Bsmall2 ρ CLip d := by
  intro w hw
  have hdist : ‖w - toCpx x‖ ≤ 1 / 8 := by
    have h : dist w (toCpx x) ≤ 1 / 8 := by simpa [Metric.mem_closedBall] using hw
    simpa [dist_eq_norm] using h
  have hre : ‖reVec w - x‖ ≤ Real.sqrt d / 8 := by
    have h1 : reVec w - x = reVec (w - toCpx x) := by
      rw [reVec_sub, reVec_toCpx]
    rw [h1]
    calc ‖reVec (w - toCpx x)‖ ≤ Real.sqrt (d : ℝ) * ‖w - toCpx x‖ := norm_reVec_le _
      _ ≤ Real.sqrt (d : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _)
      _ = Real.sqrt d / 8 := by ring
  have him : ‖imVec w‖ ≤ Real.sqrt d / 8 := by
    have h1 : imVec w = imVec (w - toCpx x) := by
      rw [imVec_sub, imVec_toCpx, sub_zero]
    rw [h1]
    calc ‖imVec (w - toCpx x)‖ ≤ Real.sqrt (d : ℝ) * ‖w - toCpx x‖ := norm_imVec_le _
      _ ≤ Real.sqrt (d : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _)
      _ = Real.sqrt d / 8 := by ring
  have hsq : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hs : (0 : ℝ) < 1 + Real.sqrt d / 8 := by positivity
  have h1 : 2 * u w ≤ 2 * u (toCpx x) + 2 * (CLip * (Real.sqrt d / 8))
      + 2 * (ρ * (Real.sqrt d / 8)) := by
    have h := (hugrowth w).2
    have h2 : u (toCpx (reVec w)) - u (toCpx x) ≤ CLip * ‖reVec w - x‖ := by
      have := hulip (reVec w) x
      linarith [le_abs_self (u (toCpx (reVec w)) - u (toCpx x))]
    have h3 : CLip * ‖reVec w - x‖ ≤ CLip * (Real.sqrt d / 8) :=
      mul_le_mul_of_nonneg_left hre hCLip
    nlinarith [h, h2, h3, him, hρ.le]
  have h2 : logWeight w ≤ 20 * (d : ℝ) * Real.log (1 + ‖x‖)
      + 40 * (d : ℝ) * Real.log (1 + Real.sqrt d / 8) := by
    have h := logWeight_le w
    have hA : ‖reVec w‖ ≤ ‖x‖ + Real.sqrt d / 8 := by
      have h6 : ‖reVec w‖ ≤ ‖reVec w - x‖ + ‖x‖ := by
        have h7 := norm_le_add_norm_add (reVec w) (-x)
        simpa [sub_eq_add_neg] using h7
      linarith
    have hB : 1 + ‖reVec w‖ ≤ (1 + ‖x‖) * (1 + Real.sqrt d / 8) := by
      nlinarith [norm_nonneg x, Real.sqrt_nonneg (d : ℝ)]
    have hC : Real.log (1 + ‖reVec w‖) ≤ Real.log (1 + ‖x‖) + Real.log (1 + Real.sqrt d / 8) := by
      calc Real.log (1 + ‖reVec w‖)
          ≤ Real.log ((1 + ‖x‖) * (1 + Real.sqrt d / 8)) :=
            Real.log_le_log (by positivity) hB
        _ = Real.log (1 + ‖x‖) + Real.log (1 + Real.sqrt d / 8) :=
            Real.log_mul hsq.ne' hs.ne'
    have hD : Real.log (1 + ‖imVec w‖) ≤ Real.log (1 + Real.sqrt d / 8) :=
      Real.log_le_log (by positivity) (by linarith)
    have hd0 : (0:ℝ) ≤ 20 * (d : ℝ) := by positivity
    have hC' := mul_le_mul_of_nonneg_left hC hd0
    have hD' := mul_le_mul_of_nonneg_left hD hd0
    have hC'' : 20 * (d : ℝ) * (Real.log (1 + ‖x‖) + Real.log (1 + Real.sqrt d / 8))
        = 20 * (d : ℝ) * Real.log (1 + ‖x‖)
          + 20 * (d : ℝ) * Real.log (1 + Real.sqrt d / 8) := by ring
    rw [hC''] at hC'
    nlinarith [h, hC', hD']
  have h3 : ρ * u0 w ≤ ρ * u0 (toCpx x) + ρ * (Real.sqrt d / 8) + (ρ / 2) * (Real.sqrt d / 8) := by
    have h := (hu0growth w).2
    have h2 : u0 (toCpx (reVec w)) - u0 (toCpx x) ≤ 1 * ‖reVec w - x‖ := by
      have := hu0lip (reVec w) x
      linarith [le_abs_self (u0 (toCpx (reVec w)) - u0 (toCpx x))]
    have h3 : 1 * ‖reVec w - x‖ ≤ 1 * (Real.sqrt d / 8) := by
      rw [one_mul, one_mul]; exact hre
    have h5 : u0 w ≤ u0 (toCpx x) + Real.sqrt d / 8 + (1 / 2) * (Real.sqrt d / 8) := by
      have h6 : (1 / 2) * ‖imVec w‖ ≤ (1 / 2) * (Real.sqrt d / 8) :=
        mul_le_mul_of_nonneg_left him (by norm_num)
      linarith
    calc ρ * u0 w ≤ ρ * (u0 (toCpx x) + Real.sqrt d / 8 + (1 / 2) * (Real.sqrt d / 8)) :=
          mul_le_mul_of_nonneg_left h5 hρ.le
      _ = ρ * u0 (toCpx x) + ρ * (Real.sqrt d / 8) + (ρ / 2) * (Real.sqrt d / 8) := by ring
  have h4 : (ρ / 2) * (imNorm w - 1) ≤ (ρ / 2) * (Real.sqrt d / 8) := by
    have h := imNorm_sub_one_le w
    calc (ρ / 2) * (imNorm w - 1) ≤ (ρ / 2) * ‖imVec w‖ :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ (ρ / 2) * (Real.sqrt d / 8) := mul_le_mul_of_nonneg_left him (by positivity)
  rw [section5Phi, Bsmall2]
  linarith [h1, h2, h3, h4]

end Submission.FUP

namespace Submission.FUP

/-- The polydisc radius used for the mean value estimates: `1/(8√d)`, so that the `ℓ²` norm of
the imaginary part grows by at most `1/8` on the polydisc. -/
noncomputable def rr (d : ℕ) : ℝ := 1 / (8 * Real.sqrt d)

lemma rr_pos {d : ℕ} (hd : 1 ≤ d) : 0 < rr d := by
  rw [rr]; positivity

lemma sqrt_mul_rr {d : ℕ} (hd : 1 ≤ d) : Real.sqrt d * rr d = 1 / 8 := by
  rw [rr]
  have h : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Estimate (i) away from the origin.**  For `|z| ≥ 1/4` the mean value inequality on the
polydisc of radius `1/(8√d)` bounds `F` by the weighted `L²` norm times `e^{4ρ|Im z|}`. -/
lemma norm_F_sq_le_ge_quarter (hd : 1 ≤ d) {ρ lam B1 B2 KF : ℝ} (hρ : 0 < ρ)
    (hlam : 0 < lam)
    {u u0 : ℂᵈ → ℝ} {F : ℂᵈ → ℂ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hu0le : ∀ x : ℝᵈ, u0 (toCpx x) ≤ lam * omega0 x)
    (habs1 : ∀ t : ℝ, 0 ≤ t → 20 * (d : ℝ) * Real.log (1 + t) ≤ (ρ / 2) * t + B1)
    (habs2 : ∀ t : ℝ, 0 ≤ t → 20 * (d : ℝ) * Real.log (1 + t)
      - ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2)) ≤ B2)
    (hFana : AnalyticOnNhd ℂ F Set.univ)
    (hMF : ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal KF)
    (hKF : 0 < KF)
    {z : ℂᵈ} (hz : 1 / 4 ≤ ‖z‖) :
    ‖F z‖ ^ 2 ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
      * Real.exp (4 * ρ * ‖imVec z‖ + ρ / 2 + (B1 + B2)) := by
  have hrp : (0:ℝ) < rr d := rr_pos hd
  have hsub : Metric.closedBall z (rr d) ⊆ U5 (d := d) := by
    intro w hw
    rw [mem_U5]
    have h2 : ‖w - z‖ ≤ rr d := by
      have h1 : dist w z ≤ rr d := by simpa [Metric.mem_closedBall] using hw
      simpa [dist_eq_norm] using h1
    have h3 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have h5 := norm_le_add_norm_add' z w
      rw [norm_sub_rev] at h5
      exact h5
    have h4 : rr d ≤ 1 / 8 := by
      rw [rr, div_le_iff₀ (by positivity : (0:ℝ) < 8 * Real.sqrt d)]
      have hs : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
      linarith
    linarith
  have hB : ∀ w ∈ Metric.closedBall z (rr d),
      section5Phi ρ u u0 w ≤ 4 * ρ * (‖imVec z‖ + 1 / 8) + (B1 + B2) := by
    intro w hw
    have h := section5Phi_le (d := d) hρ hlam habs1 habs2 hunonpos hugrowth hu0growth hu0le w
    have h2 : ‖w - z‖ ≤ rr d := by
      have h1 : dist w z ≤ rr d := by simpa [Metric.mem_closedBall] using hw
      simpa [dist_eq_norm] using h1
    have h3 : ‖imVec w - imVec z‖ ≤ 1 / 8 := by
      have h4 : imVec w - imVec z = imVec (w - z) := by rw [imVec_sub]
      rw [h4]
      have h5 := norm_imVec_le (w - z)
      have h6 : Real.sqrt (d:ℝ) * ‖w - z‖ ≤ 1 / 8 := by
        rw [← sqrt_mul_rr hd]
        exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      linarith
    have h4 : ‖imVec w‖ ≤ ‖imVec z‖ + 1 / 8 := by
      have h5 : imVec w = imVec z + (imVec w - imVec z) := by abel
      have h6 : ‖imVec w‖ ≤ ‖imVec z‖ + ‖imVec w - imVec z‖ := by
        have h7 : ‖imVec w‖ = ‖imVec z + (imVec w - imVec z)‖ := by
          congr 1
        rw [h7]
        exact norm_add_le _ _
      linarith
    have h7 : 4 * ρ * ‖imVec w‖ ≤ 4 * ρ * (‖imVec z‖ + 1 / 8) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith [h, h7]
  have hana : AnalyticOnNhd ℂ F (Metric.closedBall z (rr d)) := hFana.mono (Set.subset_univ _)
  have h1 := ofReal_norm_sq_le_of_analyticOnNhd (ρ := ρ) (u := u) (u0 := u0) (f := F)
    hrp hana hB
  have h2 : ∫⁻ w in Metric.closedBall z (rr d),
      ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))) ≤ ENNReal.ofReal KF :=
    le_trans (lintegral_mono_set hsub) hMF
  have h3 : ENNReal.ofReal (‖F z‖ ^ 2)
      ≤ ENNReal.ofReal (((Real.pi * rr d ^ 2) ^ d)⁻¹
          * Real.exp (4 * ρ * (‖imVec z‖ + 1 / 8) + (B1 + B2))) * ENNReal.ofReal KF :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal _ from bot_le))
  have h4 : ENNReal.ofReal (‖F z‖ ^ 2)
      ≤ ENNReal.ofReal ((((Real.pi * rr d ^ 2) ^ d)⁻¹
          * Real.exp (4 * ρ * (‖imVec z‖ + 1 / 8) + (B1 + B2))) * KF) := by
    refine le_trans h3 ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  have h5 : ‖F z‖ ^ 2 ≤ ((((Real.pi * rr d ^ 2) ^ d)⁻¹
      * Real.exp (4 * ρ * (‖imVec z‖ + 1 / 8) + (B1 + B2))) * KF) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4
  calc ‖F z‖ ^ 2 ≤ ((((Real.pi * rr d ^ 2) ^ d)⁻¹
        * Real.exp (4 * ρ * (‖imVec z‖ + 1 / 8) + (B1 + B2))) * KF) := h5
    _ = (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp (4 * ρ * ‖imVec z‖ + ρ / 2 + (B1 + B2)) := by
        rw [show 4 * ρ * (‖imVec z‖ + 1 / 8) + (B1 + B2)
          = 4 * ρ * ‖imVec z‖ + ρ / 2 + (B1 + B2) by ring]
        ring

end Submission.FUP

namespace Submission.FUP

/-- **Estimate (i) near the origin via `g`.** -/
lemma norm_g_sq_le_le_quarter {ρ CLip Kg : ℝ} (hρ : 0 < ρ) (hCLip : 0 ≤ CLip)
    (hKg : 0 < Kg)
    {u u0 : ℂᵈ → ℝ} {g : ℂᵈ → ℂ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0nonpos : ∀ x : ℝᵈ, u0 (toCpx x) ≤ 0)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hg_ana : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂᵈ) (1 / 2)))
    (hMg : ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal Kg)
    (hd : 1 ≤ d)
    {z : ℂᵈ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖g z‖ ^ 2 ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d)) * Kg := by
  have hrp : (0:ℝ) < rr d := rr_pos hd
  have hrr : rr d ≤ 1 / 8 := by
    rw [rr, div_le_iff₀ (by positivity : (0:ℝ) < 8 * Real.sqrt d)]
    have hs : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
    linarith
  have hsub : Metric.closedBall z (rr d) ⊆ Metric.ball (0 : ℂᵈ) (1 / 2) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : ‖w - z‖ ≤ rr d := by
      have h1 : dist w z ≤ rr d := by simpa [Metric.mem_closedBall] using hw
      simpa [dist_eq_norm] using h1
    have h3 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      have h5 := norm_le_add_norm_add' w z
      exact h5
    linarith
  have hB : ∀ w ∈ Metric.closedBall z (rr d), section5Phi ρ u u0 w ≤ Bsmall ρ CLip d :=
    fun w hw => section5Phi_le_small (d := d) hρ hCLip hunonpos hugrowth hu0nonpos hu0growth hz w
      (Metric.closedBall_subset_closedBall hrr hw)
  have hana : AnalyticOnNhd ℂ g (Metric.closedBall z (rr d)) := hg_ana.mono hsub
  have h1 := ofReal_norm_sq_le_of_analyticOnNhd (ρ := ρ) (u := u) (u0 := u0) (f := g)
    hrp hana hB
  have h2 : ∫⁻ w in Metric.closedBall z (rr d),
      ENNReal.ofReal (‖g w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))) ≤ ENNReal.ofReal Kg := by
    refine le_trans (lintegral_mono_set (Set.subset_univ _)) ?_
    simpa using hMg
  have h3 : ENNReal.ofReal (‖g z‖ ^ 2)
      ≤ ENNReal.ofReal (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d))
        * ENNReal.ofReal Kg :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal _ from bot_le))
  have h4 : ENNReal.ofReal (‖g z‖ ^ 2)
      ≤ ENNReal.ofReal ((((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d)) * Kg) := by
    refine le_trans h3 ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4

end Submission.FUP

namespace Submission.FUP

/-- The exponent constants of the small-`x` estimate. -/
noncomputable def Cc (ρ : ℝ) (d : ℕ) : ℝ := (9 / 2) * ρ * Real.sqrt d

/-- The multiplicative constant of the small-`x` estimate. -/
noncomputable def Kc (ρ : ℝ) (d : ℕ) (Kg : ℝ) : ℝ :=
  (4 * (d : ℝ) / Real.pi) ^ d * Real.exp (10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4)) * Kg

lemma norm_toCpx_apply (x : ℝᵈ) (j : Fin d) : ‖toCpx x j‖ = |x.ofLp j| := by
  have h4 : toCpx x j = ((x.ofLp j : ℝ) : ℂ) := rfl
  rw [h4]
  have h5 : ‖(((x.ofLp j : ℝ)) : ℂ)‖ ^ 2 = (x.ofLp j) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  nlinarith [norm_nonneg (((x.ofLp j : ℝ)) : ℂ), abs_nonneg (x.ofLp j), sq_abs (x.ofLp j)]

lemma norm_toCpx_le (x : ℝᵈ) : ‖toCpx x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun j => ?_
  rw [norm_toCpx_apply]
  have h2 : (x.ofLp j) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun i => ‖x.ofLp i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    rw [Real.norm_eq_abs, sq_abs]
  have h3 : |x.ofLp j| ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_abs (x.ofLp j), h2]
  nlinarith [abs_nonneg (x.ofLp j), norm_nonneg x]

lemma norm_toCpx_ge (x : ℝᵈ) : ‖x‖ ≤ Real.sqrt d * ‖toCpx x‖ := by
  have h1 : ‖x‖ ^ 2 ≤ (d : ℝ) * ‖toCpx x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, ‖toCpx x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have h : ‖x.ofLp i‖ ≤ ‖toCpx x‖ := by
              have h' := norm_le_pi_norm (toCpx x) i
              rwa [norm_toCpx_apply] at h'
            exact pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = (d : ℝ) * ‖toCpx x‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt ((d : ℝ) * ‖toCpx x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt d * ‖toCpx x‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg _)]

/-- **Estimate (ii)**: `g` is bounded by `C|x|^{9d}` near the origin, the estimate which makes
`F = h - g` non-vanishing close to `0`. -/
lemma norm_g_sq_le_pow {ρ CLip Kg : ℝ} (hρ : 0 < ρ) (hKg : 0 < Kg) (hd : 1 ≤ d)
    {u u0 : ℂᵈ → ℝ} {g : ℂᵈ → ℂ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0nonpos : ∀ x : ℝᵈ, u0 (toCpx x) ≤ 0)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hg_ana : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂᵈ) (1 / 2)))
    (hMg : ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal Kg)
    {x : ℝᵈ} (hx : 0 < ‖x‖) (hx1 : ‖x‖ ≤ 1 / 4) :
    ‖g (toCpx x)‖ ^ 2 ≤ Kc ρ d Kg * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖) := by
  have hs : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hs1 : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  set r : ℝ := ‖x‖ / (2 * Real.sqrt d) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrs : r ≤ ‖x‖ / 2 := by
    rw [hr]
    refine div_le_div_of_nonneg_left (norm_nonneg x) (by norm_num) ?_
    linarith
  have hrle : r ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_right hx1 (by norm_num : (0:ℝ) ≤ 1 / 2)
    linarith [hrs]
  have hsub : Metric.closedBall (toCpx x) r ⊆ Metric.ball (0 : ℂᵈ) (1 / 2) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : dist w (toCpx x) ≤ r := by simpa [Metric.mem_closedBall] using hw
    have h2 : ‖w - toCpx x‖ ≤ r := by simpa [dist_eq_norm] using h1
    have h3 : ‖w‖ ≤ ‖toCpx x‖ + ‖w - toCpx x‖ := norm_le_add_norm_add' w (toCpx x)
    have h4 : ‖toCpx x‖ ≤ ‖x‖ := norm_toCpx_le x
    linarith
  have hB : ∀ w ∈ Metric.closedBall (toCpx x) r,
      section5Phi ρ u u0 w ≤ (9 / 2) * ρ * Real.sqrt d * ‖x‖
        + 20 * (d : ℝ) * Real.log ‖x‖ + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4) := by
    intro w hw
    have h1 : dist w (toCpx x) ≤ r := by simpa [Metric.mem_closedBall] using hw
    have h2 : ‖w - toCpx x‖ ≤ r := by simpa [dist_eq_norm] using h1
    have hW : ‖w‖ ≤ ‖x‖ + r := by
      have h3 : ‖w‖ ≤ ‖toCpx x‖ + ‖w - toCpx x‖ := norm_le_add_norm_add' w (toCpx x)
      have h4 : ‖toCpx x‖ ≤ ‖x‖ := norm_toCpx_le x
      linarith
    have hwgt : ‖w‖ ≥ ‖x‖ / (2 * Real.sqrt d) := by
      have h4 : ‖x‖ ≤ Real.sqrt d * ‖toCpx x‖ := norm_toCpx_ge x
      have h5 : ‖toCpx x‖ ≤ ‖w‖ + ‖w - toCpx x‖ := by
        have h6 := norm_le_add_norm_add' (toCpx x) w
        rw [norm_sub_rev] at h6
        exact h6
      have h6 : Real.sqrt d * r = ‖x‖ / 2 := by
        rw [hr]; field_simp
      have h7 : Real.sqrt d * ‖toCpx x‖ ≤ Real.sqrt d * (‖w‖ + r) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        linarith
      have h8 : ‖x‖ / 2 ≤ Real.sqrt d * ‖w‖ := by nlinarith [h4, h6, h7]
      show ‖x‖ / (2 * Real.sqrt d) ≤ ‖w‖
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt d)]
      nlinarith [h8, hs]
    have hsumpos : 0 < ∑ j, ‖w j‖ ^ 2 := by
      have h7 : (0:ℝ) < ‖w‖ := by
        have := div_pos hx (by positivity : (0:ℝ) < 2 * Real.sqrt d)
        linarith
      exact lt_of_lt_of_le (pow_pos h7 2) (sum_sq_ge_norm_sq w)
    have hsumle : ∑ j, ‖w j‖ ^ 2 ≤ (d : ℝ) * (9 / 4) * ‖x‖ ^ 2 := by
      calc ∑ j : Fin d, ‖w j‖ ^ 2 ≤ ∑ _j : Fin d, (3 * ‖x‖ / 2) ^ 2 :=
            Finset.sum_le_sum fun j _ => by
              have h5 : ‖w j‖ ≤ ‖w‖ := norm_le_pi_norm w j
              have h8 : ‖w‖ ≤ 3 * ‖x‖ / 2 := by linarith
              nlinarith [norm_nonneg (w j)]
        _ = (d : ℝ) * (3 * ‖x‖ / 2) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (d : ℝ) * (9 / 4) * ‖x‖ ^ 2 := by ring
    have hlog : logWeight w ≤ 20 * (d : ℝ) * Real.log ‖x‖
        + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4) := by
      rw [logWeight]
      have h6 : Real.log (∑ j, ‖w j‖ ^ 2) ≤ Real.log ((9 * (d:ℝ) / 4) * ‖x‖ ^ 2) :=
        Real.log_le_log hsumpos (by nlinarith [hsumle])
      have h7 : Real.log ((9 * (d:ℝ) / 4) * ‖x‖ ^ 2)
          = Real.log (9 * (d:ℝ) / 4) + 2 * Real.log ‖x‖ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring
      rw [h7] at h6
      nlinarith [h6]
    have hIm : ‖imVec w‖ ≤ Real.sqrt d * (3 * ‖x‖ / 2) := by
      calc ‖imVec w‖ ≤ Real.sqrt (d:ℝ) * ‖w‖ := norm_imVec_le w
        _ ≤ Real.sqrt (d:ℝ) * (3 * ‖x‖ / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            linarith
    have h2u : 2 * u w ≤ 2 * ρ * (Real.sqrt d * (3 * ‖x‖ / 2)) := by
      have h := (hugrowth w).2
      have h9 : u (toCpx (reVec w)) ≤ 0 := hunonpos (reVec w)
      have h10 : ρ * ‖imVec w‖ ≤ ρ * (Real.sqrt d * (3 * ‖x‖ / 2)) :=
        mul_le_mul_of_nonneg_left hIm hρ.le
      linarith
    have h2u0 : ρ * u0 w ≤ (ρ / 2) * (Real.sqrt d * (3 * ‖x‖ / 2)) := by
      have h := (hu0growth w).2
      have h9 : u0 (toCpx (reVec w)) ≤ 0 := hu0nonpos (reVec w)
      have h10 : (1 / 2) * ‖imVec w‖ ≤ (1 / 2) * (Real.sqrt d * (3 * ‖x‖ / 2)) :=
        mul_le_mul_of_nonneg_left hIm (by norm_num)
      calc ρ * u0 w ≤ ρ * ((1 / 2) * (Real.sqrt d * (3 * ‖x‖ / 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ hρ.le
            linarith
        _ = (ρ / 2) * (Real.sqrt d * (3 * ‖x‖ / 2)) := by ring
    have h2i : (ρ / 2) * (imNorm w - 1) ≤ (ρ / 2) * (Real.sqrt d * (3 * ‖x‖ / 2)) := by
      have h := imNorm_sub_one_le w
      calc (ρ / 2) * (imNorm w - 1) ≤ (ρ / 2) * ‖imVec w‖ :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ ≤ (ρ / 2) * (Real.sqrt d * (3 * ‖x‖ / 2)) :=
            mul_le_mul_of_nonneg_left hIm (by positivity)
    rw [section5Phi]
    linarith [h2u, h2u0, h2i, hlog]
  have hana : AnalyticOnNhd ℂ g (Metric.closedBall (toCpx x) r) := hg_ana.mono hsub
  have h1 := ofReal_norm_sq_le_of_analyticOnNhd (ρ := ρ) (u := u) (u0 := u0) (f := g)
    hrpos hana hB
  have h2 : ∫⁻ w in Metric.closedBall (toCpx x) r,
      ENNReal.ofReal (‖g w‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 w))) ≤ ENNReal.ofReal Kg := by
    refine le_trans (lintegral_mono_set (Set.subset_univ _)) ?_
    simpa using hMg
  have h3 : ENNReal.ofReal (‖g (toCpx x)‖ ^ 2)
      ≤ ENNReal.ofReal (((Real.pi * r ^ 2) ^ d)⁻¹
        * Real.exp ((9 / 2) * ρ * Real.sqrt d * ‖x‖ + 20 * (d : ℝ) * Real.log ‖x‖
          + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4))) * ENNReal.ofReal Kg :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal _ from bot_le))
  have h4 : ENNReal.ofReal (‖g (toCpx x)‖ ^ 2)
      ≤ ENNReal.ofReal ((((Real.pi * r ^ 2) ^ d)⁻¹
        * Real.exp ((9 / 2) * ρ * Real.sqrt d * ‖x‖ + 20 * (d : ℝ) * Real.log ‖x‖
          + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4))) * Kg) := by
    refine le_trans h3 ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  have h5 : ‖g (toCpx x)‖ ^ 2 ≤ ((((Real.pi * r ^ 2) ^ d)⁻¹
      * Real.exp ((9 / 2) * ρ * Real.sqrt d * ‖x‖ + 20 * (d : ℝ) * Real.log ‖x‖
        + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4))) * Kg) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4
  have hA : (Real.pi * r ^ 2) ^ d = (Real.pi / (4 * (d : ℝ))) ^ d * (‖x‖ ^ 2) ^ d := by
    rw [hr]
    have h : Real.pi * (‖x‖ / (2 * Real.sqrt d)) ^ 2
        = (Real.pi / (4 * (d : ℝ))) * ‖x‖ ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    rw [h, mul_pow]
  have hBb : Real.exp ((9 / 2) * ρ * Real.sqrt d * ‖x‖ + 20 * (d : ℝ) * Real.log ‖x‖
        + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4))
      = Real.exp (Cc ρ d * ‖x‖) * Real.exp (20 * (d : ℝ) * Real.log ‖x‖)
        * Real.exp (10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4)) := by
    rw [Cc, Real.exp_add, Real.exp_add]
  have hCc : Real.exp (20 * (d : ℝ) * Real.log ‖x‖) = ‖x‖ ^ (20 * d) := by
    rw [show 20 * (d : ℝ) * Real.log ‖x‖ = ((20 * d : ℕ) : ℝ) * Real.log ‖x‖ by push_cast; ring]
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have hDd : ((Real.pi / (4 * (d : ℝ))) ^ d)⁻¹ = (4 * (d : ℝ) / Real.pi) ^ d := by
    rw [← inv_pow, inv_div]
  have hEe : ((‖x‖ ^ 2) ^ d)⁻¹ * ‖x‖ ^ (20 * d) = ‖x‖ ^ (18 * d) := by
    rw [show (‖x‖ ^ 2) ^ d = ‖x‖ ^ (2 * d) by rw [pow_mul]]
    rw [mul_comm, ← pow_sub₀ ‖x‖ (ne_of_gt hx) (by omega),
      show 20 * d - 2 * d = 18 * d by omega]
  calc ‖g (toCpx x)‖ ^ 2 ≤ (((Real.pi * r ^ 2) ^ d)⁻¹
        * Real.exp ((9 / 2) * ρ * Real.sqrt d * ‖x‖ + 20 * (d : ℝ) * Real.log ‖x‖
          + 10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4))) * Kg := h5
    _ = (4 * (d : ℝ) / Real.pi) ^ d
          * Real.exp (10 * (d : ℝ) * Real.log (9 * (d : ℝ) / 4)) * Kg
          * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖) := by
        rw [hA, hBb, hCc, mul_inv, hDd, ← hEe]
        ring
    _ = Kc ρ d Kg * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖) := by
        rw [Kc]

end Submission.FUP
