import Mathlib
import Submission.Work.FIArea2.R6.GenRegion
import Submission.Work.FIArea2.lemma_7_1_volume

set_option autoImplicit false

namespace Work.FIArea2.R6

open MeasureTheory
open scoped Topology

noncomputable section

/-! ## The volume of the general square annulus `bigS`

`Work.FIArea2.bigS N C = {p | |p₁² − p₂²| ≤ 2√N ∧ p₁² + p₂² ≤ C}` is the "square annulus"
containing the level region `{0 ≤ g ≤ 4N}` of the biquadratic form.  This is the volume bound
underlying `Work.FIArea2.lemma_7_1_volume`, extracted here for a general `N ≥ 1` and the critical
radius `C = 4√N/√(1−γ²)`.
-/

/-- **Volume of the square annulus at the critical radius.**  For `N ≥ 1`, `0 ≤ γ < 1`,
`volume (bigS N (4√N/√(1−γ²))) ≤ 30 √N log(2 + 1/(1−γ²))`. -/
theorem vol_bigS_le (N γ : ℝ) (hN : 1 ≤ N) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    volume (Work.FIArea2.bigS N (4 * Real.sqrt N / Real.sqrt (1 - γ ^ 2)))
      ≤ ENNReal.ofReal (30 * Real.sqrt N * Real.log (2 + 1 / (1 - γ ^ 2))) := by
  set C : ℝ := 4 * Real.sqrt N / Real.sqrt (1 - γ ^ 2) with hC_def
  have hC0 : 0 ≤ C := by
    rw [hC_def]
    exact div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hkey : ∫ u, Work.FIArea2.volBound N C u
      ≤ 30 * Real.sqrt N * Real.log (2 + 1 / (1 - γ ^ 2)) := by
    have hlog : Real.log (Work.FIArea2.volT N C / Work.FIArea2.volS N C)
        ≤ (1 / 4) * Real.log (1 / (1 - γ ^ 2)) := by
      rw [hC_def]
      exact Work.FIArea2.log_volT_div_volS_le N γ hN hγ0 hγ1
    have hInt := Work.FIArea2.integral_volBound_le N C hN hC0
    have hArith := Work.FIArea2.log_volume_arithmetic N γ hN hγ0 hγ1
    have hmul : 8 * Real.sqrt 2 * Real.sqrt N
          * Real.log (Work.FIArea2.volT N C / Work.FIArea2.volS N C)
        ≤ 2 * Real.sqrt 2 * Real.sqrt N * Real.log (1 / (1 - γ ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hlog
        (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt 2 * Real.sqrt N)
      calc 8 * Real.sqrt 2 * Real.sqrt N
            * Real.log (Work.FIArea2.volT N C / Work.FIArea2.volS N C)
          ≤ 8 * Real.sqrt 2 * Real.sqrt N * ((1 / 4) * Real.log (1 / (1 - γ ^ 2))) := h
        _ = 2 * Real.sqrt 2 * Real.sqrt N * Real.log (1 / (1 - γ ^ 2)) := by ring
    linarith
  calc volume (Work.FIArea2.bigS N C)
      ≤ ∫⁻ u, ENNReal.ofReal (Work.FIArea2.volBound N C u) := by
        rw [Work.FIArea2.volume_bigS_eq N C]
        exact lintegral_mono (fun u => Work.FIArea2.sec_volume_le N C u hN hC0)
    _ = ENNReal.ofReal (∫ u, Work.FIArea2.volBound N C u) :=
        (ofReal_integral_eq_lintegral_ofReal (Work.FIArea2.integrable_volBound N C hN hC0)
          (Filter.Eventually.of_forall (fun u => Work.FIArea2.volBound_nonneg N C u))).symm
    _ ≤ ENNReal.ofReal (30 * Real.sqrt N * Real.log (2 + 1 / (1 - γ ^ 2))) :=
        ENNReal.ofReal_le_ofReal hkey

/-! ## The geometric reduction

For `0 < A ≤ B ≤ 64M` and `1 ≤ M`, `0 ≤ γ < 1`, every point of the general region
`A ≤ g(t₁,t₂) ≤ B` satisfies `|t₁² − t₂²| ≤ 8√M` and `t₁² + t₂² ≤ 16√M/√(1−γ²)`, i.e. lies in
the square annulus `bigS (16M) (4√(16M)/√(1−γ²))`.
-/

/-- The general region is contained in the square annulus with parameter `16M`. -/
theorem regG_subset_bigS (M γ A B : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hA : 0 < A) (hAB : A ≤ B) (hB : B ≤ 64 * M) :
    regG A B γ ⊆ Work.FIArea2.bigS (16 * M) (4 * Real.sqrt (16 * M) / Real.sqrt (1 - γ ^ 2)) := by
  intro p hp
  obtain ⟨-, hhi⟩ := hp
  simp only [Work.FIArea2.gq] at hhi
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ :=
    Work.FIArea2.biquadratic_ellipse_bounds γ M p.1 p.2 hγ0 hγ1 hMpos
  have h1γ2 : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  have h16 : Real.sqrt (16 * M) = 4 * Real.sqrt M := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  constructor
  · -- `|p₁² − p₂²| ≤ 8√M = 2√(16M)`
    have hsq : (p.1 ^ 2 - p.2 ^ 2) ^ 2 ≤ 64 * M := by
      have h := le_trans hc2 hhi
      linarith
    have h8 : (8 * Real.sqrt M) ^ 2 = 64 * M := by
      rw [mul_pow, Real.sq_sqrt hMpos.le]; ring
    have habs : |p.1 ^ 2 - p.2 ^ 2| ≤ 8 * Real.sqrt M := by
      have h8nn : (0 : ℝ) ≤ 8 * Real.sqrt M := by positivity
      have hsq' : (p.1 ^ 2 - p.2 ^ 2) ^ 2 ≤ (8 * Real.sqrt M) ^ 2 := by
        rw [h8]; exact hsq
      calc |p.1 ^ 2 - p.2 ^ 2| = Real.sqrt ((p.1 ^ 2 - p.2 ^ 2) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((8 * Real.sqrt M) ^ 2) := Real.sqrt_le_sqrt hsq'
        _ = 8 * Real.sqrt M := Real.sqrt_sq h8nn
    rw [h16]
    linarith [habs]
  · -- `p₁² + p₂² ≤ 16√M/√(1−γ²) = 4√(16M)/√(1−γ²)`
    have h128 : (1 - γ ^ 2) * (p.1 ^ 4 + p.2 ^ 4) ≤ 128 * M := by
      have h2 : 2 * (p.1 ^ 4 - 2 * γ * p.1 ^ 2 * p.2 ^ 2 + p.2 ^ 4) ≤ 2 * B := by linarith
      linarith [hc1, h2, hB]
    have hAB2 : (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤ 2 * (p.1 ^ 4 + p.2 ^ 4) := by
      nlinarith [sq_nonneg (p.1 ^ 2 - p.2 ^ 2)]
    have hbig : (1 - γ ^ 2) * (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤ 256 * M := by
      have h := mul_le_mul_of_nonneg_left hAB2 h1γ2.le
      nlinarith [h, h128]
    have hsq : (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤ (16 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) ^ 2 := by
      have h1 : (p.1 ^ 2 + p.2 ^ 2) ^ 2 ≤ 256 * M / (1 - γ ^ 2) := by
        rw [le_div_iff₀ h1γ2]
        nlinarith [hbig]
      have h2 : (16 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) ^ 2 = 256 * M / (1 - γ ^ 2) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hMpos.le, Real.sq_sqrt h1γ2.le]
        norm_num
      rwa [h2]
    have hfin : p.1 ^ 2 + p.2 ^ 2 ≤ 16 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by
      have h := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ p.1 ^ 2 + p.2 ^ 2),
        abs_of_nonneg (div_nonneg (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt M)
          (Real.sqrt_nonneg _))] at h
    have hCeq : 4 * Real.sqrt (16 * M) / Real.sqrt (1 - γ ^ 2)
        = 16 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by
      rw [h16]; ring
    rw [hCeq]
    exact hfin

/-! ## The main volume bound for `regG` -/

theorem vol_regG_le (M γ A B : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hA : 0 < A) (hAB : A ≤ B) (hB : B ≤ 64 * M) :
    MeasureTheory.volume (Work.FIArea2.R6.regG A B γ)
      ≤ ENNReal.ofReal (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
  have hsub : regG A B γ ⊆
      Work.FIArea2.bigS (16 * M) (4 * Real.sqrt (16 * M) / Real.sqrt (1 - γ ^ 2)) :=
    regG_subset_bigS M γ A B hM hγ0 hγ1 hA hAB hB
  have h1 : volume (regG A B γ) ≤
      volume (Work.FIArea2.bigS (16 * M) (4 * Real.sqrt (16 * M) / Real.sqrt (1 - γ ^ 2))) :=
    measure_mono hsub
  have h2 : volume (Work.FIArea2.bigS (16 * M) (4 * Real.sqrt (16 * M) / Real.sqrt (1 - γ ^ 2)))
      ≤ ENNReal.ofReal (30 * Real.sqrt (16 * M) * Real.log (2 + 1 / (1 - γ ^ 2))) :=
    vol_bigS_le (16 * M) γ (by linarith) hγ0 hγ1
  have h3 : ENNReal.ofReal (30 * Real.sqrt (16 * M) * Real.log (2 + 1 / (1 - γ ^ 2)))
      ≤ ENNReal.ofReal (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
    apply ENNReal.ofReal_le_ofReal
    have h16 : Real.sqrt (16 * M) = 4 * Real.sqrt M := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num
    have hlog : 0 ≤ Real.log (2 + 1 / (1 - γ ^ 2)) := by
      apply Real.log_nonneg
      have h := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
      have h2 : 0 < 1 / (1 - γ ^ 2) := div_pos one_pos h
      linarith
    have hsqrtM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
    rw [h16]
    have hle : 30 * (4 * Real.sqrt M) ≤ 2000 * Real.sqrt M := by linarith
    exact mul_le_mul_of_nonneg_right hle hlog
  exact le_trans h1 (le_trans h2 h3)

end

end Work.FIArea2.R6
