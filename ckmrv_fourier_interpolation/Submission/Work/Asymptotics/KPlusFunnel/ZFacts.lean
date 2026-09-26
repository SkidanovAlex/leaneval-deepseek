/-
# The remaining `z`-cusp estimates at the threshold `Im z ≥ 1/3`

This file supplies the two `z`-estimates that are not covered by
`ZAtomsThird.first_order` and `ZAtomsThird.cusp_forms`:

* `delta_lower_third`  : `‖Δ(z)‖ ≥ c ‖q(z)‖` for `Im z ≥ 1/3` (from the product formula
  `Δ = q ∏ (1 - q^{n+1})^24` and an explicit lower bound for the finite products);
* `jz_sigma_third`     : `j(z)(E₄ - E₂²)(z) = 288 + O(q(z))` for `Im z ≥ 1/3`, which is the
  cancellation of the `1/q` growth of `j` against the vanishing of the cusp form
  `E₄ - E₂²` at the cusp.
-/
import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop

namespace Work.Asymptotics

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

open Work.Kernels

/-- On `{Im z ≥ 1/3}` the `q`-parameter is at most `exp (-(2 π / 3))`. -/
lemma norm_qParam_le_exp_third {z : ℍ} (hz : 1 / 3 ≤ z.im) :
    ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi / 3)) := by
  rw [norm_qParamFun, Real.exp_le_exp]
  nlinarith [Real.pi_pos, hz]

/-- On `{Im z ≥ 1/3}` the `q`-parameter is at most `1/3`. -/
lemma norm_qParam_le_third {z : ℍ} (hz : 1 / 3 ≤ z.im) : ‖qParamFun z‖ ≤ 1 / 3 := by
  have h3 : (3 : ℝ) ≤ Real.exp (2 * Real.pi / 3) := by
    have h2 : (2 : ℝ) ≤ 2 * Real.pi / 3 := by nlinarith [Real.pi_gt_three]
    have h4 := Real.exp_le_exp.mpr h2
    have h5 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    linarith
  calc ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi / 3)) := norm_qParam_le_exp_third hz
    _ = (Real.exp (2 * Real.pi / 3))⁻¹ := by rw [Real.exp_neg]
    _ ≤ (3 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr h3
    _ = 1 / 3 := by norm_num

/-! ## A lower bound for `Δ` on `{Im z ≥ 1/3}` -/

/-- The `24`-th power of the finite product `∏_{n<N}(1 - ‖q‖^{n+1})` is at least `(1/2)^24`
when `‖q‖ ≤ 1/3`. -/
lemma half_le_prod_range (q : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 1 / 3) (N : ℕ) :
    (1 / 2) ^ 24 ≤ ∏ i ∈ Finset.range N, (1 - q ^ (i + 1)) ^ 24 := by
  have hq1 : q < 1 := by linarith
  have h01 : q ≤ 1 := by linarith
  have hsumm : Summable (fun i : ℕ => q ^ (i + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  have htsum : ∑' i : ℕ, q ^ (i + 1) = q / (1 - q) := by
    have h1 : (fun i : ℕ => q ^ (i + 1)) = fun i : ℕ => q * q ^ i := by
      funext i; rw [pow_succ]; ring
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
  have hpartial : ∑ i ∈ Finset.range N, q ^ (i + 1) ≤ q / (1 - q) := by
    rw [← htsum]
    exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hq0 _) hsumm
  have hle : q / (1 - q) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hfs := one_sub_sum_le_prod_one_sub (Finset.range N) (fun i => q ^ (i + 1))
    (fun i _ => pow_nonneg hq0 _) (fun i _ => pow_le_one₀ hq0 h01)
  have h1 : (1 / 2 : ℝ) ≤ ∏ i ∈ Finset.range N, (1 - q ^ (i + 1)) := by linarith
  calc (1 / 2) ^ 24 ≤ (∏ i ∈ Finset.range N, (1 - q ^ (i + 1))) ^ 24 :=
        pow_le_pow_left₀ (by norm_num) h1 24
    _ = ∏ i ∈ Finset.range N, (1 - q ^ (i + 1)) ^ 24 := (Finset.prod_pow _ _ _).symm

/-- `(1/2)^24 ≤ ‖∏' n (1 - q(z)^{n+1})^24‖` for `Im z ≥ 1/3`. -/
lemma tprod_half_le (z : ℍ) (hz : 1 / 3 ≤ z.im) :
    (1 / 2) ^ 24 ≤ ‖∏' n : ℕ, (1 - (qParamFun z) ^ (n + 1)) ^ 24‖ := by
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq3 : ‖qParamFun z‖ ≤ 1 / 3 := norm_qParam_le_third hz
  have hq1z : ‖qParamFun z‖ ≤ 1 := le_trans hq3 (by norm_num)
  have hq1 : ‖qParamFun z‖ < 1 := lt_of_le_of_lt hq3 (by norm_num)
  have hmul : Multipliable (fun n : ℕ => 1 - (qParamFun z) ^ (n + 1)) :=
    ModularForm.multipliable_one_sub_pow hq1
  have hmul24 : Multipliable (fun n : ℕ => (1 - (qParamFun z) ^ (n + 1)) ^ 24) :=
    hmul.pow 24
  have htend : Filter.Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N,
      (1 - (qParamFun z) ^ (i + 1)) ^ 24) atTop
      (𝓝 (∏' n : ℕ, (1 - (qParamFun z) ^ (n + 1)) ^ 24)) :=
    hmul24.hasProd.tendsto_prod_nat
  have hnorm := htend.norm
  refine ge_of_tendsto hnorm (Eventually.of_forall fun N => ?_)
  calc (1 / 2 : ℝ) ^ 24 ≤ ∏ i ∈ Finset.range N, (1 - ‖qParamFun z‖ ^ (i + 1)) ^ 24 :=
        half_le_prod_range _ hq0 hq3 N
    _ ≤ ∏ i ∈ Finset.range N, ‖(1 - (qParamFun z) ^ (i + 1)) ^ 24‖ := by
        apply Finset.prod_le_prod₀
        · intro i _
          have hle1 : ‖qParamFun z‖ ^ (i + 1) ≤ 1 := pow_le_one₀ hq0 hq1z
          exact pow_nonneg (by linarith) 24
        · intro i _
          have hle1 : ‖qParamFun z‖ ^ (i + 1) ≤ 1 := pow_le_one₀ hq0 hq1z
          rw [norm_pow]
          apply pow_le_pow_left₀ (by linarith)
          calc (1 : ℝ) - ‖qParamFun z‖ ^ (i + 1)
              = 1 - ‖(qParamFun z) ^ (i + 1)‖ := by rw [norm_pow]
            _ ≤ ‖(1 : ℂ) - (qParamFun z) ^ (i + 1)‖ := by
                simpa using norm_sub_norm_le (1 : ℂ) ((qParamFun z) ^ (i + 1))
    _ = ‖∏ i ∈ Finset.range N, (1 - (qParamFun z) ^ (i + 1)) ^ 24‖ := (norm_prod _ _).symm

/-- `‖Δ(z)‖ ≥ (1/2)^24 ‖q(z)‖` for `Im z ≥ 1/3`. -/
theorem delta_lower_third :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → c * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ := by
  refine ⟨(1 / 2) ^ 24, by norm_num, fun z hz => ?_⟩
  have hfac : DeltaFun z = qParamFun z
      * ∏' n : ℕ, (1 - (qParamFun z) ^ (n + 1)) ^ 24 := by
    rw [show DeltaFun z = ModularForm.discriminant z from rfl, ModularForm.discriminant_eq_q_prod,
      qParamFun_eq_qParam]
  rw [hfac, norm_mul]
  calc (1 / 2) ^ 24 * ‖qParamFun z‖
      ≤ (1 / 2) ^ 24 * ‖qParamFun z‖ := le_rfl
    _ ≤ ‖∏' n : ℕ, (1 - (qParamFun z) ^ (n + 1)) ^ 24‖ * ‖qParamFun z‖ := by
        apply mul_le_mul_of_nonneg_right (tprod_half_le z hz) (norm_nonneg _)
    _ = ‖qParamFun z‖ * ‖∏' n : ℕ, (1 - (qParamFun z) ^ (n + 1)) ^ 24‖ := by ring

/-- `‖Δ(z)‖ ≤ C ‖q(z)‖` for `Im z ≥ 1/3`. -/
theorem delta_upper_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖DeltaFun z‖ ≤ C * ‖qParamFun z‖ := by
  obtain ⟨C, hC, h⟩ := ZAtomsThird.DeltaFun_two_term_third
  refine ⟨1 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have hq1 : ‖qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
  have hsplit : DeltaFun z = (DeltaFun z - qParamFun z) + qParamFun z := by ring
  rw [hsplit]
  calc ‖(DeltaFun z - qParamFun z) + qParamFun z‖
      ≤ ‖DeltaFun z - qParamFun z‖ + ‖qParamFun z‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ ^ 2 + ‖qParamFun z‖ := by linarith
    _ ≤ (1 + C) * ‖qParamFun z‖ := by
        have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by
          nlinarith [norm_nonneg (qParamFun z), hq1]
        nlinarith [mul_le_mul_of_nonneg_left hq2 hC.le, norm_nonneg (qParamFun z)]

/-- `E₄(z) - E₂(z)² = 288 q(z) + O(q(z)²)` for `Im z ≥ 1/3`. -/
theorem sigma_sub_288q_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z‖ ≤ C * ‖qParamFun z‖ ^ 2 := by
  obtain ⟨C2, hC2, h2⟩ := ZAtomsThird.E2Fun_two_term_third
  obtain ⟨C4, hC4, h4⟩ := ZAtomsThird.E4Fun_two_term_third
  set K : ℝ := 576 + C4 + 2 * (1 + 24) * C2 + C2 ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨K + 1, by positivity, fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
  have hq4 : ‖qParamFun z‖ ^ 4 ≤ ‖qParamFun z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖qParamFun z‖ ^ 2 - 1), sq_nonneg (‖qParamFun z‖), hq1, hq0]
  have h2' := h2 z hz
  have h4' := h4 z hz
  have hsplit : E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z
      = -((576 : ℂ) * qParamFun z ^ 2) + (E4Fun z - 1 - 240 * qParamFun z)
        - 2 * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)
        - (E2Fun z - 1 + 24 * qParamFun z) ^ 2 := by ring
  have h1 : ‖(2 : ℂ) * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)‖
      ≤ 2 * (1 + 24) * C2 * ‖qParamFun z‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h1q : ‖(1 : ℂ) - 24 * qParamFun z‖ ≤ 1 + 24 * ‖qParamFun z‖ := by
      calc ‖(1 : ℂ) - 24 * qParamFun z‖
          ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * qParamFun z‖ := norm_sub_le _ _
        _ = 1 + 24 * ‖qParamFun z‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
    have hprod : ‖(1 : ℂ) - 24 * qParamFun z‖ * ‖E2Fun z - 1 + 24 * qParamFun z‖
        ≤ (1 + 24 * ‖qParamFun z‖) * (C2 * ‖qParamFun z‖ ^ 2) :=
      mul_le_mul h1q h2' (norm_nonneg _) (by positivity)
    have hle : (1 + 24 * ‖qParamFun z‖) * (C2 * ‖qParamFun z‖ ^ 2)
        ≤ (1 + 24) * (C2 * ‖qParamFun z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc (2 : ℝ) * ‖(1 : ℂ) - 24 * qParamFun z‖ * ‖E2Fun z - 1 + 24 * qParamFun z‖
        = 2 * (‖(1 : ℂ) - 24 * qParamFun z‖ * ‖E2Fun z - 1 + 24 * qParamFun z‖) := by ring
      _ ≤ 2 * ((1 + 24) * (C2 * ‖qParamFun z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (le_trans hprod hle) (by norm_num)
      _ = 2 * (1 + 24) * C2 * ‖qParamFun z‖ ^ 2 := by ring
  have h2sq : ‖(E2Fun z - 1 + 24 * qParamFun z) ^ 2‖ ≤ C2 ^ 2 * ‖qParamFun z‖ ^ 2 := by
    rw [norm_pow]
    calc (‖E2Fun z - 1 + 24 * qParamFun z‖) ^ 2 ≤ (C2 * ‖qParamFun z‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2' 2
      _ ≤ C2 ^ 2 * ‖qParamFun z‖ ^ 2 := by
          have hq1' : ‖qParamFun z‖ ^ 2 ≤ 1 := by nlinarith
          nlinarith [hC2.le, hq0, hq1', sq_nonneg ‖qParamFun z‖]
  rw [hsplit]
  have h576 : ‖(576 : ℂ) * qParamFun z ^ 2‖ = 576 * ‖qParamFun z‖ ^ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have hmain : ‖-((576 : ℂ) * qParamFun z ^ 2) + (E4Fun z - 1 - 240 * qParamFun z)
        - 2 * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)
        - (E2Fun z - 1 + 24 * qParamFun z) ^ 2‖
      ≤ ‖(576 : ℂ) * qParamFun z ^ 2‖ + ‖E4Fun z - 1 - 240 * qParamFun z‖
          + ‖(2 : ℂ) * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)‖
          + ‖(E2Fun z - 1 + 24 * qParamFun z) ^ 2‖ := by
    have s1 := norm_sub_le ((-((576 : ℂ) * qParamFun z ^ 2) + (E4Fun z - 1 - 240 * qParamFun z))
        - 2 * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z))
      ((E2Fun z - 1 + 24 * qParamFun z) ^ 2)
    have s2 := norm_sub_le (-((576 : ℂ) * qParamFun z ^ 2) + (E4Fun z - 1 - 240 * qParamFun z))
      (2 * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z))
    have s3 := norm_add_le (-((576 : ℂ) * qParamFun z ^ 2)) (E4Fun z - 1 - 240 * qParamFun z)
    rw [norm_neg] at s3
    linarith [s1, s2, s3, norm_nonneg ((576 : ℂ) * qParamFun z ^ 2),
      norm_nonneg (E4Fun z - 1 - 240 * qParamFun z),
      norm_nonneg ((2 : ℂ) * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)),
      norm_nonneg ((E2Fun z - 1 + 24 * qParamFun z) ^ 2)]
  calc ‖-((576 : ℂ) * qParamFun z ^ 2) + (E4Fun z - 1 - 240 * qParamFun z)
        - 2 * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)
        - (E2Fun z - 1 + 24 * qParamFun z) ^ 2‖
      ≤ ‖(576 : ℂ) * qParamFun z ^ 2‖ + ‖E4Fun z - 1 - 240 * qParamFun z‖
          + ‖(2 : ℂ) * (1 - 24 * qParamFun z) * (E2Fun z - 1 + 24 * qParamFun z)‖
          + ‖(E2Fun z - 1 + 24 * qParamFun z) ^ 2‖ := hmain
    _ ≤ (576 * ‖qParamFun z‖ ^ 2 + C4 * ‖qParamFun z‖ ^ 2
          + 2 * (1 + 24) * C2 * ‖qParamFun z‖ ^ 2) + C2 ^ 2 * ‖qParamFun z‖ ^ 2 := by
        rw [h576]
        linarith [h4', h1, h2sq]
    _ = K * ‖qParamFun z‖ ^ 2 := by rw [hK]; ring
    _ ≤ (K + 1) * ‖qParamFun z‖ ^ 2 := by
        nlinarith [pow_nonneg hq0 2, hK0]

/-- `E₄³ - 1 = O(q)` on `{Im z ≥ 1/3}`. -/
theorem E4cube_sub_one_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z ^ 3 - 1‖ ≤ C * ‖qParamFun z‖ := by
  obtain ⟨C4, hC4, h4⟩ := ZAtomsThird.E4Fun_two_term_third
  refine ⟨3 * (240 + C4) + 3 * (240 + C4) ^ 2 + (240 + C4) ^ 3, by positivity, fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
  have h4' := h4 z hz
  have hE4m1 : ‖E4Fun z - 1‖ ≤ (240 + C4) * ‖qParamFun z‖ := by
    have hsplit : E4Fun z - 1 = (E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z := by ring
    rw [hsplit]
    have h240 : ‖(240 : ℂ) * qParamFun z‖ = 240 * ‖qParamFun z‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    calc ‖(E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z‖
        ≤ ‖E4Fun z - 1 - 240 * qParamFun z‖ + ‖(240 : ℂ) * qParamFun z‖ := norm_add_le _ _
      _ ≤ C4 * ‖qParamFun z‖ ^ 2 + 240 * ‖qParamFun z‖ := by
          rw [h240]
          linarith [h4']
      _ ≤ (240 + C4) * ‖qParamFun z‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hq2 hC4.le, hq0]
  have hsplit : E4Fun z ^ 3 - 1
      = 3 * (E4Fun z - 1) + 3 * (E4Fun z - 1) ^ 2 + (E4Fun z - 1) ^ 3 := by ring
  have h2 : ‖(E4Fun z - 1) ^ 2‖ ≤ ((240 + C4) * ‖qParamFun z‖) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hE4m1 2
  have h3 : ‖(E4Fun z - 1) ^ 3‖ ≤ ((240 + C4) * ‖qParamFun z‖) ^ 3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hE4m1 3
  have hD : 0 ≤ (240 + C4) * ‖qParamFun z‖ := by positivity
  rw [hsplit]
  calc ‖3 * (E4Fun z - 1) + 3 * (E4Fun z - 1) ^ 2 + (E4Fun z - 1) ^ 3‖
      ≤ (‖(3 : ℂ) * (E4Fun z - 1)‖ + ‖(3 : ℂ) * (E4Fun z - 1) ^ 2‖)
        + ‖(E4Fun z - 1) ^ 3‖ := by
        have s1 := norm_add_le (3 * (E4Fun z - 1) + 3 * (E4Fun z - 1) ^ 2)
          ((E4Fun z - 1) ^ 3)
        have s2 := norm_add_le (3 * (E4Fun z - 1)) (3 * (E4Fun z - 1) ^ 2)
        linarith [s1, s2, norm_nonneg ((3 : ℂ) * (E4Fun z - 1)),
          norm_nonneg ((3 : ℂ) * (E4Fun z - 1) ^ 2), norm_nonneg ((E4Fun z - 1) ^ 3)]
    _ ≤ (3 * ((240 + C4) * ‖qParamFun z‖) + 3 * ((240 + C4) * ‖qParamFun z‖) ^ 2)
        + ((240 + C4) * ‖qParamFun z‖) ^ 3 := by
        have h31 : ‖(3 : ℂ) * (E4Fun z - 1)‖ ≤ 3 * ((240 + C4) * ‖qParamFun z‖) := by
          rw [norm_mul, Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left hE4m1 (by norm_num)
        have h32 : ‖(3 : ℂ) * (E4Fun z - 1) ^ 2‖ ≤ 3 * ((240 + C4) * ‖qParamFun z‖) ^ 2 := by
          rw [norm_mul, Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        linarith [h31, h32, h3]
    _ ≤ (3 * (240 + C4) + 3 * (240 + C4) ^ 2 + (240 + C4) ^ 3) * ‖qParamFun z‖ := by
        have h1 : ((240 + C4) * ‖qParamFun z‖) ^ 2 ≤ (240 + C4) ^ 2 * ‖qParamFun z‖ := by
          have h2' : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := hq2
          nlinarith [hq0, hq1, mul_nonneg (by positivity : (0:ℝ) ≤ (240 + C4) ^ 2) hq0,
            sq_nonneg (240 + C4)]
        have h2'' : ((240 + C4) * ‖qParamFun z‖) ^ 3 ≤ (240 + C4) ^ 3 * ‖qParamFun z‖ := by
          have : ‖qParamFun z‖ ^ 3 ≤ ‖qParamFun z‖ := by nlinarith
          nlinarith [hq0, hq1, mul_nonneg (by positivity : (0:ℝ) ≤ (240 + C4) ^ 3) hq0,
            pow_nonneg (by positivity : (0:ℝ) ≤ 240 + C4) 3]
        nlinarith [h1, h2'', hq0]

/-- `j(z)(E₄ - E₂²)(z) - 288 = O(q(z))` for `Im z ≥ 1/3`. -/
theorem jz_sigma_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288‖ ≤ C * ‖qParamFun z‖ := by
  obtain ⟨Cσ, hCσ, hσ⟩ := sigma_sub_288q_third
  obtain ⟨Cδ, hCδ, hδ⟩ := ZAtomsThird.DeltaFun_two_term_third
  obtain ⟨C3, hC3, hcube⟩ := E4cube_sub_one_third
  obtain ⟨cΔ, hcΔ, hΔ⟩ := delta_lower_third
  have hnum : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖E4Fun z ^ 3 * (E4Fun z - E2Fun z ^ 2) - 288 * DeltaFun z‖
        ≤ (Cσ + 288 * C3 + C3 * Cσ + 288 * Cδ) * ‖qParamFun z‖ ^ 2 := by
    intro z hz
    have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hq1 : ‖qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
    have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
    have hq3 : ‖qParamFun z‖ ^ 3 ≤ ‖qParamFun z‖ ^ 2 := by nlinarith
    have hε := hcube z hz
    have hρ := hσ z hz
    have hrd := hδ z hz
    have hkey : E4Fun z ^ 3 * (E4Fun z - E2Fun z ^ 2) - 288 * DeltaFun z
        = (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
          + 288 * ((E4Fun z ^ 3 - 1) * qParamFun z)
          + (E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
          - 288 * (DeltaFun z - qParamFun z) := by ring
    rw [hkey]
    have h1 : ‖E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z‖ ≤ Cσ * ‖qParamFun z‖ ^ 2 := hρ
    have h2 : ‖(288 : ℂ) * ((E4Fun z ^ 3 - 1) * qParamFun z)‖ ≤ 288 * C3 * ‖qParamFun z‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_mul]
      calc (288 : ℝ) * (‖E4Fun z ^ 3 - 1‖ * ‖qParamFun z‖)
          ≤ 288 * ((C3 * ‖qParamFun z‖) * ‖qParamFun z‖) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right hε hq0
        _ = 288 * C3 * ‖qParamFun z‖ ^ 2 := by ring
    have h3 : ‖(E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)‖
        ≤ C3 * Cσ * ‖qParamFun z‖ ^ 2 := by
      rw [norm_mul]
      calc ‖E4Fun z ^ 3 - 1‖ * ‖E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z‖
          ≤ (C3 * ‖qParamFun z‖) * (Cσ * ‖qParamFun z‖ ^ 2) :=
            mul_le_mul hε hρ (norm_nonneg _) (by positivity)
        _ = C3 * Cσ * (‖qParamFun z‖ * ‖qParamFun z‖ ^ 2) := by ring
        _ ≤ C3 * Cσ * ‖qParamFun z‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hq3, hq0]
    have h4 : ‖(288 : ℂ) * (DeltaFun z - qParamFun z)‖ ≤ 288 * Cδ * ‖qParamFun z‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat]
      calc (288 : ℝ) * ‖DeltaFun z - qParamFun z‖ ≤ 288 * (Cδ * ‖qParamFun z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hrd (by norm_num)
        _ = 288 * Cδ * ‖qParamFun z‖ ^ 2 := by ring
    have hsplit2 : ‖(E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
          + 288 * ((E4Fun z ^ 3 - 1) * qParamFun z)
          + (E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)‖
        ≤ Cσ * ‖qParamFun z‖ ^ 2 + 288 * C3 * ‖qParamFun z‖ ^ 2
          + C3 * Cσ * ‖qParamFun z‖ ^ 2 := by
      have s1 := norm_add_le ((E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
          + 288 * ((E4Fun z ^ 3 - 1) * qParamFun z))
        ((E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z))
      have s2 := norm_add_le (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
        (288 * ((E4Fun z ^ 3 - 1) * qParamFun z))
      linarith [s1, s2, h1, h2, h3, norm_nonneg (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z),
        norm_nonneg (288 * ((E4Fun z ^ 3 - 1) * qParamFun z)),
        norm_nonneg ((E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z))]
    calc ‖(E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
          + 288 * ((E4Fun z ^ 3 - 1) * qParamFun z)
          + (E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
          - 288 * (DeltaFun z - qParamFun z)‖
        ≤ ‖(E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)
            + 288 * ((E4Fun z ^ 3 - 1) * qParamFun z)
            + (E4Fun z ^ 3 - 1) * (E4Fun z - E2Fun z ^ 2 - 288 * qParamFun z)‖
          + ‖(288 : ℂ) * (DeltaFun z - qParamFun z)‖ := norm_sub_le _ _
      _ ≤ (Cσ * ‖qParamFun z‖ ^ 2 + 288 * C3 * ‖qParamFun z‖ ^ 2
            + C3 * Cσ * ‖qParamFun z‖ ^ 2) + 288 * Cδ * ‖qParamFun z‖ ^ 2 :=
          add_le_add hsplit2 h4
      _ = (Cσ + 288 * C3 + C3 * Cσ + 288 * Cδ) * ‖qParamFun z‖ ^ 2 := by ring
  refine ⟨(Cσ + 288 * C3 + C3 * Cσ + 288 * Cδ) / cΔ + 1, by positivity, fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hqz : 0 < ‖qParamFun z‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hfac : jInvariantFun z * (E4Fun z - E2Fun z ^ 2)
      = E4Fun z ^ 3 * (E4Fun z - E2Fun z ^ 2) / DeltaFun z := by
    rw [show jInvariantFun z = E4Fun z ^ 3 / DeltaFun z from rfl]
    ring
  have hsub : jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288
      = (E4Fun z ^ 3 * (E4Fun z - E2Fun z ^ 2) - 288 * DeltaFun z) / DeltaFun z := by
    rw [hfac, sub_div]
    congr 1
    rw [mul_comm 288 (DeltaFun z), mul_div_cancel_left₀ _ hDz]
  have hΔz : cΔ * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ := hΔ z hz
  have hpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcΔ hqz) hΔz
  have hinv : ‖DeltaFun z‖⁻¹ ≤ (cΔ * ‖qParamFun z‖)⁻¹ :=
    (inv_le_inv₀ hpos (mul_pos hcΔ hqz)).mpr hΔz
  have hn := hnum z hz
  rw [hsub, norm_div]
  calc ‖E4Fun z ^ 3 * (E4Fun z - E2Fun z ^ 2) - 288 * DeltaFun z‖ / ‖DeltaFun z‖
      = ‖E4Fun z ^ 3 * (E4Fun z - E2Fun z ^ 2) - 288 * DeltaFun z‖ * ‖DeltaFun z‖⁻¹ := by
        rw [div_eq_mul_inv]
    _ ≤ ((Cσ + 288 * C3 + C3 * Cσ + 288 * Cδ) * ‖qParamFun z‖ ^ 2)
          * (cΔ * ‖qParamFun z‖)⁻¹ :=
        mul_le_mul hn hinv (by positivity) (by positivity)
    _ = (Cσ + 288 * C3 + C3 * Cσ + 288 * Cδ) / cΔ * ‖qParamFun z‖ := by
        field_simp
    _ ≤ ((Cσ + 288 * C3 + C3 * Cσ + 288 * Cδ) / cΔ + 1) * ‖qParamFun z‖ := by
        nlinarith [hq0, div_nonneg (by positivity) hcΔ.le]

end

end Work.Asymptotics
