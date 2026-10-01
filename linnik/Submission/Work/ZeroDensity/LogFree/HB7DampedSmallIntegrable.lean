import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs

namespace Work.ZeroDensity.LogFree

open MeasureTheory

/-! Integrability of the damped integrand for the class of *small* exponents.

For `0 < X`, `0 < U' ≤ X`, `L ≥ 1`, exponents `a i ∈ [0, 1/L]` and arbitrary complex weights
`z i`, frequencies `γ i`, the function
`y ↦ (e^{-y/X} - e^{-y/U'}) · ‖Σ_i z_i y^{a_i - iγ_i}‖² / y`
is integrable on `(0, ∞)`.

No separation condition on the frequencies `γ` is needed: the pointwise bound
`‖y^{a i - iγ i}‖ = y^{a i} ≤ max 1 (y^{1/L})` together with `a i ≤ 1/L` dominates the exponential
sum by `(Σ_i ‖z_i‖) (1 + y^{1/L})`, and the weight `e^{-y/X} - e^{-y/U'}` is
`≤ y (1/U' - 1/X)` (mean value bound) near `0` and `≤ e^{-y/X}` (super-exponential decay) near `∞`.

The two elementary estimates are proved first as separate lemmas. -/

/-- Pointwise norm bound for the exponential-twist sum.  For `y > 0`, `0 ≤ a i` and `a i ≤ 1/L`,
`‖Σ_i z_i y^{a_i - iγ_i}‖ ≤ (Σ_i ‖z_i‖) (1 + y^{1/L})`: the complex power contributes exactly
`y^{a_i}` (its imaginary part is a unit modulus factor), and `y^{a_i} ≤ 1 + y^{1/L}` in both
regimes `y ≤ 1` and `y ≥ 1`. -/
lemma HB7DampedSmallSumBound {L : ℝ} {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ)
    (ha : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ 1 / L) {y : ℝ} (hy : 0 < y) :
    ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ≤
      (∑ i, ‖z i‖) * (1 + y ^ (1 / L)) := by
  have hre : ∀ i, ((a i : ℂ) - (γ i : ℂ) * Complex.I).re = a i := by
    intro i
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  calc ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖
      ≤ ∑ i, ‖z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ = ∑ i, ‖z i‖ * y ^ (a i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre i]
    _ ≤ ∑ i, ‖z i‖ * (1 + y ^ (1 / L)) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rcases lt_or_ge y 1 with hy1 | hy1
        · have h1 : y ^ (a i) ≤ 1 := Real.rpow_le_one hy.le hy1.le (ha i)
          have h2 : (0 : ℝ) ≤ y ^ (1 / L) := Real.rpow_nonneg hy.le _
          linarith
        · have h1 : y ^ (a i) ≤ y ^ (1 / L) := Real.rpow_le_rpow_of_exponent_le hy1 (haL i)
          have h2 : (0 : ℝ) ≤ 1 := by norm_num
          linarith
    _ = (∑ i, ‖z i‖) * (1 + y ^ (1 / L)) := by rw [Finset.sum_mul]

/-- The damped weight `e^{-y/X} - e^{-y/U'}` for `0 < U' ≤ X` and `y ≥ 0` is nonnegative and
bounded by its mean value estimate `y (1/U' - 1/X)`. -/
lemma HB7DampedSmallExpDiff {X U' : ℝ} (hX : 0 < X) (hU' : 0 < U') (hUX : U' ≤ X) {y : ℝ}
    (hy : 0 ≤ y) :
    0 ≤ Real.exp (-(y / X)) - Real.exp (-(y / U')) ∧
      Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤ y * (1 / U' - 1 / X) := by
  have hXU : 1 / X ≤ 1 / U' := one_div_le_one_div_of_le hU' hUX
  have hyXU : y / X ≤ y / U' := by
    have h := mul_le_mul_of_nonneg_left hXU hy
    simpa [div_eq_mul_inv, mul_div_assoc] using h
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hyXU))
  · have hmain : Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤ y / U' - y / X := by
      have heq : Real.exp (-(y / X)) * Real.exp (-(y / U' - y / X)) = Real.exp (-(y / U')) := by
        rw [← Real.exp_add]; congr 1; ring
      have hea : Real.exp (-(y / X)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have h : 0 ≤ y / X := div_nonneg hy hX.le
        linarith)
      have h1e : 1 - Real.exp (-(y / U' - y / X)) ≤ y / U' - y / X := by
        have := Real.one_sub_le_exp_neg (y / U' - y / X); linarith
      have h1e0 : 0 ≤ 1 - Real.exp (-(y / U' - y / X)) := by
        have h : 0 ≤ y / U' - y / X := sub_nonneg.mpr hyXU
        have h2 : Real.exp (-(y / U' - y / X)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      calc Real.exp (-(y / X)) - Real.exp (-(y / U'))
          = Real.exp (-(y / X)) * (1 - Real.exp (-(y / U' - y / X))) := by rw [← heq]; ring
        _ ≤ 1 * (1 - Real.exp (-(y / U' - y / X))) := mul_le_mul_of_nonneg_right hea h1e0
        _ ≤ 1 * (y / U' - y / X) := mul_le_mul_of_nonneg_left h1e (by norm_num)
        _ = y / U' - y / X := by ring
    calc Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤ y / U' - y / X := hmain
      _ = y * (1 / U' - 1 / X) := by ring

/-- Integrability of the damped integrand on `(0,∞)` for exponents `a i ∈ [0, 1/L]`. -/
theorem HB7DampedSmallIntegrable {X U' L : ℝ} (hX : 0 < X) (hU' : 0 < U') (hUX : U' ≤ X)
    (hL : 1 ≤ L) {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ)
    (ha : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ 1 / L) :
    MeasureTheory.IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
      ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioi 0) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hD0 : 0 ≤ 1 / U' - 1 / X := sub_nonneg.mpr (one_div_le_one_div_of_le hU' hUX)
  have hpow : ∀ i, ContinuousOn
      (fun y : ℝ => (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)) (Set.Ioi 0) :=
    fun i => fun y hy =>
      (Complex.continuousAt_ofReal_cpow_const y _ (Or.inr (ne_of_gt hy))).continuousWithinAt
  have hScont : ContinuousOn
      (fun y : ℝ => ∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)) (Set.Ioi 0) := by
    simpa using continuousOn_finsetSum (Finset.univ : Finset ι)
      (fun i _ => continuousOn_const.mul (hpow i))
  have hc1 : Continuous (fun y : ℝ => Real.exp (-(y / X))) :=
    Real.continuous_exp.comp (continuous_id.div_const X).neg
  have hc2 : Continuous (fun y : ℝ => Real.exp (-(y / U'))) :=
    Real.continuous_exp.comp (continuous_id.div_const U').neg
  have hcont : ContinuousOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
      ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioi 0) :=
    (((hc1.continuousOn).sub (hc2.continuousOn)).mul ((hScont.norm).pow 2)).div
      continuousOn_id (fun y hy => ne_of_gt hy)
  -- near `0`: the mean value bound on the weight makes the integrand bounded on `(0,1]`
  have hnear : IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
      ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioc 0 1) := by
    refine IntegrableOn.of_bound (measure_Ioc_lt_top (a := (0 : ℝ)) (b := 1)) ?_
      (4 * (1 / U' - 1 / X) * (∑ i, ‖z i‖) ^ 2) ?_
    · exact (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      obtain ⟨hy0, hy1⟩ := hy
      have hdiff := HB7DampedSmallExpDiff hX hU' hUX hy0.le
      have hsum := HB7DampedSmallSumBound a γ z ha haL hy0
      have hS2 : ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2
          ≤ ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsum 2
      have hF0 : 0 ≤ (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
          ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y :=
        div_nonneg (mul_nonneg hdiff.1 (sq_nonneg _)) hy0.le
      rw [Real.norm_of_nonneg hF0]
      have ht0 : 0 ≤ y ^ (1 / L) := Real.rpow_nonneg hy0.le _
      have ht1 : y ^ (1 / L) ≤ 1 :=
        Real.rpow_le_one hy0.le hy1 (div_nonneg (by norm_num) hL0.le)
      have hsq : (1 + y ^ (1 / L)) ^ 2 ≤ 4 := by nlinarith
      have hb1 : (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
            ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2
          ≤ (y * (1 / U' - 1 / X)) * ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 :=
        mul_le_mul hdiff.2 hS2 (sq_nonneg _) (mul_nonneg hy0.le hD0)
      calc (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
              ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
          ≤ (y * (1 / U' - 1 / X)) * ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 / y :=
            div_le_div_of_nonneg_right hb1 hy0.le
        _ = (1 / U' - 1 / X) * ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 := by
            rw [mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt hy0)]
        _ = (1 / U' - 1 / X) * (∑ i, ‖z i‖) ^ 2 * (1 + y ^ (1 / L)) ^ 2 := by
            rw [mul_pow]; ring
        _ ≤ (1 / U' - 1 / X) * (∑ i, ‖z i‖) ^ 2 * 4 :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg hD0 (sq_nonneg _))
        _ = 4 * (1 / U' - 1 / X) * (∑ i, ‖z i‖) ^ 2 := by ring
  -- near `∞`: the exponential decay dominates the polynomially growing sum
  have htail : IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
      ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioi 1) := by
    have hb : -1 < 2 / L := by
      have hp : 0 < 2 / L := div_pos (by norm_num) hL0
      linarith
    have hbase : IntegrableOn (fun y : ℝ => y ^ (2 / L) * Real.exp (-(1 / X) * y)) (Set.Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2 / L) (b := 1 / X)
        hb one_pos (one_div_pos.mpr hX)
      simpa [Real.rpow_one] using h
    have hmodel' : IntegrableOn (fun y : ℝ => 4 * (∑ i, ‖z i‖) ^ 2 *
        (y ^ (2 / L) * Real.exp (-(1 / X) * y))) (Set.Ioi 0) :=
      Integrable.const_mul hbase _
    have hmodel : IntegrableOn (fun y : ℝ => 4 * (∑ i, ‖z i‖) ^ 2 *
        (y ^ (2 / L) * Real.exp (-(1 / X) * y))) (Set.Ioi 1) :=
      hmodel'.mono_set (Set.Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono' hmodel ?_ ?_
    · exact (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy1 : 1 ≤ y := hy.le
      have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
      have hdiff := HB7DampedSmallExpDiff hX hU' hUX hy0.le
      have hsum := HB7DampedSmallSumBound a γ z ha haL hy0
      have hS2 : ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2
          ≤ ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsum 2
      have hF0 : 0 ≤ (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
          ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y :=
        div_nonneg (mul_nonneg hdiff.1 (sq_nonneg _)) hy0.le
      rw [Real.norm_of_nonneg hF0]
      have ht1 : 1 ≤ y ^ (1 / L) := Real.one_le_rpow hy1 (div_nonneg (by norm_num) hL0.le)
      have ht2 : (y ^ (1 / L)) ^ 2 = y ^ (2 / L) := by
        rw [pow_two, ← Real.rpow_add hy0]; congr 1; ring
      have hsq : (1 + y ^ (1 / L)) ^ 2 ≤ 4 * y ^ (2 / L) := by
        have h1 : 1 + y ^ (1 / L) ≤ 2 * y ^ (1 / L) := by linarith
        have h2 : (1 + y ^ (1 / L)) ^ 2 ≤ (2 * y ^ (1 / L)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        calc (1 + y ^ (1 / L)) ^ 2 ≤ (2 * y ^ (1 / L)) ^ 2 := h2
          _ = 4 * y ^ (2 / L) := by rw [mul_pow, ht2]; ring
      have hsqA : ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2
          ≤ 4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L) := by
        rw [mul_pow]
        calc (∑ i, ‖z i‖) ^ 2 * (1 + y ^ (1 / L)) ^ 2
            ≤ (∑ i, ‖z i‖) ^ 2 * (4 * y ^ (2 / L)) :=
              mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
          _ = 4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L) := by ring
      have hd : Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤ Real.exp (-(y / X)) := by
        have h := Real.exp_nonneg (-(y / U')); linarith
      have hstep1 : (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
            ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
          ≤ Real.exp (-(y / X)) * ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 / y :=
        div_le_div_of_nonneg_right (mul_le_mul hd hS2 (sq_nonneg _) (Real.exp_nonneg _)) hy0.le
      have hden : Real.exp (-(y / X)) * (4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L)) / y
          ≤ Real.exp (-(y / X)) * (4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L)) := by
        have h0 : 0 ≤ Real.exp (-(y / X)) * (4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L)) :=
          mul_nonneg (Real.exp_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hy0.le _))
        rw [div_eq_mul_inv]
        simpa using mul_le_mul_of_nonneg_left ((inv_le_one₀ hy0).mpr hy1) h0
      calc (Real.exp (-(y / X)) - Real.exp (-(y / U'))) *
              ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
          ≤ Real.exp (-(y / X)) * ((∑ i, ‖z i‖) * (1 + y ^ (1 / L))) ^ 2 / y := hstep1
        _ ≤ Real.exp (-(y / X)) * (4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L)) / y :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqA (Real.exp_nonneg _)) hy0.le
        _ ≤ Real.exp (-(y / X)) * (4 * (∑ i, ‖z i‖) ^ 2 * y ^ (2 / L)) := hden
        _ = 4 * (∑ i, ‖z i‖) ^ 2 * (y ^ (2 / L) * Real.exp (-(1 / X) * y)) := by
            rw [show Real.exp (-(y / X)) = Real.exp (-(1 / X) * y) from by congr 1; ring]
            ring
  have hfin := hnear.union htail
  rw [Set.Ioc_union_Ioi (show (1 : ℝ) ≤ max 0 1 by norm_num),
    min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at hfin
  exact hfin

end Work.ZeroDensity.LogFree
