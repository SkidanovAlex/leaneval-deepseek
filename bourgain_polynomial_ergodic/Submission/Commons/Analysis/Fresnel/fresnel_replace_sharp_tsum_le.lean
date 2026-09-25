import Mathlib
import Submission.Commons.Analysis.Fresnel.fresnel_integral_decay
import Submission.Commons.Analysis.Fresnel.fresnel_integral_one_sub_le

namespace Commons.Analysis.Fresnel

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- Partial sums of `∑ 4^i` are at most `4^m / 3`. -/
private lemma geom_four_sum_le (m : ℕ) :
    ∑ i ∈ Finset.range m, (4:ℝ)^i ≤ (4:ℝ)^m / 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h : (4:ℝ)^m / 3 + (4:ℝ)^m = ((4:ℝ)^m * 4) / 3 := by ring
    calc ∑ i ∈ Finset.range m, (4:ℝ)^i + (4:ℝ)^m
        ≤ (4:ℝ)^m / 3 + (4:ℝ)^m := add_le_add_left ih _
      _ = ((4:ℝ)^m * 4) / 3 := h

/-- `∑_{i<m} (1/2)^i = 2 - 2 (1/2)^m`. -/
private lemma geom_half_eq (m : ℕ) :
    ∑ i ∈ Finset.range m, ((1:ℝ)/2)^i = 2 - 2 * ((1:ℝ)/2)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private lemma one_div_two_pow (m : ℕ) : (1:ℝ) / (2:ℝ)^m = ((1:ℝ)/2)^m := by
  rw [one_div, ← inv_pow, one_div]

/-- For `z ≥ 1`, `1 / √(z · 4^m) ≤ (1/2)^m`. -/
private lemma inv_sqrt_mul_four_pow_le (z : ℝ) (hz : 1 ≤ z) (m : ℕ) :
    1 / Real.sqrt (z * (4:ℝ)^m) ≤ ((1:ℝ)/2)^m := by
  have h2pos : (0:ℝ) < (2:ℝ)^m := pow_pos (by norm_num) m
  have h22 : (2:ℝ)^m * (2:ℝ)^m = (4:ℝ)^m := by rw [← mul_pow]; norm_num
  have hle : (2:ℝ)^m ≤ Real.sqrt (z * (4:ℝ)^m) := by
    calc (2:ℝ)^m = Real.sqrt ((2:ℝ)^m * (2:ℝ)^m) :=
          (Real.sqrt_mul_self (le_of_lt h2pos)).symm
      _ ≤ Real.sqrt (z * (4:ℝ)^m) := by
            apply Real.sqrt_le_sqrt
            rw [h22]
            nlinarith [hz, pow_pos (by norm_num : (0:ℝ) < 4) m]
  calc 1 / Real.sqrt (z * (4:ℝ)^m) ≤ 1 / (2:ℝ)^m := one_div_le_one_div_of_le h2pos hle
    _ = ((1:ℝ)/2)^m := one_div_two_pow m

/-- `1 / √|4^(j+m) x| ≤ (1/2)^m` when `|4^j x| ≥ 1`. -/
private lemma inv_sqrt_four_pow (x : ℝ) (j m : ℕ) (hj : 1 ≤ |(4:ℝ)^j * x|) :
    1 / Real.sqrt |(4:ℝ)^(j+m) * x| ≤ ((1:ℝ)/2)^m := by
  have h1 : |(4:ℝ)^(j+m) * x| = (4:ℝ)^(j+m) * |x| := by
    rw [abs_mul, abs_of_pos (pow_pos (by norm_num) (j+m))]
  have h2 : |(4:ℝ)^j * x| * (4:ℝ)^m = (4:ℝ)^j * |x| * (4:ℝ)^m := by
    rw [abs_mul, abs_of_pos (pow_pos (by norm_num) j)]
  have hsplit : |(4:ℝ)^(j+m) * x| = |(4:ℝ)^j * x| * (4:ℝ)^m := by
    rw [h1, h2, pow_add]; ring
  rw [hsplit]
  exact inv_sqrt_mul_four_pow_le _ hj m

/-- In the regime `|y| ≤ 1` the Fresnel factor is close to `1`. -/
private lemma fresnel_regime_small (y : ℝ) (hy : |y| ≤ 1) :
    ‖(∫ s in (0:ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((y * s^2 : ℝ) : ℂ)))
      - (if |y| ≤ 1 then (1:ℂ) else 0)‖ ≤ 2 * Real.pi * |y| := by
  rw [if_pos hy]
  exact fresnel_integral_one_sub_le y

/-- In the regime `|y| > 1` the Fresnel factor decays. -/
private lemma fresnel_regime_large (y : ℝ) (hy : 1 < |y|) {C : ℝ}
    (hC : ‖(∫ s in (0:ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((y * s^2 : ℝ) : ℂ)))‖ ≤ C / Real.sqrt |y|) :
    ‖(∫ s in (0:ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((y * s^2 : ℝ) : ℂ)))
      - (if |y| ≤ 1 then (1:ℂ) else 0)‖ ≤ C / Real.sqrt |y| := by
  rw [if_neg (not_le.mpr hy), sub_zero]
  exact hC

theorem fresnel_replace_sharp_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ≠ 0 →
      (∑' k : ℕ,
        ‖(∫ s in (0:ℝ)..1,
            Complex.exp (2 * Real.pi * Complex.I * ((((4:ℝ)^k * x) * s ^ 2 : ℝ) : ℂ)))
          - (if |(4:ℝ)^k * x| ≤ 1 then (1:ℂ) else 0)‖) ≤ C := by
  classical
  obtain ⟨C₁, hC₁pos, hdecay⟩ := fresnel_integral_decay
  have hC₁'ge : C₁ ≤ max C₁ 2 := le_max_left _ _
  have hC₁'ge2 : (2:ℝ) ≤ max C₁ 2 := le_max_right _ _
  have hC₁'pos : (0:ℝ) < max C₁ 2 := lt_of_lt_of_le (by norm_num) hC₁'ge2
  refine ⟨8 * Real.pi / 3 + 2 * (max C₁ 2), ?_, ?_⟩
  · have := Real.pi_pos; linarith
  · intro x hx
    have hxabs : 0 < |x| := abs_pos.mpr hx
    have hdecay' : ∀ y : ℝ, 1 ≤ |y| →
        ‖(∫ s in (0:ℝ)..1,
            Complex.exp (2 * Real.pi * Complex.I * ((y * s^2 : ℝ) : ℂ)))‖
          ≤ (max C₁ 2) / Real.sqrt |y| := by
      intro y hy
      exact le_trans (hdecay y hy) (div_le_div_of_nonneg_right hC₁'ge (Real.sqrt_nonneg _))
    have hmono : ∀ i j : ℕ, i ≤ j → |(4:ℝ)^i * x| ≤ |(4:ℝ)^j * x| := by
      intro i j hij
      have hi : |(4:ℝ)^i * x| = (4:ℝ)^i * |x| := by
        rw [abs_mul, abs_of_pos (pow_pos (by norm_num) i)]
      have hj : |(4:ℝ)^j * x| = (4:ℝ)^j * |x| := by
        rw [abs_mul, abs_of_pos (pow_pos (by norm_num) j)]
      rw [hi, hj]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij) (abs_nonneg x)
    have hex : ∃ k : ℕ, 1 < |(4:ℝ)^k * x| := by
      have htop : Tendsto (fun k : ℕ => (4:ℝ)^k * |x|) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4)).atTop_mul_const hxabs
      obtain ⟨k, hk⟩ := (htop.eventually (eventually_gt_atTop (1:ℝ))).exists
      refine ⟨k, ?_⟩
      have h : |(4:ℝ)^k * x| = (4:ℝ)^k * |x| := by
        rw [abs_mul, abs_of_pos (pow_pos (by norm_num) k)]
      rw [h]; exact hk
    set j := Nat.find hex with hjdef
    have hj_spec : 1 < |(4:ℝ)^j * x| := Nat.find_spec hex
    have hj_min : ∀ i, i < j → |(4:ℝ)^i * x| ≤ 1 :=
      fun i hi => not_lt.mp (Nat.find_min hex hi)
    have hj_le : ∀ i, j ≤ i → 1 < |(4:ℝ)^i * x| :=
      fun i hi => lt_of_lt_of_le hj_spec (hmono j i hi)
    have hb : ∀ k : ℕ,
        ‖(∫ s in (0:ℝ)..1,
            Complex.exp (2 * Real.pi * Complex.I * ((((4:ℝ)^k * x) * s ^ 2 : ℝ) : ℂ)))
          - (if |(4:ℝ)^k * x| ≤ 1 then (1:ℂ) else 0)‖
        ≤ (if |(4:ℝ)^k * x| ≤ 1 then 2 * Real.pi * |(4:ℝ)^k * x|
            else (max C₁ 2) / Real.sqrt |(4:ℝ)^k * x|) := by
      intro k
      by_cases hk : |(4:ℝ)^k * x| ≤ 1
      · simpa only [if_pos hk] using fresnel_regime_small ((4:ℝ)^k * x) hk
      · simpa only [if_neg hk, sub_zero] using
          fresnel_regime_large ((4:ℝ)^k * x) (lt_of_not_ge hk)
            (hdecay' _ (le_of_lt (lt_of_not_ge hk)))
    have hsum_small : ∀ m, (∀ i, i < m → |(4:ℝ)^i * x| ≤ 1) →
        ∑ i ∈ Finset.range m, |(4:ℝ)^i * x| ≤ 4/3 := by
      intro m hm
      have h1 : ∑ i ∈ Finset.range m, |(4:ℝ)^i * x| =
          (∑ i ∈ Finset.range m, (4:ℝ)^i) * |x| := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [abs_mul, abs_of_pos (pow_pos (by norm_num) i)])
      rw [h1]
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp only [Finset.sum_range_zero]; norm_num
      · have hlast : |(4:ℝ)^(m-1) * x| ≤ 1 := hm (m-1) (Nat.sub_lt hmpos (by norm_num))
        have hlast2 : (4:ℝ)^(m-1) * |x| ≤ 1 := by
          rwa [abs_mul, abs_of_pos (pow_pos (by norm_num) (m-1))] at hlast
        have hgm : (∑ i ∈ Finset.range m, (4:ℝ)^i) ≤ (4:ℝ)^m / 3 := geom_four_sum_le m
        have hpow : (4:ℝ)^m = 4 * (4:ℝ)^(m-1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m from hmpos)]
          rw [pow_succ']
        have h4m : (4:ℝ)^m * |x| ≤ 4 := by
          rw [hpow]; nlinarith [hlast2]
        calc (∑ i ∈ Finset.range m, (4:ℝ)^i) * |x|
            ≤ ((4:ℝ)^m / 3) * |x| := mul_le_mul_of_nonneg_right hgm (abs_nonneg x)
          _ = (4:ℝ)^m * |x| / 3 := by ring
          _ ≤ 4/3 := by linarith
    refine Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) ?_
    intro n
    let b : ℕ → ℝ := fun k =>
      ‖(∫ s in (0:ℝ)..1,
          Complex.exp (2 * Real.pi * Complex.I * ((((4:ℝ)^k * x) * s ^ 2 : ℝ) : ℂ)))
        - (if |(4:ℝ)^k * x| ≤ 1 then (1:ℂ) else 0)‖
    change ∑ i ∈ Finset.range n, b i ≤ 8 * Real.pi / 3 + 2 * (max C₁ 2)
    by_cases hnj : n ≤ j
    · have hbnd : ∀ i ∈ Finset.range n, b i ≤ 2 * Real.pi * |(4:ℝ)^i * x| := by
        intro i hi
        have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hnj
        exact le_trans (hb i) (le_of_eq (if_pos (hj_min i hij)))
      calc ∑ i ∈ Finset.range n, b i
          ≤ ∑ i ∈ Finset.range n, 2 * Real.pi * |(4:ℝ)^i * x| := Finset.sum_le_sum hbnd
        _ = 2 * Real.pi * (∑ i ∈ Finset.range n, |(4:ℝ)^i * x|) := by rw [Finset.mul_sum]
        _ ≤ 2 * Real.pi * (4/3) :=
              mul_le_mul_of_nonneg_left
                (hsum_small n (fun i hi => hj_min i (lt_of_lt_of_le hi hnj)))
                (by positivity)
        _ = 8 * Real.pi / 3 := by ring
        _ ≤ 8 * Real.pi / 3 + 2 * (max C₁ 2) := by linarith [hC₁'pos]
    · have hjn : j < n := lt_of_not_ge hnj
      have hn_eq : n = j + (n - j) := (Nat.add_sub_cancel' (le_of_lt hjn)).symm
      rw [hn_eq, Finset.sum_range_add]
      have hfirst : ∑ i ∈ Finset.range j, b i ≤ 8 * Real.pi / 3 := by
        calc ∑ i ∈ Finset.range j, b i
            ≤ ∑ i ∈ Finset.range j, 2 * Real.pi * |(4:ℝ)^i * x| :=
                Finset.sum_le_sum (fun i hi =>
                  le_trans (hb i) (le_of_eq (if_pos (hj_min i (Finset.mem_range.mp hi)))))
          _ = 2 * Real.pi * (∑ i ∈ Finset.range j, |(4:ℝ)^i * x|) := by rw [Finset.mul_sum]
          _ ≤ 2 * Real.pi * (4/3) :=
                mul_le_mul_of_nonneg_left (hsum_small j hj_min) (by positivity)
          _ = 8 * Real.pi / 3 := by ring
      have hsecond : ∑ m ∈ Finset.range (n - j), b (j + m) ≤ 2 * (max C₁ 2) := by
        have hstep : ∀ m ∈ Finset.range (n - j),
            b (j + m) ≤ (max C₁ 2) * ((1:ℝ)/2)^m := by
          intro m _
          have hjm : 1 < |(4:ℝ)^(j+m) * x| := hj_le (j + m) (Nat.le_add_right j m)
          have hmul : (max C₁ 2) / Real.sqrt |(4:ℝ)^(j+m) * x| ≤ (max C₁ 2) * ((1:ℝ)/2)^m := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left (inv_sqrt_four_pow x j m (le_of_lt hj_spec))
              (le_of_lt hC₁'pos)
          exact le_trans (le_trans (hb (j + m))
            (le_of_eq (if_neg (not_le.mpr hjm)))) hmul
        calc ∑ m ∈ Finset.range (n - j), b (j + m)
            ≤ ∑ m ∈ Finset.range (n - j), (max C₁ 2) * ((1:ℝ)/2)^m :=
                Finset.sum_le_sum hstep
          _ = (max C₁ 2) * ∑ m ∈ Finset.range (n - j), ((1:ℝ)/2)^m := by
                rw [Finset.mul_sum]
          _ ≤ (max C₁ 2) * 2 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₁'pos)
                rw [geom_half_eq]
                have := pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) (n - j)
                linarith
          _ = 2 * (max C₁ 2) := by ring
      exact add_le_add hfirst hsecond

end Commons.Analysis.Fresnel
