import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SumIntegralComparisons
import Submission.Commons.Analysis.ExpLog.log_le_two_sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset MeasureTheory intervalIntegral

namespace Commons.Analysis.ExpLog

/-- Reindexing: summing `f` over `Icc 2 k` agrees with summing `f (i+1)`
over `Ico 1 k`, for `2 ≤ k`. -/
private lemma sum_Icc_two_eq_sum_Ico {k : ℕ} (f : ℕ → ℝ) (hk : 2 ≤ k) :
    (∑ n ∈ Finset.Icc 2 k, f n) = ∑ i ∈ Finset.Ico 1 k, f (i + 1) := by
  have hc : Finset.Icc 2 k = Finset.Ico 2 (k + 1) := by
    ext n
    simp
  rw [hc, Finset.sum_Ico_eq_sum_range]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show (k + 1) - 2 = k - 1 by omega]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

/-- `x ↦ 1 / (x * √x)` is antitone on `[a, k]`, for `1 ≤ a`. -/
private lemma inv_sqrt_mul_self_antitoneOn (a k : ℕ) (ha : 1 ≤ a) :
    AntitoneOn (fun x : ℝ => 1 / (x * √x)) (Set.Icc ((a : ℕ) : ℝ) ((k : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  have hxa : ((a : ℕ) : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
  have hya : ((a : ℕ) : ℝ) ≤ y := (Set.mem_Icc.mp hy).1
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < a)
  have hxpos : 0 < x := lt_of_lt_of_le hapos hxa
  have hypos : 0 < y := lt_of_lt_of_le hapos hya
  have hsqrt_le : √x ≤ √y := Real.sqrt_le_sqrt hxy
  have hprod_le : x * √x ≤ y * √y :=
    mul_le_mul hxy hsqrt_le (Real.sqrt_nonneg x) hypos.le
  have hprod_pos : 0 < x * √x := mul_pos hxpos ((Real.sqrt_pos).2 hxpos)
  exact one_div_le_one_div_of_le (a := x * √x) (b := y * √y) hprod_pos hprod_le

/-- `x ↦ 1 / (x * √x)` is continuous on `[a, k]` (real), for `1 ≤ a`. -/
private lemma inv_sqrt_mul_self_continuousOn (a k : ℕ) (ha : 1 ≤ a) :
    ContinuousOn (fun x : ℝ => 1 / (x * √x)) (Set.Icc ((a : ℕ) : ℝ) ((k : ℕ) : ℝ)) := by
  refine ContinuousOn.div ?hnum ?hden ?hne
  · exact continuousOn_const
  · exact (continuous_id.continuousOn.mul Real.continuous_sqrt.continuousOn)
  · intro x hx
    have hxa : ((a : ℕ) : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < a)
    have hxpos : 0 < x := lt_of_lt_of_le hapos hxa
    exact ne_of_gt (mul_pos hxpos ((Real.sqrt_pos).2 hxpos))

/-- The integral of `1 / (x √x)` over `[a, k]` is `2/√a - 2/√k`
(antiderivative `x ↦ -2/√x`), for `1 ≤ a ≤ k`. -/
private lemma integral_inv_sqrt_mul_self (a k : ℕ) (ha : 1 ≤ a) (hak : a ≤ k) :
    (∫ x in ((a : ℕ) : ℝ)..((k : ℕ) : ℝ), 1 / (x * √x)) =
      2 / √((a : ℕ) : ℝ) - 2 / √((k : ℕ) : ℝ) := by
  have hakR : ((a : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hak
  have hcontU : ContinuousOn (fun x : ℝ => 1 / (x * √x))
      (Set.uIcc ((a : ℕ) : ℝ) ((k : ℕ) : ℝ)) := by
    simpa [Set.uIcc_of_le hakR] using inv_sqrt_mul_self_continuousOn a k ha
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (x * √x)) volume
      ((a : ℕ) : ℝ) ((k : ℕ) : ℝ) := hcontU.intervalIntegrable
  have hderiv : ∀ x ∈ Set.uIcc ((a : ℕ) : ℝ) ((k : ℕ) : ℝ),
      HasDerivAt (fun t : ℝ => -2 / √t) (1 / (x * √x)) x := by
    intro x hx
    have hxi : x ∈ Set.Icc ((a : ℕ) : ℝ) ((k : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hakR] using hx
    have hxa : ((a : ℕ) : ℝ) ≤ x := (Set.mem_Icc.mp hxi).1
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < a)
    have hxpos : 0 < x := lt_of_lt_of_le hapos hxa
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hsqrt_ne : √x ≠ 0 := ne_of_gt ((Real.sqrt_pos).2 hxpos)
    have hd1 : HasDerivAt (fun t : ℝ => √t) (1 / (2 * √x)) x :=
      Real.hasDerivAt_sqrt hxne
    have hd2 : HasDerivAt (fun t : ℝ => -2 / √t)
        ((0 * √x - (-2) * (1 / (2 * √x))) / (√x) ^ 2) x :=
      (hasDerivAt_const x (-2)).div hd1 hsqrt_ne
    have hval : (0 * √x - (-2) * (1 / (2 * √x))) / (√x) ^ 2 = 1 / (x * √x) := by
      calc
        (0 * √x - (-2) * (1 / (2 * √x))) / (√x) ^ 2 =
            (2 * (1 / (2 * √x))) / (√x) ^ 2 := by ring
        _ = (1 / √x) / (√x) ^ 2 := by
          field_simp [hsqrt_ne]
        _ = 1 / ((√x) * (√x) ^ 2) := by
          field_simp [hsqrt_ne]
        _ = 1 / (x * √x) := by
          rw [Real.sq_sqrt hxpos.le]
          field_simp [hxne, hsqrt_ne]
    exact hd2.congr_deriv hval
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -2 / √t) (f' := fun x : ℝ => 1 / (x * √x))
      (a := ((a : ℕ) : ℝ)) (b := ((k : ℕ) : ℝ)) hderiv hint
  have hakpos : 0 < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < a)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < k)
  have hsqrtk_ne : √(k : ℝ) ≠ 0 := ne_of_gt ((Real.sqrt_pos).2 hkpos)
  have hsqrta_ne : √(a : ℝ) ≠ 0 := ne_of_gt ((Real.sqrt_pos).2 hakpos)
  calc
    (∫ x in ((a : ℕ) : ℝ)..((k : ℕ) : ℝ), 1 / (x * √x))
        = (-2) / √(k : ℝ) - (-2) / √(a : ℝ) := hmain
    _ = 2 / √(a : ℝ) - 2 / √(k : ℝ) := by
      field_simp [hsqrtk_ne, hsqrta_ne]
      ring

/-- `∑_{n=2}^{k} 1 / (n √n) ≤ 2` for `k ≥ 2`.

The summand `x ↦ 1/(x√x)` is antitone on `[1, k]`, so the finite sum
`∑_{n=2}^{k} 1/(n√n) = ∑_{i=1}^{k-1} f(i+1)` is bounded by the integral
`∫_{1}^{k} 1/(x√x) dx = 2 - 2/√k ≤ 2`. -/
private lemma sum_inv_sqrt_mul_self_le_two {k : ℕ} (hk : 2 ≤ k) :
    (∑ n ∈ Finset.Icc 2 k, 1 / ((n : ℝ) * √(n : ℝ))) ≤ 2 := by
  let f : ℝ → ℝ := fun x => 1 / (x * √x)
  have h1k : (1 : ℕ) ≤ k := by omega
  have hanti : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) ((k : ℕ) : ℝ)) := by
    simpa [f] using inv_sqrt_mul_self_antitoneOn (a := 1) (k := k)
      (by norm_num : (1 : ℕ) ≤ (1 : ℕ))
  have hmain : (∑ i ∈ Finset.Ico 1 k, f ((i + 1 : ℕ) : ℝ)) ≤
      ∫ x in ((1 : ℕ) : ℝ)..((k : ℕ) : ℝ), f x :=
    AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := k) h1k hanti
  have hreindex : (∑ n ∈ Finset.Icc 2 k, f (n : ℝ)) =
      ∑ i ∈ Finset.Ico 1 k, f ((i + 1 : ℕ) : ℝ) := by
    simpa using sum_Icc_two_eq_sum_Ico (f := fun n : ℕ => f (n : ℝ)) hk
  have hval : (∫ x in ((1 : ℕ) : ℝ)..((k : ℕ) : ℝ), f x) = 2 - 2 / √(k : ℝ) := by
    have hgen : (∫ x in ((1 : ℕ) : ℝ)..((k : ℕ) : ℝ), 1 / (x * √x)) =
        2 / √((1 : ℕ) : ℝ) - 2 / √((k : ℕ) : ℝ) :=
      integral_inv_sqrt_mul_self (a := 1) (k := k)
        (by norm_num : (1 : ℕ) ≤ (1 : ℕ)) h1k
    calc
      (∫ x in ((1 : ℕ) : ℝ)..((k : ℕ) : ℝ), f x)
          = ∫ x in ((1 : ℕ) : ℝ)..((k : ℕ) : ℝ), 1 / (x * √x) := by simp [f]
      _ = 2 / √((1 : ℕ) : ℝ) - 2 / √((k : ℕ) : ℝ) := hgen
      _ = 2 - 2 / √(k : ℝ) := by norm_num [Real.sqrt_one]
  calc
    (∑ n ∈ Finset.Icc 2 k, 1 / ((n : ℝ) * √(n : ℝ)))
        = ∑ n ∈ Finset.Icc 2 k, f (n : ℝ) := by simp [f]
    _ = ∑ i ∈ Finset.Ico 1 k, f ((i + 1 : ℕ) : ℝ) := hreindex
    _ ≤ ∫ x in ((1 : ℕ) : ℝ)..((k : ℕ) : ℝ), f x := hmain
    _ = 2 - 2 / √(k : ℝ) := hval
    _ ≤ 2 := by
      have hnonneg : 0 ≤ 2 / √(k : ℝ) :=
        div_nonneg (by norm_num) (Real.sqrt_nonneg (k : ℝ))
      linarith

/-- For `2 ≤ k`, `log k / k² ≤ 2 / (k √k)`, from `log k ≤ 2√k`. -/
private lemma log_div_sq_le_two_div_sqrt (k : ℕ) (hk : 2 ≤ k) :
    Real.log (k : ℝ) / ((k : ℝ) * (k : ℝ)) ≤ 2 / ((k : ℝ) * √(k : ℝ)) := by
  have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hlog : Real.log (k : ℝ) ≤ 2 * √(k : ℝ) := log_le_two_sqrt hk0
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < k)
  have hk2pos : 0 < (k : ℝ) * (k : ℝ) := mul_pos hkpos hkpos
  have hden2pos : 0 < (k : ℝ) * √(k : ℝ) :=
    mul_pos hkpos ((Real.sqrt_pos).2 hkpos)
  have hsqmul : √(k : ℝ) * √(k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hk0
  have hlog' : Real.log (k : ℝ) * ((k : ℝ) * √(k : ℝ)) ≤ 2 * ((k : ℝ) * (k : ℝ)) := by
    calc
      Real.log (k : ℝ) * ((k : ℝ) * √(k : ℝ))
          ≤ (2 * √(k : ℝ)) * ((k : ℝ) * √(k : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hlog
              (mul_nonneg hkpos.le (Real.sqrt_nonneg (k : ℝ)))
      _ = 2 * ((k : ℝ) * (k : ℝ)) := by
        calc
          (2 * √(k : ℝ)) * ((k : ℝ) * √(k : ℝ))
              = 2 * ((k : ℝ) * (√(k : ℝ) * √(k : ℝ))) := by ring
          _ = 2 * ((k : ℝ) * (k : ℝ)) := by rw [hsqmul]
  rw [div_le_div_iff₀ hk2pos hden2pos]
  exact hlog'

/-- `∑_{k=2}^{n} log k / k² ≤ 4` for `n ≥ 2`.

Each summand satisfies `log k / k² ≤ 2 / (k √k)` (since `log k ≤ 2√k`), and the
right-hand side sums to at most `2·2 = 4` by comparison with
`∫₁ⁿ x⁻³ᐟ² dx = 2 - 2/√n ≤ 2`. -/
lemma sum_log_sq_inv_le_four (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Icc 2 n, Real.log (k : ℝ) / ((k : ℝ) * (k : ℝ))) ≤ 4 := by
  calc
    (∑ k ∈ Finset.Icc 2 n, Real.log (k : ℝ) / ((k : ℝ) * (k : ℝ)))
        ≤ ∑ k ∈ Finset.Icc 2 n, 2 / ((k : ℝ) * √(k : ℝ)) := by
          exact Finset.sum_le_sum (fun k hk => log_div_sq_le_two_div_sqrt k
            ((Finset.mem_Icc.mp hk).1))
    _ = 2 * (∑ k ∈ Finset.Icc 2 n, 1 / ((k : ℝ) * √(k : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ ≤ 2 * 2 := by
          exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_mul_self_le_two (k := n) hn)
            (by norm_num)
    _ = 4 := by norm_num

end Commons.Analysis.ExpLog
