import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.NumberTheory.DirichletCharacter.L_lower_re_two_explicit

open Complex DirichletCharacter
open scoped Real BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### Tail-sum bound `∑_{n ≥ 2} log n / n² ≤ 2`

Elementary proof: `log n ≤ √n` for `n ≥ 1` (from `exp z ≥ 2z` for `z ≥ 0`), so
`log n / n² ≤ √n / n² = 1/(n √n)`, and the latter telescopes:
`1/(n√n) ≤ 2 (1/√(n-1) − 1/√n)` for `n ≥ 2`, so every partial sum of
`∑_{n≥2} √n/n²` is at most `2·(1/√1 − 1/√(K−1)) ≤ 2`. -/

private lemma two_mul_le_exp (v : ℝ) (hv : 0 ≤ v) : 2 * v ≤ Real.exp v := by
  have h1 : 1 + v / 2 ≤ Real.exp (v / 2) := by
    simpa [add_comm] using Real.add_one_le_exp (v / 2)
  have h1nonneg : 0 ≤ 1 + v / 2 := by positivity
  have hsq : (1 + v / 2) ^ 2 ≤ (Real.exp (v / 2)) ^ 2 := pow_le_pow_left₀ h1nonneg h1 2
  have hexp : (Real.exp (v / 2)) ^ 2 = Real.exp v := by
    rw [pow_two, ← Real.exp_add, add_halves]
  calc
    2 * v ≤ (1 + v / 2) ^ 2 := by nlinarith [sq_nonneg (v - 2)]
    _ ≤ Real.exp v := by rw [← hexp]; exact hsq

private lemma log_le_sqrt_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsqrt_one : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx
  have hlog_sqrt_nonneg : 0 ≤ Real.log (Real.sqrt x) := Real.log_nonneg hsqrt_one
  have hmul : 2 * Real.log (Real.sqrt x) ≤ Real.sqrt x := by
    have h := two_mul_le_exp (Real.log (Real.sqrt x)) hlog_sqrt_nonneg
    rwa [Real.exp_log hsqrt_pos] at h
  calc
    Real.log x = 2 * Real.log (Real.sqrt x) := by
      have hl := Real.log_sqrt hx0.le
      linarith
    _ ≤ Real.sqrt x := hmul

private lemma log_nat_le_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  exact log_le_sqrt_of_one_le (by exact_mod_cast hn)

/-- For `n ≥ 2`: `√n / n² ≤ 2 · (1/√(n-1) - 1/√n)`. -/
private lemma sqrt_div_sq_le_two_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (n : ℝ) / (n : ℝ) ^ 2 ≤
      2 * ((Real.sqrt ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹) := by
  let a : ℝ := Real.sqrt ((n - 1 : ℕ) : ℝ)
  let b : ℝ := Real.sqrt (n : ℝ)
  have ha0 : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by exact_mod_cast (by omega : (0 : ℕ) < n - 1))
  have hb0 : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 (by exact_mod_cast (by omega : (0 : ℕ) < n))
  have ha1 : a ≤ b := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n - 1 ≤ n))
  have ha2 : a ^ 2 = ((n - 1 : ℕ) : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (n : ℝ) := by
    dsimp [b]
    exact Real.sq_sqrt (by positivity)
  have hrel : a ^ 2 = b ^ 2 - 1 := by
    rw [ha2, hb2]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hmain : a * (a + b) ≤ 2 * b ^ 2 := by
    nlinarith [ha1, hb0.le, hrel]
  change b / (n : ℝ) ^ 2 ≤ 2 * (a⁻¹ - b⁻¹)
  rw [hb2.symm]
  field_simp [ha0.ne', hb0.ne']
  ring_nf
  nlinarith [hmain]

/-- Every partial sum of `∑_{n ≥ 2} √n / n²` is at most `2`. -/
private lemma sum_sqrt_div_sq_le_two (K : ℕ) :
    (∑ i ∈ Finset.range (K - 2), Real.sqrt ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  by_cases hK2 : K ≤ 2
  · have h0 : K - 2 = 0 := by omega
    rw [h0]
    norm_num
  · let g : ℕ → ℝ := fun m : ℕ => 2 * (Real.sqrt (m : ℝ))⁻¹
    have hg_nonneg : ∀ m : ℕ, 0 ≤ g m := by
      intro m
      dsimp [g]
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg (m : ℝ)))
    have hg1 : g 1 = 2 := by
      dsimp [g]
      norm_num
    have hterm : ∀ i : ℕ, Real.sqrt ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2 ≤ g (i + 1) - g (i + 2) := by
      intro i
      have hsub : (i + 2 - 1 : ℕ) = i + 1 := by omega
      have h := sqrt_div_sq_le_two_sub (n := i + 2) (by omega)
      rw [hsub] at h
      have hg : g (i + 1) - g (i + 2) =
          2 * ((Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt ((i + 2 : ℕ) : ℝ))⁻¹) := by
        dsimp [g]
        ring
      calc
        Real.sqrt ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2 ≤
            2 * ((Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt ((i + 2 : ℕ) : ℝ))⁻¹) := h
        _ = g (i + 1) - g (i + 2) := hg.symm
    calc
      (∑ i ∈ Finset.range (K - 2), Real.sqrt ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2)
          ≤ ∑ i ∈ Finset.range (K - 2), (g (i + 1) - g (i + 2)) := by
            exact Finset.sum_le_sum (fun i _ => hterm i)
      _ = ∑ i ∈ Finset.range (K - 2), (g (i + 1) - g (i + 1 + 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
      _ = g 1 - g (K - 1) := by
            rw [Finset.sum_range_sub' (f := fun i => g (i + 1)) (K - 2)]
            rw [show (K - 2) + 1 = K - 1 by omega]
      _ ≤ 2 := by
            rw [hg1]
            have : 0 ≤ g (K - 1) := hg_nonneg (K - 1)
            linarith

/-- Every partial sum of `∑_{n ≥ 2} log n / n²` is at most `2`. -/
private lemma log_div_nat_sq_partial_le_two (K : ℕ) :
    (∑ n ∈ Finset.range K, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0)) ≤ 2 := by
  by_cases hK : 3 ≤ K
  · have hA : (∑ n ∈ Finset.range K, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0))
        = ∑ i ∈ Finset.range (K - 2), (Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2) := by
      have h1 : (∑ n ∈ Finset.range K, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0))
          = ∑ n ∈ Finset.filter (fun n : ℕ => 2 ≤ n) (Finset.range K), (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
            rw [← Finset.sum_filter]
      have h2 : (∑ n ∈ Finset.filter (fun n : ℕ => 2 ≤ n) (Finset.range K), (Real.log (n : ℝ) / (n : ℝ) ^ 2))
          = ∑ n ∈ Finset.Ico 2 K, (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
            rw [show Finset.filter (fun n : ℕ => 2 ≤ n) (Finset.range K) = Finset.Ico 2 K by
              ext n
              simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
              omega]
      have h3 : (∑ n ∈ Finset.Ico 2 K, (Real.log (n : ℝ) / (n : ℝ) ^ 2))
          = ∑ i ∈ Finset.range (K - 2), (Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2) := by
            rw [Finset.sum_Ico_eq_sum_range (f := fun m : ℕ => Real.log (m : ℝ) / (m : ℝ) ^ 2) 2 K]
            apply Finset.sum_congr rfl
            intro i hi
            rw [show (2 + i : ℕ) = i + 2 by omega]
      rw [h1, h2, h3]
    rw [hA]
    calc
      (∑ i ∈ Finset.range (K - 2), (Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2))
          ≤ ∑ i ∈ Finset.range (K - 2), (Real.sqrt ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2) := by
            exact Finset.sum_le_sum (fun i hi =>
              div_le_div_of_nonneg_right (log_nat_le_sqrt (n := i + 2) (by omega)) (sq_nonneg ((i + 2 : ℕ) : ℝ)))
      _ ≤ 2 := sum_sqrt_div_sq_le_two K
  · have hK2 : K ≤ 2 := by omega
    have hsum : (∑ n ∈ Finset.range K, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < K := Finset.mem_range.mp hn
      have : ¬ 2 ≤ n := by omega
      simp [this]
    rw [hsum]
    norm_num

/-! ### The logarithmic-derivative bound -/

private lemma guard_nonneg (n : ℕ) :
    0 ≤ if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0 := by
  by_cases h : 2 ≤ n
  · simp [h]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (sq_nonneg (n : ℝ))
  · simp [h]

private lemma guard_summable :
    Summable (fun n : ℕ => if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
  exact summable_of_sum_range_le guard_nonneg log_div_nat_sq_partial_le_two

private lemma guard_tsum_le_two :
    (∑' n : ℕ, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0)) ≤ 2 := by
  exact Real.tsum_le_of_sum_range_le guard_nonneg log_div_nat_sq_partial_le_two

/-- `‖L'(χ, s)‖ ≤ 2` on the line `Re s = 2`. -/
private lemma deriv_norm_le_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖deriv (LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 2 := by
  let f : ℕ → ℂ := fun n : ℕ => (χ (n : ZMod N) : ℂ)
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs1 : 1 < s.re := by simp [s]
  have hs2 : s.re = 2 := by simp [s]
  have hder : deriv (LFunction χ) s = -LSeries (LSeries.logMul f) s := by
    have h1 := DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1
    have habs : LSeries.abscissaOfAbsConv f < s.re := by
      have h := DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) χ
      rw [show LSeries.abscissaOfAbsConv f = 1 by simpa [f] using h]
      rw [hs2]
      exact EReal.coe_lt_coe_iff.mpr (by norm_num : (1 : ℝ) < 2)
    have h2 := LSeries_deriv (f := f) (s := s) habs
    calc
      deriv (LFunction χ) s = deriv (LSeries f) s := by simpa [f] using h1
      _ = -LSeries (LSeries.logMul f) s := by simpa [f] using h2
  have hterm : ∀ n : ℕ, ‖LSeries.term (LSeries.logMul f) s n‖ ≤
      (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
    intro n
    by_cases hn : 2 ≤ n
    · have hn0 : n ≠ 0 := by omega
      have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hn0r : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hlogs : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
        symm
        exact Complex.ofReal_log hn0r
      have hnormlog : ‖Complex.log (n : ℂ)‖ = Real.log (n : ℝ) := by
        rw [hlogs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1r)]
      have hnormcoef : ‖LSeries.logMul f n‖ ≤ Real.log (n : ℝ) := by
        calc
          ‖LSeries.logMul f n‖ = ‖Complex.log (n : ℂ)‖ * ‖(χ (n : ZMod N) : ℂ)‖ := by
            simp [LSeries.logMul, f]
          _ ≤ ‖Complex.log (n : ℂ)‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ (n : ZMod N)) (norm_nonneg _)
          _ = Real.log (n : ℝ) := by rw [mul_one, hnormlog]
      have hnormden : (n : ℝ) ^ s.re = (n : ℝ) ^ 2 := by
        rw [hs2]
        simp
      calc
        ‖LSeries.term (LSeries.logMul f) s n‖
            = ‖LSeries.logMul f n‖ / (n : ℝ) ^ s.re := by
              rw [LSeries.norm_term_eq]
              simp [hn0]
        _ = ‖LSeries.logMul f n‖ / (n : ℝ) ^ 2 := by rw [hnormden]
        _ ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hnormcoef (sq_nonneg _)
        _ = (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by simp [hn]
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl
      · simp
      · simp [LSeries.logMul, f]
  have hsumm_norm : Summable (fun n : ℕ => ‖LSeries.term (LSeries.logMul f) s n‖) := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm guard_summable
  calc
    ‖deriv (LFunction χ) s‖ = ‖LSeries (LSeries.logMul f) s‖ := by
      rw [hder, norm_neg]
    _ = ‖(∑' n, LSeries.term (LSeries.logMul f) s n)‖ := rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term (LSeries.logMul f) s n‖ := norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n : ℕ, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) :=
      Summable.tsum_le_tsum hterm hsumm_norm guard_summable
    _ ≤ 2 := guard_tsum_le_two

/-- Bound for the logarithmic derivative of a non-trivial Dirichlet L-function on the
vertical line `Re s = 2`, uniform in the imaginary part:

`‖deriv (LFunction χ) (2 + iT) / LFunction χ (2 + iT)‖ ≤ 8` for all real `T`.

Method: for `Re s = 2 > 1` the L-function agrees with its Dirichlet series
(`DirichletCharacter.LFunction_eq_LSeries`), and its derivative with the termwise
differentiated series (`DirichletCharacter.deriv_LFunction_eq_deriv_LSeries`,
`LSeries_deriv`, with `logMul`); hence
`‖deriv L (2+iT)‖ ≤ ∑_{n≥2} log n / n² ≤ 2`
(prove `∑_{n≥2} log n / n² ≤ 2` elementarily, e.g. `log n ≤ √n` for `n ≥ 2` and
`∑_{n≥2} n^(−3/2) ≤ 2` by an integral comparison), while
`1/4 ≤ ‖LFunction χ (2+iT)‖` by `Commons.NumberTheory.DirichletCharacter.L_lower_re_two_explicit`.
The bound `8` is loose; any constant `≤ 8` is fine. -/
theorem logDeriv_L_two_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ)) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 8 := by
  let f : ℕ → ℂ := fun n : ℕ => (χ (n : ZMod N) : ℂ)
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hdernorm : ‖deriv (LFunction χ) s‖ ≤ 2 := by
    simpa [s] using deriv_norm_le_two χ T
  have hden : (1 : ℝ) / 4 ≤ ‖LFunction χ s‖ := by
    simpa [s] using L_lower_re_two_explicit χ hχ T
  have hdenpos : 0 < ‖LFunction χ s‖ := by linarith
  rw [norm_div]
  rw [div_le_iff₀ hdenpos]
  have h2b : 2 ≤ 8 * ‖LFunction χ s‖ := by
    calc
      2 ≤ 8 * ((1 : ℝ) / 4) := by norm_num
      _ ≤ 8 * ‖LFunction χ s‖ := mul_le_mul_of_nonneg_left hden (by norm_num)
  nlinarith

end Commons.NumberTheory.DirichletCharacter