import Mathlib

open scoped Classical

namespace Work.EQ

/-- **An entire function of polynomial growth is a polynomial.** If `F : ℂ → ℂ` is complex
differentiable everywhere and satisfies `‖F z‖ ≤ C * ‖z‖ ^ m` for all `z` with `R ≤ ‖z‖`
(with `C > 0`), then `F` is the evaluation of a polynomial. -/
theorem entire_of_polyGrowth {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∃ (m : ℕ) (C R : ℝ), 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖F z‖ ≤ C * ‖z‖ ^ m) :
    ∃ N : Polynomial ℂ, ∀ z : ℂ, F z = N.eval z := by
  obtain ⟨m, C, R, hCpos, hbound⟩ := h
  -- Step 1: the `(m+1)`-st derivative of `F` vanishes identically, by Cauchy's estimate on
  -- circles of arbitrarily large radius.
  have hk : ∀ z : ℂ, iteratedDeriv (m+1) F z = 0 := by
    intro z
    rw [← norm_le_zero_iff]
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    simp only [zero_add]
    set K : ℝ := (m+1).factorial * C * (1 + ‖z‖)^m with hKdef
    have hKpos : 0 < K := by rw [hKdef]; positivity
    set t : ℝ := max (max (max R 1) (K / ε)) (‖z‖ + R) + 1 with htdef
    have ht1 : 1 ≤ t := by
      rw [htdef]
      have h1 : (1:ℝ) ≤ max (max R 1) (K/ε) := le_trans (le_max_right R 1) (le_max_left _ _)
      have h2 : max (max R 1) (K/ε) ≤ max (max (max R 1) (K/ε)) (‖z‖ + R) := le_max_left _ _
      linarith
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have htR : R ≤ t := by
      rw [htdef]
      have h1 : R ≤ max (max R 1) (K/ε) := le_trans (le_max_left R 1) (le_max_left _ _)
      have h2 : max (max R 1) (K/ε) ≤ max (max (max R 1) (K/ε)) (‖z‖ + R) := le_max_left _ _
      linarith
    have htK : K / ε ≤ t := by
      rw [htdef]
      have h1 : K/ε ≤ max (max R 1) (K/ε) := le_max_right _ _
      have h2 : max (max R 1) (K/ε) ≤ max (max (max R 1) (K/ε)) (‖z‖ + R) := le_max_left _ _
      linarith
    have htzR : ‖z‖ + R ≤ t := by
      rw [htdef]; linarith [le_max_right (max (max R 1) (K/ε)) (‖z‖ + R)]
    have hsphere : ∀ w ∈ Metric.sphere z t, ‖F w‖ ≤ C * (‖z‖ + t)^m := by
      intro w hw
      have hwz : ‖w - z‖ = t := by
        rwa [mem_sphere_iff_norm] at hw
      have hwR : R ≤ ‖w‖ := by
        have h1 : t - ‖z‖ ≤ ‖w‖ := by
          have h2 := norm_sub_le w z
          rw [hwz] at h2
          linarith
        have h2 : R ≤ t - ‖z‖ := by linarith
        linarith
      have hwle : ‖w‖ ≤ ‖z‖ + t := by
        have h2 := norm_add_le (w - z) z
        rw [sub_add_cancel] at h2
        linarith [hwz]
      calc ‖F w‖ ≤ C * ‖w‖^m := hbound w hwR
        _ ≤ C * (‖z‖ + t)^m := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
              exact pow_le_pow_left₀ (norm_nonneg w) hwle m
    have hratio : (‖z‖ + t)^m / t^(m+1) ≤ (1 + ‖z‖)^m / t := by
      rw [pow_succ, ← div_div]
      apply div_le_div_of_nonneg_right _ (le_of_lt htpos)
      rw [← div_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ htpos]
      nlinarith [ht1, norm_nonneg z]
    have hmain : (↑(m+1).factorial : ℝ) * (C * (‖z‖ + t)^m) / t^(m+1) ≤ ε := by
      calc (↑(m+1).factorial : ℝ) * (C * (‖z‖ + t)^m) / t^(m+1)
          = ((↑(m+1).factorial : ℝ) * C) * ((‖z‖ + t)^m / t^(m+1)) := by ring
        _ ≤ ((↑(m+1).factorial : ℝ) * C) * ((1 + ‖z‖)^m / t) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = K / t := by rw [hKdef]; ring
        _ ≤ ε := by
              rw [div_le_iff₀ htpos]
              have hh := (div_le_iff₀ hε).mp htK
              linarith
    have hcauchy : ‖iteratedDeriv (m+1) F z‖ ≤
        (↑(m+1).factorial : ℝ) * (C * (‖z‖ + t)^m) / t^(m+1) :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (m+1) htpos hF.diffContOnCl hsphere
    exact hcauchy.trans hmain
  -- Step 2: consequently every derivative of order `≥ m+1` vanishes identically.
  have hfun : ∀ j : ℕ, iteratedDeriv (m+1+j) F = 0 := by
    intro j
    induction j with
    | zero => funext x; simpa using hk x
    | succ j ih =>
        have hidx : m+1+(j+1) = (m+1+j)+1 := by omega
        rw [hidx, iteratedDeriv_succ, ih, deriv_zero]
  have hvan : ∀ n, m+1 ≤ n → iteratedDeriv n F 0 = 0 := by
    intro n hn
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hn
    rw [hj]
    exact congrFun (hfun j) 0
  -- Step 3: `F` is the Taylor polynomial of order `m` at `0`.
  refine ⟨∑ n ∈ Finset.range (m+1),
      Polynomial.C ((↑n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0) * Polynomial.X ^ n, fun z => ?_⟩
  rw [← Complex.taylorSeries_eq_of_entire' (0:ℂ) z hF]
  simp only [sub_zero]
  rw [show (∑' n : ℕ, (↑n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0 * z^n) =
        ∑ n ∈ Finset.range (m+1), ((↑n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0 * z^n) from
      tsum_eq_sum (s := Finset.range (m+1)) (fun n hn => by
        simp only [Finset.mem_range, not_lt] at hn
        rw [hvan n hn]; ring)]
  rw [Polynomial.eval_finsetSum]
  refine (Finset.sum_congr rfl (fun n hn => ?_)).symm
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

end Work.EQ
