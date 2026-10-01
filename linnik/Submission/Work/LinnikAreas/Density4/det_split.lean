import Mathlib
import Submission.Work.LinnikAreas.Density4.zeroDetAux

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-! ## Bounds on the mollifier coefficients

`|ψ_d| ≤ 1` (for `0 < U`, so that the branch `U < d ≤ V` forces `V/U > 1`) and
`|θ_d| ≤ 1` (always).  These give `|Ψ(n)|, |Θ(n)| ≤ n.divisors.card ≤ n`, whence the terms of
`detSum` are dominated by `n ↦ n^2 · n^{|Re ρ|} · e^{-nt}`, summable for `t > 0` with any
polynomial factor.  This is the "absolute convergence" behind `det_split`. -/

/-- `|ψ_d| ≤ 1` for `0 < U`.  In the middle branch `U < d ≤ V` one has `1 ≤ V/d ≤ V/U`, so
`0 ≤ log(V/d) ≤ log(V/U)` and the ratio lies in `[0,1]`. -/
lemma abs_psiM_le_one {U V : ℝ} (hU : 0 < U) (d : ℕ) : |psiM U V d| ≤ 1 := by
  rw [psiM]
  by_cases h1 : (d:ℝ) ≤ U
  · rw [if_pos h1]
    have : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact this
  · rw [if_neg h1]
    by_cases h2 : (d:ℝ) ≤ V
    · rw [if_pos h2]
      have hUd : U < (d:ℝ) := not_le.mp h1
      have hd0 : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hU hUd.le
      have hV0 : (0:ℝ) < V := lt_of_lt_of_le hd0 h2
      have hVU1 : 1 < V / U := by rw [lt_div_iff₀ hU]; linarith
      have hlogU : 0 < Real.log (V/U) := Real.log_pos hVU1
      have hlogd_nn : 0 ≤ Real.log (V/(d:ℝ)) := by
        apply Real.log_nonneg; rw [le_div_iff₀ hd0]; simpa using h2
      have hlogd_le : Real.log (V/(d:ℝ)) ≤ Real.log (V/U) := by
        apply Real.log_le_log (div_pos hV0 hd0)
        exact (div_le_div_iff_of_pos_left hV0 hd0 hU).mpr hUd.le
      have hratio : |Real.log (V/(d:ℝ)) / Real.log (V/U)| ≤ 1 := by
        rw [abs_div, abs_of_nonneg hlogd_nn, abs_of_pos hlogU, div_le_one hlogU]; exact hlogd_le
      have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (V/(d:ℝ)) / Real.log (V/U)|
          = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              |Real.log (V/(d:ℝ)) / Real.log (V/U)| := by rw [mul_div_assoc, abs_mul]
        _ ≤ 1 * 1 := mul_le_mul hμ hratio (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    · rw [if_neg h2]; simp

/-- `|θ_d| ≤ 1`.  In the branch `d ≤ W` with `d ≥ 1` we have `W ≥ 1`; for `W = 1` the value is
`0`, and for `W > 1` one has `1 ≤ W/d ≤ W`, so `0 ≤ log(W/d) ≤ log W`. -/
lemma abs_thetaM_le_one (W : ℝ) (d : ℕ) : |thetaM W d| ≤ 1 := by
  rw [thetaM]
  by_cases h1 : (d:ℝ) ≤ W
  · rw [if_pos h1]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      by_cases hW : W ≤ 1
      · have hdeq : (d:ℝ) = 1 := le_antisymm (le_trans h1 hW) hd1
        have hd_eq : d = 1 := by exact_mod_cast hdeq
        subst hd_eq
        have hWeq : W = 1 := le_antisymm hW (by simpa using h1)
        rw [hWeq]; simp
      · have hW1 : 1 < W := not_le.mp hW
        have hW0 : (0:ℝ) < W := by linarith
        have hlogW : 0 < Real.log W := Real.log_pos hW1
        have hlogd_nn : 0 ≤ Real.log (W/(d:ℝ)) := by
          apply Real.log_nonneg; rw [le_div_iff₀ hd0]; simpa using h1
        have hlogd_le : Real.log (W/(d:ℝ)) ≤ Real.log W := by
          apply Real.log_le_log (div_pos hW0 hd0)
          rw [div_le_iff₀ hd0]
          exact le_mul_of_one_le_right hW0.le hd1
        have hratio : |Real.log (W/(d:ℝ)) / Real.log W| ≤ 1 := by
          rw [abs_div, abs_of_nonneg hlogd_nn, abs_of_pos hlogW, div_le_one hlogW]; exact hlogd_le
        have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        calc |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (W/(d:ℝ)) / Real.log W|
            = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                |Real.log (W/(d:ℝ)) / Real.log W| := by rw [mul_div_assoc, abs_mul]
          _ ≤ 1 * 1 := mul_le_mul hμ hratio (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
  · rw [if_neg h1]; simp

/-- `|Ψ(n)| = |Σ_{d|n} ψ_d| ≤ n`. -/
lemma abs_psiS_le {U V : ℝ} (hU : 0 < U) (n : ℕ) : |psiS U V n| ≤ (n:ℝ) := by
  rw [psiS]
  calc |∑ d ∈ n.divisors, psiM U V d| ≤ ∑ d ∈ n.divisors, |psiM U V d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, (1:ℝ) := Finset.sum_le_sum (fun d _ => abs_psiM_le_one hU d)
    _ = ((n.divisors.card : ℕ) : ℝ) := by simp
    _ ≤ (n:ℝ) := by exact_mod_cast Nat.card_divisors_le_self n

/-- `|Θ(n)| = |Σ_{d|n} θ_d| ≤ n`. -/
lemma abs_thetaS_le (W : ℝ) (n : ℕ) : |thetaS W n| ≤ (n:ℝ) := by
  rw [thetaS]
  calc |∑ d ∈ n.divisors, thetaM W d| ≤ ∑ d ∈ n.divisors, |thetaM W d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, (1:ℝ) := Finset.sum_le_sum (fun d _ => abs_thetaM_le_one W d)
    _ = ((n.divisors.card : ℕ) : ℝ) := by simp
    _ ≤ (n:ℝ) := by exact_mod_cast Nat.card_divisors_le_self n

/-- The detector coefficient is polynomially bounded: `‖a_n χ(n) n^{-ρ}‖ ≤ n^{2⌈2+|Re ρ|⌉}`. -/
lemma norm_detCoeff_le {q : ℕ} [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hU : 0 < U) (n : ℕ) :
    ‖detCoeff q U V W χ ρ n‖ ≤ (n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : detCoeff q U V W χ ρ 0 = 0 := by simp [detCoeff, psiS_zero]
    rw [h0, norm_zero]
    exact pow_nonneg (Nat.cast_nonneg 0) _
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hKle : 2 + |ρ.re| ≤ ((Nat.ceil (2 + |ρ.re|) : ℕ) : ℝ) := Nat.le_ceil _
    have hK2 : 2 ≤ Nat.ceil (2 + |ρ.re|) :=
      by exact_mod_cast (le_trans (by norm_num : (2:ℝ) ≤ 2 + |ρ.re|) hKle)
    have hKs : |ρ.re| ≤ ((Nat.ceil (2 + |ρ.re|) : ℕ) : ℝ) :=
      le_trans (by linarith [abs_nonneg ρ.re] : |ρ.re| ≤ 2 + |ρ.re|) hKle
    have hpsi : ‖((psiS U V n : ℝ) : ℂ)‖ ≤ (n:ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_psiS_le hU n
    have htheta : ‖((thetaS W n : ℝ) : ℂ)‖ ≤ (n:ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_thetaS_le W n
    have hchi : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hcp : ‖((n:ℂ)^(-ρ))‖ ≤ (n:ℝ) ^ (|ρ.re|) := by
      rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_abs ρ.re)
    calc ‖detCoeff q U V W χ ρ n‖
        = ‖((psiS U V n : ℝ) : ℂ) * ((thetaS W n : ℝ) : ℂ) * χ (n : ZMod q)
            * ((n:ℂ)^(-ρ))‖ := rfl
      _ = ‖((psiS U V n : ℝ) : ℂ)‖ * ‖((thetaS W n : ℝ) : ℂ)‖ * ‖χ (n : ZMod q)‖
            * ‖((n:ℂ)^(-ρ))‖ := by simp only [norm_mul]
      _ ≤ (n:ℝ) * (n:ℝ) * 1 * (n:ℝ) ^ (|ρ.re|) := by gcongr
      _ ≤ (n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) := by
            rw [show (n:ℝ) * (n:ℝ) * 1 * (n:ℝ) ^ (|ρ.re|)
                  = (n:ℝ)^2 * (n:ℝ) ^ (|ρ.re|) by ring]
            calc (n:ℝ)^2 * (n:ℝ) ^ (|ρ.re|)
                ≤ (n:ℝ)^(Nat.ceil (2 + |ρ.re|)) * (n:ℝ)^(Nat.ceil (2 + |ρ.re|)) := by
                  apply mul_le_mul (pow_le_pow_right₀ hn1 hK2) _
                    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg (Nat.cast_nonneg n) _)
                  rw [← Real.rpow_natCast]
                  exact Real.rpow_le_rpow_of_exponent_le hn1 hKs
              _ = (n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) := by rw [Nat.two_mul, pow_add]

/-- Absolute convergence of the smoothed detector series: for `t > 0` and `U > 0` the terms
`a_n χ(n) n^{-ρ} e^{-nt}` are summable. -/
lemma summable_detCoeff_mul_exp {q : ℕ} [NeZero q] (U V W : ℝ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) {t : ℝ} (hU : 0 < U) (ht : 0 < t) :
    Summable (fun n : ℕ => detCoeff q U V W χ ρ n * ((Real.exp (-(n:ℝ)*t) : ℝ) : ℂ)) := by
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0, Real.exp_lt_one_iff]; linarith
  refine Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) (2 * Nat.ceil (2 + |ρ.re|)) hr1)
    (fun n => ?_)
  have hnorm1 : ‖(((Real.exp (-(n:ℝ)*t) : ℝ)) : ℂ)‖ = Real.exp (-(n:ℝ)*t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hnorm2 : ‖(n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) * Real.exp (-t)^n‖
      = (n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) * Real.exp (-t)^n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg hr0 _))]
  have hexp : Real.exp (-(n:ℝ)*t) = Real.exp (-t)^n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  calc ‖detCoeff q U V W χ ρ n * ((Real.exp (-(n:ℝ)*t) : ℝ) : ℂ)‖
      = ‖detCoeff q U V W χ ρ n‖ * Real.exp (-(n:ℝ)*t) := by rw [norm_mul, hnorm1]
    _ ≤ (n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) * Real.exp (-(n:ℝ)*t) :=
          mul_le_mul_of_nonneg_right (norm_detCoeff_le U V W χ ρ hU n) (Real.exp_pos _).le
    _ = (n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) * Real.exp (-t)^n := by rw [hexp]
    _ = ‖(n:ℝ)^(2 * Nat.ceil (2 + |ρ.re|)) * Real.exp (-t)^n‖ := by rw [hnorm2]

/-- **HB §11: termwise split of the zero detector.**  The detector sum `detSum` of HB
(11.8)–(11.10) is the difference of the two single-exponential smoothed Dirichlet sums
`Ssm = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n/X}` and `Sbig = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n𝓛²/U}`
(introduced in `Submission.Work.LinnikAreas.Density4.zeroDetAux`), because the summand of
`detSum` is `detCoeff n · (e^{-n/X} - e^{-n𝓛²/U})`.  Absolute convergence is supplied by
`0 < U`, `0 < L`, `0 < X`. -/
theorem det_split {q : ℕ} [NeZero q] (U V W X L : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hU : 0 < U) (hL : 0 < L) (hX : 0 < X) :
    Work.LinnikAreas.Density4.detSum q U V W X L χ ρ
      = Work.LinnikAreas.Density4.Ssm q U V W X χ ρ
        - Work.LinnikAreas.Density4.Sbig q U V W L χ ρ := by
  have ht1 : 0 < 1/X := div_pos one_pos hX
  have ht2 : 0 < L^2/U := div_pos (pow_pos hL 2) hU
  have hs1 : Summable (fun n : ℕ =>
      detCoeff q U V W χ ρ n * ((Real.exp (-(n:ℝ)/X) : ℝ) : ℂ)) := by
    have := summable_detCoeff_mul_exp (q := q) U V W χ ρ (t := 1/X) hU ht1
    simpa [div_eq_mul_inv] using this
  have hs2 : Summable (fun n : ℕ =>
      detCoeff q U V W χ ρ n * ((Real.exp (-(n:ℝ)*L^2/U) : ℝ) : ℂ)) := by
    have := summable_detCoeff_mul_exp (q := q) U V W χ ρ (t := L^2/U) hU ht2
    simpa [div_eq_mul_inv, mul_assoc] using this
  rw [detSum, Ssm, Sbig]
  rw [← Summable.tsum_sub hs1 hs2]
  apply tsum_congr
  intro n
  simp only [detCoeff, psiS, thetaS, Complex.ofReal_sub]
  ring

end Work.LinnikAreas.Density4
