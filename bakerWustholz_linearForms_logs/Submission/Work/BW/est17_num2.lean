import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_13
import Submission.Work.BW.num_T
import Submission.Work.BW.num_kum
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Pure real arithmetic kernel behind `est17_num2`: the two `z`-terms are matched by the extra
`0.007·P·z·D` in the `1.007` constant; the log-term is absorbed by the `0.001` slack between
`0.203` and `0.204` (using `P = 2^r ≥ 4`); the `2(J+1)`-term splits into the `0.032 S D` slot and
the `kumJ` slot. -/
private lemma est17_num2_arith {P d h S D D0 Tst z N kumJ J T : ℝ}
    (hP : 4 ≤ P) (hd : 1 ≤ d) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hz : 0 ≤ z) (hlogN : 0 ≤ Real.log N)
    (h1 : Real.log N ≤ 0.001 * h * T)
    (h2 : d * h * T ≤ 0.735 * S * D)
    (h3 : 2 * d * h * (D0 + 1) * Real.log 2 ≤ 0.032 * S * D)
    (h4 : 2 * d * J * h * (D0 + 1) * Real.log 2 ≤ kumJ) :
    (P * d - 1) * (h * Tst + 0.203 * S * D / d + Real.log N)
      + (P * d - 1) * (0.007 * z * D / d)
      + P * z * D
      + P * (2 * (J + 1) * d * h * (D0 + 1) * Real.log 2)
    ≤ P * ((1 - 1 / (P * d)) * (d * h * Tst + 0.204 * S * D)
        + 1.007 * z * D + 0.032 * S * D + kumJ) := by
  have hd0 : (0:ℝ) < d := by linarith
  have hP0 : (0:ℝ) < P := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  have hPne : P ≠ 0 := ne_of_gt hP0
  have hPd0 : (0:ℝ) < P * d := mul_pos hP0 hd0
  have hA : (P * d - 1) * (h * Tst) = P * (1 - 1 / (P * d)) * (d * h * Tst) := by
    field_simp
  have hB : (P * d - 1) * (0.203 * S * D / d) = (P - 1 / d) * (0.203 * S * D) := by
    field_simp
  have hC : P * (1 - 1 / (P * d)) * (0.204 * S * D) = (P - 1 / d) * (0.204 * S * D) := by
    field_simp
  have hT4 : (P * d - 1) * (0.007 * z * D / d) = (P - 1 / d) * (0.007 * z * D) := by
    field_simp
  have hT3 : (P * d - 1) * Real.log N ≤ P * (0.000735 * S * D) := by
    have h1' : (P*d - 1) * Real.log N ≤ (P*d) * Real.log N :=
      mul_le_mul_of_nonneg_right (by linarith) hlogN
    have h2' : (P*d) * Real.log N ≤ (P*d) * (0.001 * h * T) :=
      mul_le_mul_of_nonneg_left h1 hPd0.le
    have h3' : (P*d) * (0.001 * h * T) ≤ P * (0.000735 * S * D) := by
      have h := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ P * 0.001)
      nlinarith [h]
    linarith
  have hSD : 0 ≤ S * D := mul_nonneg hS hD
  have hF6 : P * (0.000735 * S * D) ≤ 0.001 * (P - 1 / d) * S * D := by
    have h1d : 1 / d ≤ 1 := by rw [div_le_one hd0]; linarith
    have hle1 : 0.001 * (1/d) ≤ 0.001 := by
      have := mul_le_mul_of_nonneg_left h1d (by norm_num : (0:ℝ) ≤ 0.001)
      linarith
    have hle2 : (0.001:ℝ) ≤ 0.000265 * P := by nlinarith [hP]
    have hkey : 0.000735 * P ≤ 0.001 * (P - 1 / d) := by nlinarith [hle1, hle2]
    nlinarith [mul_le_mul_of_nonneg_right hkey hSD]
  have hT45 : (P * d - 1) * (0.007 * z * D / d) + P * z * D ≤ P * (1.007 * z * D) := by
    rw [hT4]
    have hzD : 0 ≤ z * D := mul_nonneg hz hD
    have hz7 : 0 ≤ 0.007 * z * D := by nlinarith [hzD]
    have hBle : P - 1 / d ≤ P := by
      have : 0 ≤ 1/d := by positivity
      linarith
    have hstep := mul_le_mul_of_nonneg_right hBle hz7
    nlinarith [hstep]
  have hT6 : P * (2 * (J + 1) * d * h * (D0 + 1) * Real.log 2)
      ≤ P * (0.032 * S * D) + P * kumJ := by
    rw [show 2 * (J + 1) * d * h * (D0 + 1) * Real.log 2
        = 2 * d * h * (D0 + 1) * Real.log 2
          + 2 * J * d * h * (D0 + 1) * Real.log 2 from by ring]
    rw [mul_add]
    have h3' := mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ P by linarith)
    have h4' := mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ P by linarith)
    linarith
  have hexp : (P * d - 1) * (h * Tst + 0.203 * S * D / d + Real.log N)
      = (P*d-1)*(h*Tst) + (P*d-1)*(0.203*S*D/d) + (P*d-1)*Real.log N := by ring
  have hexpR : P * ((1 - 1 / (P * d)) * (d * h * Tst + 0.204 * S * D)
        + 1.007 * z * D + 0.032 * S * D + kumJ)
      = P*(1 - 1/(P*d))*(d*h*Tst) + P*(1 - 1/(P*d))*(0.204*S*D)
        + P*(1.007*z*D) + P*(0.032*S*D) + P*kumJ := by ring
  rw [hexp, hexpR]
  linarith [hA, hB, hC, hT3, hF6, hT45, hT6]

/-- `[K:ℚ] ≥ 1`. -/
private lemma est17_num2_one_le_dK (K : Type*) [Field K] [NumberField K] : 1 ≤ dK K := by
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos (R := ℚ) (M := K)
  show 1 ≤ Module.finrank ℚ K
  omega

/-- **Numerical bookkeeping for `est17`.** With `h = acH K b v`, `d = dK K`, `S = acS K r b v`,
`D = acD K σl`, `D₀ = pD0 r d σl`, `D_j = pDj r d σl j`, `z = |s|/2/2^J` and
`N = h(D₀+1)∏_j(D_j+1)`, the total correction
`(2^r d − 1)(h·T* + 0.203·S·D/d + log N) + (2^r d − 1)·0.007·z·D/d + 2^r·z·D
 + 2^r·2(J+1)·d·h·(D₀+1)·log 2`
(with `T* = Tst`) is at most the budget
`2^r((1 − 1/(2^r d))(dhT* + 0.204·S·D) + 1.007·z·D + 0.032·S·D + kumJ)` of BW (17).
Pure real arithmetic.  The `h·T*` terms agree exactly on both sides;
`(2^r d − 1)·log N ≤ 2^r d · log N ≤ 2^r·0.001·(d·h·pT) ≤ 2^r·0.001·0.735·S·D` by `num_13`
clause 4 and `num_T` clause 3, absorbed by the `0.032·S·D` slot together with
`2·d·h·(D₀+1)·log 2 ≤ 0.032·S·D` (`num_kum`); `2·J·d·h·(D₀+1)·log 2 ≤ kumJ` (`num_kum`) covers
the `J`-dependent part; `0.203·(2^r d − 1)/d ≤ 0.204·(2^r d − 1)/d` is strict; and the two `z`-terms
satisfy `(2^r d − 1)·0.007/d ≤ 0.007·2^r`, matching the extra `0.007·2^r·z·D` in the `1.007`
constant. -/
theorem est17_num2 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v L α' σl ι p) (J : ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σl) (s : ℤ) :
    (2 ^ r * (dK K : ℝ) - 1) * ((acH K b v : ℝ) * Tst
        + 0.203 * acS K r b v * acD K σl / (dK K : ℝ)
        + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * ∏ j, ((pDj r (dK K) σl j : ℝ) + 1)))
      + (2 ^ r * (dK K : ℝ) - 1) * (0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ))
      + (2 : ℝ) ^ r * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl
      + (2 : ℝ) ^ r * (2 * ((J : ℝ) + 1) * (dK K : ℝ) * (acH K b v : ℝ)
          * ((pD0 r (dK K) σl : ℝ) + 1) * Real.log 2)
      ≤ (2 : ℝ) ^ r * ((1 - 1 / (2 ^ r * (dK K : ℝ)))
            * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σl)
          + 1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl
          + 0.032 * acS K r b v * acD K σl + kumJ K b v σl J) := by
  have hhr : 2 ≤ r := H.hr
  have hdK1 : 1 ≤ dK K := est17_num2_one_le_dK K
  have hh19 : 19 ≤ acH K b v := (acH_lower H).1
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σl j := fun j => sigma_ge H j
  have hP : (4:ℝ) ≤ (2:ℝ)^r := by
    calc (4:ℝ) = 2^2 := by norm_num
      _ ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) hhr
  have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hdK1
  have hd0 : (0:ℝ) < (dK K : ℝ) := by linarith
  have hS : 0 ≤ acS K r b v := by
    simp only [acS]
    positivity
  have hD : 0 ≤ acD K σl := by
    simp only [acD]
    exact le_of_lt (pD_pos hhr hdK1 σl hσ)
  have hz : 0 ≤ ((|s| : ℤ) : ℝ) / 2 / 2 ^ J := by positivity
  have hN1 : (1:ℝ) ≤ (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
      * ∏ j : Fin r, ((pDj r (dK K) σl j : ℝ) + 1) := by
    have ha : (1:ℝ) ≤ (acH K b v : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 19) hh19)
    have hb : (1:ℝ) ≤ (pD0 r (dK K) σl : ℝ) + 1 := by
      have h : (0:ℝ) ≤ (pD0 r (dK K) σl : ℝ) := Nat.cast_nonneg _
      linarith
    have hc : (1:ℝ) ≤ ∏ j : Fin r, ((pDj r (dK K) σl j : ℝ) + 1) :=
      Finset.one_le_prod₀ (fun j _ => by
        have h : (0:ℝ) ≤ (pDj r (dK K) σl j : ℝ) := Nat.cast_nonneg _
        linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) hc
  have hlogN : 0 ≤ Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
      * ∏ j : Fin r, ((pDj r (dK K) σl j : ℝ) + 1)) := Real.log_nonneg hN1
  have h13 := (num_13 hhr hdK1 hh19 σl hσ 0 (by
      have h : (0:ℝ) ≤ (pT r (dK K) σl : ℝ) := Nat.cast_nonneg _
      push_cast
      exact h) 0 (le_refl 0)).2.2.2
  have hT3' := (num_T hhr hdK1 hh19 σl hσ).2.2.1
  have hk := num_kum hhr hdK1 hh19 σl hσ J
  have h3 : 2 * (dK K : ℝ) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1) * Real.log 2
      ≤ 0.032 * acS K r b v * acD K σl := by
    simp only [acS, acD]
    calc 2 * (dK K : ℝ) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1) * Real.log 2
        = (dK K : ℝ) * (2 * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * Real.log 2) := by ring
      _ ≤ (dK K : ℝ) * (0.032 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σl
            / (dK K : ℝ)) := mul_le_mul_of_nonneg_left hk.1 hd0.le
      _ = 0.032 * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σl := by field_simp
  have h4 : 2 * (dK K : ℝ) * (J : ℝ) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
      * Real.log 2 ≤ kumJ K b v σl J := by
    simp only [kumJ, acS, acD]
    exact hk.2.1
  exact est17_num2_arith (P := (2:ℝ)^r) (d := (dK K : ℝ)) (h := (acH K b v : ℝ))
    (S := acS K r b v) (D := acD K σl) (D0 := (pD0 r (dK K) σl : ℝ)) (Tst := Tst)
    (z := ((|s| : ℤ) : ℝ) / 2 / 2 ^ J) (kumJ := kumJ K b v σl J) (J := (J : ℝ))
    (T := (pT r (dK K) σl : ℝ))
    hP hd1 hS hD hz hlogN h13 hT3' h3 h4

end Work.BW
