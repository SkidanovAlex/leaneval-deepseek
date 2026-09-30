import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_17

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## Term count of the p. 48 expansion

BW §17, closing sentence of p. 49 (the last `0.027` of the `0.282`): a sum with at most
`(m+1)^n` normalized terms (`m ≤ T`, one index `a` and `n` indices `t'_i` with
`a + Σ t'_i = m`), each bounded by `exp (0.255·(1/d)SD + …)`, is bounded by the same
quantity with `0.255` raised to `0.282`; equivalently
`(m+1)^n ≤ exp (0.027·(1/d)·S·D) = exp (0.432·r·h·D)`.

The arithmetic: `log (m+1) ≤ log (T+1) ≤ 2.16 rD`, `n ≤ h/5`, and `0.027·16/5 = 0.0864 = 0.432/5`.
The only analytic input is `log y ≤ 2√y`; the only size input is `D ≥ 268` (from `pD_low`),
which gives `rD ≥ 536 ≥ 100`. -/

/-- `log y ≤ 2√y` (from `Real.log_le_rpow_div` at `ε = 1/2`). -/
private lemma log_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_rpow_div hy (show (0:ℝ) < 1/2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have h' : Real.sqrt y / (1/2) = 2 * Real.sqrt y := by ring
  linarith [h, h'.le, h'.ge]

/-- `log (11.75 x + 1) ≤ 2.16 x` for `x ≥ 100`. -/
private lemma log_1175_le {x : ℝ} (hx : 100 ≤ x) : Real.log (11.75 * x + 1) ≤ 2.16 * x := by
  have hx0 : 0 < x := by linarith
  have h12 : 11.75 * x + 1 ≤ 12 * x := by linarith
  have hpos : (0:ℝ) < 11.75 * x + 1 := by linarith
  have h1 : Real.log (11.75 * x + 1) ≤ Real.log (12 * x) := Real.log_le_log hpos h12
  have h2 : Real.log (12 * x) ≤ 2 * Real.sqrt (12 * x) := log_le_two_sqrt (by linarith)
  have h3 : Real.sqrt (12 * x) ≤ 1.08 * x := by
    rw [Real.sqrt_le_left (by linarith : (0:ℝ) ≤ 1.08 * x)]
    nlinarith
  linarith

/-- `D ≥ 268` (`≥ 2·4·32³·(4/3)` actually) from `σ_j ≥ 1/d`. -/
private lemma pD_ge_268 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d:ℝ) ≤ σ j) : (268:ℝ) ≤ pD r d σ := by
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlog : (4/3:ℝ) ≤ Real.log (2*r*d) := log_2rd_ge hr hd
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    have h1 : (2:ℝ)^(2:ℕ) ≤ (r:ℝ)^(2:ℕ) := pow_le_pow_left₀ (by norm_num) hrR 2
    have h2 : (r:ℝ)^(2:ℕ) ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) hr
    calc (4:ℝ) = (2:ℝ)^(2:ℕ) := by norm_num
      _ ≤ (r:ℝ)^(2:ℕ) := h1
      _ ≤ (r:ℝ)^r := h2
  have h32 : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 32) (by omega : 3 ≤ r + 1)
    norm_num at h
    exact h
  have hD := pD_low hr hd σ hσ
  have hkey : 2 * 4 * 32768 * 1 * (4/3 : ℝ)
      ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2*r*d) := by
    gcongr
  linarith [hD, hkey]

/-- The general arithmetic form of the term count, in the notation `pD`, `pS`, `pT`. -/
private lemma est21_aux {r d h n : ℕ} {σ : Fin r → ℝ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h)
    (hn : 5 * n ≤ h) (hσ : ∀ j, 1 / (d:ℝ) ≤ σ j) (m : ℕ) (hm : (m:ℝ) ≤ (pT r d σ : ℝ)) :
    ((m + 1 : ℕ) : ℝ) ^ n ≤
      Real.exp (0.027 * (1 / (d : ℝ)) * (pS r d h : ℝ) * pD r d σ) := by
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hhR : (19:ℝ) ≤ h := by exact_mod_cast hh
  have hnR : (5:ℝ) * n ≤ (h:ℝ) := by exact_mod_cast hn
  have hDpos : (0:ℝ) < pD r d σ := pD_pos hr hd σ hσ
  have hx100 : (100:ℝ) ≤ (r:ℝ) * pD r d σ := by
    have h268 : (268:ℝ) ≤ pD r d σ := pD_ge_268 hr hd σ hσ
    have h := mul_le_mul hrR h268 (by norm_num : (0:ℝ) ≤ 268) (by linarith : (0:ℝ) ≤ (r:ℝ))
    linarith [h]
  have hTle : (pT r d σ : ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by
    have h0 : (0:ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by nlinarith
    simpa only [pT] using Nat.floor_le h0
  set A : ℝ := ((m + 1 : ℕ) : ℝ) with hAdef
  have hAeq : A = (m:ℝ) + 1 := by rw [hAdef]; push_cast; ring
  have hApos : 0 < A := by rw [hAeq]; positivity
  have hm1 : A ≤ 11.75 * (r:ℝ) * pD r d σ + 1 := by
    rw [hAeq]; linarith
  have hlogb : Real.log A ≤ 2.16 * ((r:ℝ) * pD r d σ) := by
    have h1 : Real.log A ≤ Real.log (11.75 * (r:ℝ) * pD r d σ + 1) :=
      Real.log_le_log hApos hm1
    have h2 := log_1175_le hx100
    have heq : 11.75 * ((r:ℝ) * pD r d σ) + 1 = 11.75 * (r:ℝ) * pD r d σ + 1 := by ring
    rw [heq] at h2
    linarith
  have hmain : (n:ℝ) * Real.log A ≤ 0.432 * (r:ℝ) * (h:ℝ) * pD r d σ := by
    have hnle : (n:ℝ) ≤ (h:ℝ) / 5 := by linarith
    have hlpos : 0 ≤ Real.log A := Real.log_nonneg (by rw [hAeq]; linarith)
    have h1 : (n:ℝ) * Real.log A ≤ ((h:ℝ)/5) * Real.log A :=
      mul_le_mul_of_nonneg_right hnle hlpos
    have h2 : ((h:ℝ)/5) * Real.log A ≤ ((h:ℝ)/5) * (2.16 * ((r:ℝ) * pD r d σ)) := by
      apply mul_le_mul_of_nonneg_left hlogb
      linarith
    have h3 : ((h:ℝ)/5) * (2.16 * ((r:ℝ) * pD r d σ)) = 0.432 * (r:ℝ) * (h:ℝ) * pD r d σ := by
      ring
    linarith [h1, h2, h3.le]
  calc A ^ n = Real.exp ((n:ℝ) * Real.log A) := by
        rw [Real.exp_nat_mul, Real.exp_log hApos]
    _ ≤ Real.exp (0.432 * (r:ℝ) * (h:ℝ) * pD r d σ) := Real.exp_le_exp.mpr hmain
    _ = Real.exp (0.027 * (1 / (d:ℝ)) * (pS r d h : ℝ) * pD r d σ) := by
        congr 1
        have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
          simp only [pS]; push_cast; ring
        rw [hS]
        field_simp
        ring

/-- The term count of BW's p. 48 expansion (`taylorC_acf_expand`): the number of pairs
`(a, t') : ℕ × (Fin n → ℕ)` with `a + Σᵢ t'_i = m` is at most `(m+1)^n`, and this is at most
`exp (0.027·(1/d)·S·D)` — the `2^T`-type loss of BW p. 49 (`num_17`: `T log 2 ≤ 0.027·SD/d`).
Used in `est21_l` to raise the `0.255` of `est21_dpoly_diff_norm` to the final `0.282`.
Concretely: `m ≤ T`, `5n ≤ h`, `h ≥ 19`, `σ_j ≥ 1/d`, and `log(11.75 rD + 1) ≤ 2.16 rD`. -/
theorem est21_l_count {K : Type*} [Field K] [NumberField K] {r n : ℕ} {b : Fin n → ℤ} {v : ℕ}
    {σ : Fin r → ℝ} (hr : 2 ≤ r) (hh : 19 ≤ acH K b v) (hn : 5 * n ≤ acH K b v)
    (hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j) (m : ℕ) (hm : m ≤ acT K σ) :
    ((m + 1 : ℕ) : ℝ) ^ n ≤
      Real.exp (0.027 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ) := by
  have hd : 1 ≤ dK K := Module.finrank_pos (R := ℚ) (M := K)
  exact est21_aux (d := dK K) (h := acH K b v) hr hd hh hn hσ m hm

end Work.BW
