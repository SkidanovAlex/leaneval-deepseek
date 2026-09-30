import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_13
import Submission.Work.BW.num_17
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.acH_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The purely real-arithmetic core of (21).  With `H = h`, `S = 16 r d h`, `T = ⌊11.75 r D⌋`,
`D` the parameter of §13, the "non-`X`" part of the estimate
`0.001hT + neD + T log 2 + T log 1.7 + 0.007(X+h)D/d ≤ 0.255 SD/d` reduces (after moving the
`S`-terms whose coefficients differ by `0.146`) to
`0.101 hT + neD + T(log 2 + log 1.7) + 0.007 hD/d ≤ 0.146·16 r hD = 2.336 r hD`.
We use `n ≤ h/5`, `T ≤ 11.75 r D`, `r ≥ 2`, `h ≥ 19`. -/
private lemma key_arith (d H D T r n e l2 l17 q : ℝ)
    (_hd : 1 ≤ d) (hH : 19 ≤ H) (hn : 5*n ≤ H) (hr : 2 ≤ r) (hD : 0 ≤ D)
    (hT : T ≤ 11.75*r*D) (hT0 : 0 ≤ T) (hn0 : 0 ≤ n) (he : e ≤ 2.7182818286)
    (he0 : 0 ≤ e) (hl2 : l2 ≤ 0.6931471808) (_hl20 : 0 ≤ l2) (hl17 : l17 ≤ 0.532)
    (_hl170 : 0 ≤ l17) (hq : q ≤ 1) (_hq0 : 0 ≤ q) :
    0.101*H*T + n*e*D + T*l2 + T*l17 + 0.007*H*D*q ≤ 2.336*r*H*D := by
  have hn0' : (0:ℝ) ≤ n := hn0
  have hH0 : (0:ℝ) ≤ H := by linarith
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hHD : (0:ℝ) ≤ H*D := mul_nonneg hH0 hD
  -- `0.101 H T ≤ 1.18675 r H D`
  have hA : 0.101*H*T ≤ 1.186750*(r*H*D) := by
    have h1 : 0.101*H*T ≤ 0.101*H*(11.75*r*D) :=
      mul_le_mul_of_nonneg_left hT (by nlinarith [hH0])
    nlinarith [h1, hD, hr0, hH0]
  -- `n e D ≤ (e/5) H D ≤ 0.543661 H D`
  have hB : n*e*D ≤ 0.543661*(H*D) := by
    have hn' : n ≤ H/5 := by linarith
    have h1 : n*e ≤ (H/5)*2.7182818286 := by nlinarith [hn', he, hn0', he0, hH0]
    have h2 : n*e*D ≤ (H/5)*2.7182818286*D := mul_le_mul_of_nonneg_right h1 hD
    nlinarith [h2, hHD, hH0, hD]
  -- `T log 2 ≤ 8.1444795 r D`
  have hC : T*l2 ≤ 8.1444795*(r*D) := by
    have h1 : T*l2 ≤ T*0.6931471808 := mul_le_mul_of_nonneg_left hl2 hT0
    have h2 : T*0.6931471808 ≤ (11.75*r*D)*0.6931471808 :=
      mul_le_mul_of_nonneg_right hT (by norm_num)
    nlinarith [h1, h2]
  -- `T log 1.7 ≤ 6.251 r D`
  have hD' : T*l17 ≤ 6.251*(r*D) := by
    have h1 : T*l17 ≤ T*0.532 := mul_le_mul_of_nonneg_left hl17 hT0
    have h2 : T*0.532 ≤ (11.75*r*D)*0.532 := mul_le_mul_of_nonneg_right hT (by norm_num)
    nlinarith [h1, h2]
  -- `0.007 H D q ≤ 0.007 H D`
  have hE : 0.007*H*D*q ≤ 0.007*(H*D) := by
    have h1 : H*D*q ≤ H*D*1 := mul_le_mul_of_nonneg_left hq hHD
    nlinarith [h1]
  -- `H D ≤ r H D / 2` and `14.3954795 r D ≤ 0.8739195 r H D` (from `H ≥ 19`)
  have hS1 : 0.550661*(H*D) ≤ 0.2753305*(r*H*D) := by nlinarith [hHD, hr, hH0, hD]
  have hS2 : 14.3954795*(r*D) ≤ 0.8739195*(r*H*D) := by nlinarith [hD, hr0, hH]
  linarith [hA, hB, hC, hD', hE, hS1, hS2]

theorem est21_dpb_arith {K : Type*} [Field K] [NumberField K] {n r : ℕ} {b : Fin n → ℤ} {v : ℕ}
    {σ : Fin r → ℝ} (hr : 2 ≤ r) (hh : 19 ≤ acH K b v) (h5n : 5 * n ≤ acH K b v)
    (hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j) {X : ℝ} (hX : 0 ≤ X) :
    0.001 * (acH K b v : ℝ) * acT K σ + (n : ℝ) * Real.exp 1 * acD K σ
      + acT K σ * Real.log 2 + acT K σ * Real.log 1.7 + 0.1 * (acH K b v : ℝ) * acT K σ
      + (0.108 * acS K r b v + 0.007 * (X + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ)
      + X * acD K σ + 0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) + 0.002 * X * acD K σ
    ≤ (0.255 / (dK K : ℝ)) * acS K r b v * acD K σ + 1.01 * X * acD K σ := by
  set d : ℝ := (dK K : ℝ) with hd_def
  set H : ℝ := (acH K b v : ℝ) with hH_def
  set D : ℝ := acD K σ with hD_def
  set T : ℝ := acT K σ with hT_def
  set S : ℝ := acS K r b v with hS_def
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ d := by
    rw [hd_def]
    have : (0:ℕ) < dK K := Module.finrank_pos
    exact_mod_cast this
  have hd0 : (0:ℝ) < d := by linarith
  have hH19 : (19:ℝ) ≤ H := by rw [hH_def]; exact_mod_cast hh
  have hn5 : (5:ℝ)*(n:ℝ) ≤ H := by rw [hH_def]; exact_mod_cast h5n
  -- `D ≥ 0`
  have hD0 : (0:ℝ) ≤ D := by
    rw [hD_def]; simp only [acD, pD]
    have hlog : (0:ℝ) ≤ Real.log (2*(r:ℝ)*(dK K:ℝ)) := by
      apply Real.log_nonneg; nlinarith
    have hprod : (0:ℝ) ≤ ∏ j, σ j := by
      apply Finset.prod_nonneg
      intro j _
      have : (0:ℝ) ≤ 1/(dK K:ℝ) := by positivity
      linarith [hσ j]
    have h1 : (0:ℝ) ≤ (r:ℝ)^r := pow_nonneg hr0 r
    have h2 : (0:ℝ) ≤ (32*(dK K:ℝ))^(r+1) := pow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h1) h2) hlog) hprod
  have hT0 : (0:ℝ) ≤ T := by rw [hT_def]; simp only [acT]; positivity
  -- `T ≤ 11.75 r D`
  have hTle : T ≤ 11.75 * (r:ℝ) * D := by
    have h2 : T = ((⌊(11.75:ℝ) * (r:ℝ) * pD r (dK K) σ⌋₊ : ℕ) : ℝ) := by
      simp only [hT_def, acT, pT]
    have hD0' : (0:ℝ) ≤ pD r (dK K) σ := hD0
    rw [h2]
    exact Nat.floor_le (by nlinarith [hD0', hr0])
  -- `S = 16 r d H`
  have hS : S = 16 * (r:ℝ) * d * H := by
    rw [hS_def, hd_def, hH_def]
    simp only [acS, pS]
    push_cast
    ring
  -- the `S`-free part of the left-hand side
  have hkey' : 0.101*H*T + (n:ℝ)*Real.exp 1*D + T*Real.log 2 + T*Real.log 1.7 + 0.007*H*D/d
      ≤ 2.336*(r:ℝ)*H*D := by
    have := key_arith d H D T (r:ℝ) (n:ℝ) (Real.exp 1) (Real.log 2) (Real.log 1.7) (1/d)
      (by linarith) hH19 hn5 hr2 hD0 hTle hT0 (by positivity)
      (le_of_lt Real.exp_one_lt_d9) (le_of_lt (Real.exp_pos 1))
      (le_of_lt Real.log_two_lt_d9) (Real.log_nonneg (by norm_num))
      (le_of_lt num13_log_17_lt) (Real.log_nonneg (by norm_num))
      (by rw [div_le_one hd0]; exact hd1) (by positivity)
    simpa [div_eq_mul_inv] using this
  have hX0 : (0:ℝ) ≤ X := hX
  have hXD : (0:ℝ) ≤ X*D := mul_nonneg hX0 hD0
  -- the `X`-part: `0.007 X D/d + 1.002 X D ≤ 1.01 X D`
  have hXp' : 0.007*X*D/d + 1.002*X*D ≤ 1.01*X*D := by
    have h1 : 0.007*X*D/d ≤ 0.007*X*D := by
      rw [div_le_iff₀ hd0]
      nlinarith [hXD, hd1]
    nlinarith [h1, hXD]
  -- clear denominators from the two parts
  have hkey'' : 0.101*H*T*d + (n:ℝ)*Real.exp 1*D*d + T*Real.log 2*d + T*Real.log 1.7*d + 0.007*H*D
      ≤ 2.336*(r:ℝ)*H*D*d := by
    have h := mul_le_mul_of_nonneg_right hkey' (le_of_lt hd0)
    have h1 : (0.007*H*D/d) * d = 0.007*H*D := by field_simp
    nlinarith [h, h1]
  have hXp'' : 0.007*X*D + 1.002*X*D*d ≤ 1.01*X*D*d := by
    have h := mul_le_mul_of_nonneg_right hXp' (le_of_lt hd0)
    have h1 : (0.007*X*D/d) * d = 0.007*X*D := by field_simp
    nlinarith [h, h1]
  rw [hS]
  field_simp
  linarith [hkey'', hXp'']

end Work.BW
