import Mathlib
import Submission.Work.BMF.VKF.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKF

open Work.BMF.liouville

noncomputable section

/-- `logK lam` is `log (dKappa lam)`, expanded: the logarithm of the accumulated constant
`κ = (5r)^k · s^{h-1} · 2^{(g+3)(g-h+1)} · stechF k r' · stechF g s'`. -/
def logK (lam : ℝ) : ℝ :=
  (dK lam : ℝ) * Real.log (5 * (dR lam : ℝ))
    + ((dH lam - 1 : ℕ) : ℝ) * Real.log ((dS lam : ℝ))
    + (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2
    + sK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ))
        * (1 + Real.log (dK lam : ℝ))
    + sK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ))
        * (1 + Real.log (dG lam : ℝ))

/-- Taking logarithms in the definition of `dKappa`. -/
lemma log_dKappa (lam : ℝ) (hlam : 13 / 5 ≤ lam) : Real.log (dKappa lam) = logK lam := by
  have hR : (0 : ℝ) < (dR lam : ℝ) := by
    have := dR_pos lam hlam; exact_mod_cast (by omega : 0 < dR lam)
  have hS : (0 : ℝ) < (dS lam : ℝ) := by
    have := dS_pos lam hlam; exact_mod_cast (by omega : 0 < dS lam)
  have hK : (0 : ℝ) < (dK lam : ℝ) := by
    have := dK_pos lam hlam; exact_mod_cast (by omega : 0 < dK lam)
  have hG : (0 : ℝ) < (dG lam : ℝ) := by
    have := dG_pos lam hlam; exact_mod_cast (by omega : 0 < dG lam)
  have hp5r : (0 : ℝ) < 5 * (dR lam : ℝ) := by linarith
  have hB : (0 : ℝ) < (dS lam : ℝ) ^ (dH lam - 1) := pow_pos hS _
  have hC : (0 : ℝ) < (2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1)) := pow_pos (by norm_num) _
  have hD : (0 : ℝ) < stechF (dK lam) (dRp lam) := stechF_pos _ _
  have hE : (0 : ℝ) < stechF (dG lam) (dSp lam) := stechF_pos _ _
  rw [dKappa]
  rw [Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul,
      Real.log_pow, Real.log_pow, Real.log_pow]
  · simp only [stechF, Real.log_exp]
    rw [logK]
    simp only [sK]
  all_goals positivity

/-- The three elementary terms of `log κ` fit in `6rs`. -/
private lemma priv_elem (lam : ℝ) (hlam : 13 / 5 ≤ lam)
    (hr : 300 * lam ^ 2 ≤ ((dR lam : ℕ) : ℝ))
    (hs : 200 * lam ^ 2 ≤ ((dS lam : ℕ) : ℝ))
    (hk : ((dK lam : ℕ) : ℝ) ≤ 5 * lam + 2)
    (hg : ((dG lam : ℕ) : ℝ) ≤ 5 * lam + 1) :
    (dK lam : ℝ) * Real.log (5 * ((dR lam : ℕ) : ℝ))
      + ((dH lam - 1 : ℕ) : ℝ) * Real.log ((dS lam : ℕ) : ℝ)
      + (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2
      ≤ 6 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
  have hr0 : (0 : ℝ) < (dR lam : ℝ) := by nlinarith [hr, hlam]
  have hs0 : (0 : ℝ) < (dS lam : ℝ) := by nlinarith [hs, hlam]
  have hk0 : (0 : ℝ) ≤ (dK lam : ℝ) := Nat.cast_nonneg _
  have hT1 : (dK lam : ℝ) * Real.log (5 * ((dR lam : ℕ) : ℝ))
      ≤ 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
    have hlog1 : Real.log (5 * (dR lam : ℝ)) ≤ 5 * (dR lam : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 * (dR lam : ℝ) by linarith)
      linarith
    have h5k : 5 * (dK lam : ℝ) ≤ 2 * (dS lam : ℝ) := by
      nlinarith [hk, hs, hlam, sq_nonneg (lam - 13 / 5)]
    calc (dK lam : ℝ) * Real.log (5 * ((dR lam : ℕ) : ℝ))
        ≤ (dK lam : ℝ) * (5 * (dR lam : ℝ)) := mul_le_mul_of_nonneg_left hlog1 hk0
      _ = 5 * (dK lam : ℝ) * (dR lam : ℝ) := by ring
      _ ≤ 2 * (dS lam : ℝ) * (dR lam : ℝ) := mul_le_mul_of_nonneg_right h5k hr0.le
      _ = 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by ring
  have hT2 : ((dH lam - 1 : ℕ) : ℝ) * Real.log ((dS lam : ℕ) : ℝ)
      ≤ 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
    have hS1 : (1 : ℝ) ≤ (dS lam : ℝ) := by nlinarith [hs, hlam]
    have hlog2 : Real.log ((dS lam : ℕ) : ℝ) ≤ (dS lam : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hs0; linarith
    have hlog2' : (0 : ℝ) ≤ Real.log ((dS lam : ℕ) : ℝ) := Real.log_nonneg hS1
    have hdh : ((dH lam - 1 : ℕ) : ℝ) ≤ 2 * (dR lam : ℝ) := by
      have h1 : ((dH lam - 1 : ℕ) : ℝ) ≤ (dH lam : ℝ) := by
        exact_mod_cast (by omega : dH lam - 1 ≤ dH lam)
      have h2 : (dH lam : ℝ) ≤ lam + 1 := dH_le lam (by linarith)
      have h3 : lam + 1 ≤ 2 * (dR lam : ℝ) := by
        nlinarith [hr, hlam, sq_nonneg (lam - 13 / 5)]
      linarith
    calc ((dH lam - 1 : ℕ) : ℝ) * Real.log ((dS lam : ℕ) : ℝ)
        ≤ (2 * (dR lam : ℝ)) * Real.log ((dS lam : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdh hlog2'
      _ ≤ (2 * (dR lam : ℝ)) * (dS lam : ℝ) := mul_le_mul_of_nonneg_left hlog2 (by linarith)
      _ = 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by ring
  have hT3 : (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2
      ≤ 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
    have hlog3 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hlog3' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hcast : (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) ≤ (5 * lam + 4) * (5 * lam + 2) := by
      have h1 : ((dG lam + 3 : ℕ) : ℝ) ≤ 5 * lam + 4 := by
        have h := hg; push_cast; linarith
      have h2 : ((dG lam - dH lam + 1 : ℕ) : ℝ) ≤ 5 * lam + 2 := by
        have hle : dG lam - dH lam + 1 ≤ dG lam + 1 := by omega
        have h2' : ((dG lam + 1 : ℕ) : ℝ) ≤ 5 * lam + 2 := by push_cast; linarith
        exact le_trans (by exact_mod_cast hle) h2'
      have h3 : (0 : ℝ) ≤ ((dG lam + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ ((dG lam - dH lam + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ)
          = ((dG lam + 3 : ℕ) : ℝ) * ((dG lam - dH lam + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (5 * lam + 4) * (5 * lam + 2) := by nlinarith [h1, h2, h3, h4]
    have hprod : (300 * lam ^ 2) * (200 * lam ^ 2) ≤ ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) :=
      mul_le_mul hr hs (by positivity) hr0.le
    calc (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2
        ≤ ((5 * lam + 4) * (5 * lam + 2)) * 1 :=
          mul_le_mul hcast hlog3 hlog3' (by nlinarith [hlam])
      _ ≤ 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
          nlinarith [hprod, hlam, sq_nonneg (lam - 13 / 5)]
  nlinarith [hT1, hT2, hT3]

/-- The first Stechkin term of `log κ` is at most a `50·sK` fraction of `2rs`. -/
private lemma priv_stech1 (lam : ℝ) (hlam : 13 / 5 ≤ lam)
    (hrd : ((dR lam : ℕ) : ℝ) = ((dK lam : ℕ) : ℝ) * ((dRp lam : ℕ) : ℝ))
    (hk : ((dK lam : ℕ) : ℝ) ≤ 5 * lam + 2)
    (hrp : ((dRp lam : ℕ) : ℝ) ≤ 61 * lam)
    (hs : 200 * lam ^ 2 ≤ ((dS lam : ℕ) : ℝ)) :
    sK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ))
        * (1 + Real.log (dK lam : ℝ))
      ≤ 100 * sK * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (dK lam : ℝ) := by
    rw [dK_eq]; have h := dG_ge lam; linarith
  have hk0 : (0 : ℝ) < (dK lam : ℝ) := by linarith
  have hsK : (0 : ℝ) ≤ sK := sK_nonneg
  have hlogk : Real.log (dK lam : ℝ) ≤ 5 * lam + 1 := by
    have h2 : (0 : ℝ) < 5 * lam + 2 := by linarith
    have h3 : Real.log (dK lam : ℝ) ≤ Real.log (5 * lam + 2) := Real.log_le_log hk0 hk
    have h4 : Real.log (5 * lam + 2) ≤ 5 * lam + 2 - 1 := Real.log_le_sub_one_of_pos h2
    linarith
  have hnn2 : (0 : ℝ) ≤ 1 + Real.log (dK lam : ℝ) := by
    have h := Real.log_nonneg hk1; linarith
  have hkplus : ((dK lam : ℕ) : ℝ) + ((dRp lam : ℕ) : ℝ) ≤ 66 * lam + 2 := by
    linarith [hk, hrp]
  have hprod : (((dK lam : ℕ) : ℝ) + ((dRp lam : ℕ) : ℝ)) * (1 + Real.log (dK lam : ℝ))
      ≤ 100 * (dS lam : ℝ) := by
    have h1 : 1 + Real.log (dK lam : ℝ) ≤ 5 * lam + 2 := by linarith
    have h2 : (0 : ℝ) ≤ 66 * lam + 2 := by linarith
    have h3 : ((66 * lam + 2) * (5 * lam + 2) : ℝ) ≤ 100 * (dS lam : ℝ) := by
      nlinarith [hs, hlam, sq_nonneg (lam - 13 / 5)]
    exact le_trans (mul_le_mul hkplus h1 hnn2 h2) h3
  have hnn : (0 : ℝ) ≤ sK * (dK lam : ℝ) * (dRp lam : ℝ) :=
    mul_nonneg (mul_nonneg hsK (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc sK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ))
        * (1 + Real.log (dK lam : ℝ))
      = (sK * (dK lam : ℝ) * (dRp lam : ℝ))
          * ((((dK lam : ℕ) : ℝ) + ((dRp lam : ℕ) : ℝ)) * (1 + Real.log (dK lam : ℝ))) := by
        ring
    _ ≤ (sK * (dK lam : ℝ) * (dRp lam : ℝ)) * (100 * (dS lam : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod hnn
    _ = 100 * sK * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by rw [hrd]; ring

/-- The second Stechkin term of `log κ` is at most a `50·sK` fraction of `2rs`. -/
private lemma priv_stech2 (lam : ℝ) (hlam : 13 / 5 ≤ lam)
    (hrd : ((dR lam : ℕ) : ℝ) = ((dK lam : ℕ) : ℝ) * ((dRp lam : ℕ) : ℝ))
    (hsd : ((dS lam : ℕ) : ℝ) = ((dG lam : ℕ) : ℝ) * ((dSp lam : ℕ) : ℝ))
    (hg : ((dG lam : ℕ) : ℝ) ≤ 5 * lam + 1)
    (hsp : ((dSp lam : ℕ) : ℝ) ≤ 41 * lam)
    (hr : 300 * lam ^ 2 ≤ ((dR lam : ℕ) : ℝ)) :
    sK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ))
        * (1 + Real.log (dG lam : ℝ))
      ≤ 100 * sK * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by
  have hg1 : (1 : ℝ) ≤ (dG lam : ℝ) := by have h := dG_ge lam; linarith
  have hg0 : (0 : ℝ) < (dG lam : ℝ) := by linarith
  have hsK : (0 : ℝ) ≤ sK := sK_nonneg
  have hlogg : Real.log (dG lam : ℝ) ≤ 5 * lam := by
    have h2 : (0 : ℝ) < 5 * lam + 1 := by linarith
    have h3 : Real.log (dG lam : ℝ) ≤ Real.log (5 * lam + 1) := Real.log_le_log hg0 hg
    have h4 : Real.log (5 * lam + 1) ≤ 5 * lam + 1 - 1 := Real.log_le_sub_one_of_pos h2
    linarith
  have hnn2 : (0 : ℝ) ≤ 1 + Real.log (dG lam : ℝ) := by
    have h := Real.log_nonneg hg1; linarith
  have hgplus : ((dG lam : ℕ) : ℝ) + ((dSp lam : ℕ) : ℝ) ≤ 46 * lam + 1 := by
    linarith [hg, hsp]
  have hprod : (((dG lam : ℕ) : ℝ) + ((dSp lam : ℕ) : ℝ)) * (1 + Real.log (dG lam : ℝ))
      ≤ 100 * ((dR lam : ℕ) : ℝ) := by
    have h1 : 1 + Real.log (dG lam : ℝ) ≤ 5 * lam + 1 := by linarith
    have h2 : (0 : ℝ) ≤ 46 * lam + 1 := by linarith
    have h3 : ((46 * lam + 1) * (5 * lam + 1) : ℝ) ≤ 100 * ((dR lam : ℕ) : ℝ) := by
      nlinarith [hr, hlam, sq_nonneg (lam - 13 / 5)]
    exact le_trans (mul_le_mul hgplus h1 hnn2 h2) h3
  have hnn : (0 : ℝ) ≤ sK * (dG lam : ℝ) * (dSp lam : ℝ) :=
    mul_nonneg (mul_nonneg hsK (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc sK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ))
        * (1 + Real.log (dG lam : ℝ))
      = (sK * (dG lam : ℝ) * (dSp lam : ℝ))
          * ((((dG lam : ℕ) : ℝ) + ((dSp lam : ℕ) : ℝ)) * (1 + Real.log (dG lam : ℝ))) := by
        ring
    _ ≤ (sK * (dG lam : ℝ) * (dSp lam : ℝ)) * (100 * ((dR lam : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod hnn
    _ = 100 * sK * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) := by rw [hsd]; ring

/-- The accumulated constant `κ` of the Ford §5 extraction is dominated by the target constant
`dC = exp(1000 + 100K)` once raised to the power `1/(2rs)`: `κ^{1/(2rs)} ≤ dC`.

Proof route: take logarithms.  `log κ = k·log(5r) + (h-1)·log s + (g+3)(g-h+1)·log 2
+ K·k·r'·(k+r')(1+log k) + K·g·s'·(g+s')(1+log g)` with `K = stechK = sK` and
`r = k r'`, `s = g s'`.  The first three terms are at most `6rs`, and each Stechkin term is at
most `100·sK·r·s`; hence `log κ ≤ (6 + 200·sK)·r·s ≤ (1000 + 100·sK)·(2rs)`, which is `log dC`
multiplied by `2rs`. -/
theorem vkf_kappa (lam : ℝ) (hlam : 13 / 5 ≤ lam)
    (hr : 300 * lam ^ 2 ≤ ((Work.BMF.VKF.dR lam : ℕ) : ℝ))
    (hs : 200 * lam ^ 2 ≤ ((Work.BMF.VKF.dS lam : ℕ) : ℝ))
    (hk : ((Work.BMF.VKF.dK lam : ℕ) : ℝ) ≤ 5 * lam + 2)
    (hg : ((Work.BMF.VKF.dG lam : ℕ) : ℝ) ≤ 5 * lam + 1)
    (hk2 : ((Work.BMF.VKF.dK lam : ℕ) : ℝ) = ((Work.BMF.VKF.dG lam : ℕ) : ℝ) + 1)
    (hrd : ((Work.BMF.VKF.dR lam : ℕ) : ℝ)
        = ((Work.BMF.VKF.dK lam : ℕ) : ℝ) * ((Work.BMF.VKF.dRp lam : ℕ) : ℝ))
    (hsd : ((Work.BMF.VKF.dS lam : ℕ) : ℝ)
        = ((Work.BMF.VKF.dG lam : ℕ) : ℝ) * ((Work.BMF.VKF.dSp lam : ℕ) : ℝ))
    (hrp : ((Work.BMF.VKF.dRp lam : ℕ) : ℝ) ≤ 61 * lam)
    (hsp : ((Work.BMF.VKF.dSp lam : ℕ) : ℝ) ≤ 41 * lam)
    (hh : lam ≤ ((Work.BMF.VKF.dH lam : ℕ) : ℝ)) :
    Work.BMF.VKF.dKappa lam ^
        ((1 : ℝ) / (2 * ((Work.BMF.VKF.dR lam : ℕ) : ℝ) * ((Work.BMF.VKF.dS lam : ℕ) : ℝ)))
      ≤ Work.BMF.VKF.dC := by
  have hr0 : (0 : ℝ) < (dR lam : ℝ) := by nlinarith [hr, hlam]
  have hs0 : (0 : ℝ) < (dS lam : ℝ) := by nlinarith [hs, hlam]
  have hden : (0 : ℝ) < 2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ) :=
    mul_pos (mul_pos (by norm_num) hr0) hs0
  have hL := log_dKappa lam hlam
  have he := priv_elem lam hlam hr hs hk hg
  have h1 := priv_stech1 lam hlam hrd hk hrp hs
  have h2 := priv_stech2 lam hlam hrd hsd hg hsp hr
  have hstep1 : logK lam ≤ (6 + 200 * sK) * (((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ)) := by
    rw [logK]
    nlinarith [he, h1, h2]
  have hstep2 : (6 + 200 * sK) * (((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ))
      ≤ (1000 + 100 * sK) * (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ)) := by
    nlinarith [hden.le]
  have hh1K : logK lam ≤ (1000 + 100 * sK) * (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ)) :=
    le_trans hstep1 hstep2
  have hmainK : logK lam * (1 / (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ)))
      ≤ 1000 + 100 * sK := by
    rw [← div_eq_mul_one_div]
    exact (div_le_iff₀ hden).mpr hh1K
  have hkpos := dKappa_pos lam hlam
  rw [Real.rpow_def_of_pos hkpos, hL, dC]
  exact Real.exp_le_exp.mpr hmainK

end

end Work.BMF.VKF
