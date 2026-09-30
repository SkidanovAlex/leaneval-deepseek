import Mathlib
import Submission.Work.BMF.VKF.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKF

/-- The exponential beats the quadratic: `(41/5)·n² ≤ 2^n` for `n ≥ 13`. -/
private lemma pow_key (n : ℕ) (hn : 13 ≤ n) : (41 : ℝ) / 5 * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hm' : (13 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hstep : (41 : ℝ) / 5 * ((m : ℝ) + 1) ^ 2 ≤ 2 * ((41 : ℝ) / 5 * (m : ℝ) ^ 2) := by
      nlinarith [hm', sq_nonneg ((m : ℝ) - 1)]
    calc (41 : ℝ) / 5 * ((m + 1 : ℕ) : ℝ) ^ 2
        = (41 : ℝ) / 5 * ((m : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ 2 * ((41 : ℝ) / 5 * (m : ℝ) ^ 2) := hstep
      _ ≤ 2 * (2 : ℝ) ^ m := by linarith [ih]
      _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring

/-- Parameter bounds for the Ford §5 extraction with `h = ⌈λ⌉`, `g = ⌈5λ⌉`, `k = g+1`,
`r = k⌈300λ²/k⌉`, `s = g⌈200λ²/g⌉`, for `λ ≥ 13/5`.  Elementary consequences of
`Nat.le_ceil`, `Nat.ceil_lt_add_one`, `dK_eq`, `dRp_mul`, `dSp_mul`, `dRp_le`, `dSp_le` in
`Submission.Work.BMF.VKF.defs`; the only mildly non-trivial ones are `dSp ≤ 41λ`
(`200λ²/g + 1 ≤ 41λ` because `g ≥ 5λ`), `13g ≤ r` (because `r ≥ 300λ² ≥ 65λ+13` for `λ ≥ 13/5`)
and `s ≤ 2^g` (`205λ² ≤ 2^{5λ}` for `λ ≥ 13/5`; the ratio is increasing in `λ ≥ 1`). -/
theorem vkf_params (lam : ℝ) (hlam : 13 / 5 ≤ lam) :
    (lam ≤ ((Work.BMF.VKF.dH lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dH lam : ℕ) : ℝ) ≤ lam + 1) ∧
    (Work.BMF.VKF.dH lam ≤ Work.BMF.VKF.dG lam) ∧
    (((Work.BMF.VKF.dG lam : ℕ) : ℝ) ≤ 5 * lam + 1) ∧
    (((Work.BMF.VKF.dK lam : ℕ) : ℝ) = ((Work.BMF.VKF.dG lam : ℕ) : ℝ) + 1) ∧
    (2 * lam + 1 ≤ ((Work.BMF.VKF.dG lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dG lam : ℕ) : ℝ) ≤ 6 * lam + 1) ∧
    (5 * lam ≤ ((Work.BMF.VKF.dK lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dK lam : ℕ) : ℝ) ≤ 5 * lam + 2) ∧
    (300 * lam ^ 2 ≤ ((Work.BMF.VKF.dRp lam : ℕ) : ℝ) * ((Work.BMF.VKF.dK lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dRp lam : ℕ) : ℝ) ≤ 61 * lam) ∧
    (200 * lam ^ 2 ≤ ((Work.BMF.VKF.dSp lam : ℕ) : ℝ) * ((Work.BMF.VKF.dG lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dSp lam : ℕ) : ℝ) ≤ 41 * lam) ∧
    (300 * lam ^ 2 ≤ ((Work.BMF.VKF.dR lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dR lam : ℕ) : ℝ) ≤ 310 * lam ^ 2) ∧
    (200 * lam ^ 2 ≤ ((Work.BMF.VKF.dS lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dS lam : ℕ) : ℝ) ≤ 205 * lam ^ 2) ∧
    (13 * ((Work.BMF.VKF.dG lam : ℕ) : ℝ) ≤ ((Work.BMF.VKF.dR lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dS lam : ℕ) : ℝ) ≤ ((Work.BMF.VKF.dR lam : ℕ) : ℝ)) ∧
    (((Work.BMF.VKF.dS lam : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Work.BMF.VKF.dG lam)) ∧
    (2 ≤ Work.BMF.VKF.dR lam) ∧ (1 ≤ Work.BMF.VKF.dS lam) := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hkpos_nat : 0 < dK lam := by unfold dK; omega
  have hkpos : (0 : ℝ) < (dK lam : ℝ) := by exact_mod_cast hkpos_nat
  have hgpos : (0 : ℝ) < (dG lam : ℝ) := by
    have := dG_ge lam; linarith
  have h1 : lam ≤ ((dH lam : ℕ) : ℝ) := dH_ge lam
  have h2 : ((dH lam : ℕ) : ℝ) ≤ lam + 1 := dH_le lam (by linarith)
  have h3 : dH lam ≤ dG lam := Nat.ceil_mono (by linarith : lam ≤ 5 * lam)
  have h4 : ((dG lam : ℕ) : ℝ) ≤ 5 * lam + 1 := dG_le lam (by linarith)
  have h5 : ((dK lam : ℕ) : ℝ) = ((dG lam : ℕ) : ℝ) + 1 := dK_eq lam
  have h6 : 2 * lam + 1 ≤ ((dG lam : ℕ) : ℝ) := by have := dG_ge lam; linarith
  have h7 : ((dG lam : ℕ) : ℝ) ≤ 6 * lam + 1 := by linarith [h4, hlam]
  have h8 : 5 * lam ≤ ((dK lam : ℕ) : ℝ) := by rw [dK_eq]; have := dG_ge lam; linarith
  have h9 : ((dK lam : ℕ) : ℝ) ≤ 5 * lam + 2 := dK_le lam (by linarith)
  have h10 : 300 * lam ^ 2 ≤ ((dRp lam : ℕ) : ℝ) * ((dK lam : ℕ) : ℝ) :=
    dRp_mul lam (dK_pos lam hlam)
  have h11 : ((dRp lam : ℕ) : ℝ) ≤ 61 * lam := by
    have hle := dRp_le lam (by linarith) hkpos
    have hprod : 300 * lam ^ 2 ≤ 60 * lam * (dK lam : ℝ) := by
      have h : (300 : ℝ) * lam ^ 2 = 60 * lam * (5 * lam) := by ring
      rw [h]; exact mul_le_mul_of_nonneg_left h8 (by linarith)
    have := (div_le_iff₀ hkpos).mpr hprod
    linarith [(by linarith : (1 : ℝ) ≤ lam)]
  have h12 : 200 * lam ^ 2 ≤ ((dSp lam : ℕ) : ℝ) * ((dG lam : ℕ) : ℝ) :=
    dSp_mul lam (dG_pos lam hlam)
  have h13 : ((dSp lam : ℕ) : ℝ) ≤ 41 * lam := by
    have hle := dSp_le lam (by linarith) hgpos
    have hprod : 200 * lam ^ 2 ≤ 40 * lam * (dG lam : ℝ) := by
      have h : (200 : ℝ) * lam ^ 2 = 40 * lam * (5 * lam) := by ring
      rw [h]; exact mul_le_mul_of_nonneg_left (dG_ge lam) (by linarith)
    have := (div_le_iff₀ hgpos).mpr hprod
    linarith [(by linarith : (1 : ℝ) ≤ lam)]
  have hR_eq : ((dR lam : ℕ) : ℝ) = (dK lam : ℝ) * (dRp lam : ℝ) := by
    simp only [dR]; push_cast; ring
  have hS_eq : ((dS lam : ℕ) : ℝ) = (dG lam : ℝ) * (dSp lam : ℝ) := by
    simp only [dS]; push_cast; ring
  have h14 : 300 * lam ^ 2 ≤ ((dR lam : ℕ) : ℝ) := by rw [hR_eq]; nlinarith [h10]
  have h15 : ((dR lam : ℕ) : ℝ) ≤ 310 * lam ^ 2 := by
    rw [hR_eq]
    have hle := dRp_le lam (by linarith) hkpos
    have hfac : (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ) + 1)
        = 300 * lam ^ 2 + (dK lam : ℝ) := by
      have hne : (dK lam : ℝ) ≠ 0 := ne_of_gt hkpos
      field_simp
    calc (dK lam : ℝ) * (dRp lam : ℝ)
        ≤ (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hle hkpos.le
      _ = 300 * lam ^ 2 + (dK lam : ℝ) := hfac
      _ ≤ 300 * lam ^ 2 + (5 * lam + 2) := by linarith [h9]
      _ ≤ 310 * lam ^ 2 := by nlinarith [hlam]
  have h16 : 200 * lam ^ 2 ≤ ((dS lam : ℕ) : ℝ) := by rw [hS_eq]; nlinarith [h12]
  have h17 : ((dS lam : ℕ) : ℝ) ≤ 205 * lam ^ 2 := by
    rw [hS_eq]
    have hle := dSp_le lam (by linarith) hgpos
    have hfac : (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ) + 1)
        = 200 * lam ^ 2 + (dG lam : ℝ) := by
      have hne : (dG lam : ℝ) ≠ 0 := ne_of_gt hgpos
      field_simp
    calc (dG lam : ℝ) * (dSp lam : ℝ)
        ≤ (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hle hgpos.le
      _ = 200 * lam ^ 2 + (dG lam : ℝ) := hfac
      _ ≤ 200 * lam ^ 2 + (5 * lam + 1) := by linarith [h4]
      _ ≤ 205 * lam ^ 2 := by nlinarith [hlam]
  have h18 : 13 * ((dG lam : ℕ) : ℝ) ≤ ((dR lam : ℕ) : ℝ) := by
    have hq : 13 * (5 * lam + 1) ≤ 300 * lam ^ 2 := by nlinarith [hlam]
    linarith [h14, hq, h4]
  have h19 : ((dS lam : ℕ) : ℝ) ≤ ((dR lam : ℕ) : ℝ) := by
    linarith [h17, h14, sq_nonneg lam]
  have h20 : ((dS lam : ℕ) : ℝ) ≤ (2 : ℝ) ^ (dG lam) := by
    have hdg13 : 13 ≤ dG lam := by
      have : (13 : ℝ) ≤ (dG lam : ℝ) := by have := dG_ge lam; linarith
      exact_mod_cast this
    have h25 : 25 * lam ^ 2 ≤ (dG lam : ℝ) ^ 2 := by
      have h := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ 5 * lam) (dG_ge lam)
      nlinarith [h]
    have hpk := pow_key (dG lam) hdg13
    nlinarith [h17, h25, hpk]
  have h21 : 2 ≤ dR lam := by
    have h2 : (2 : ℝ) ≤ (dR lam : ℝ) := by
      have : (2 : ℝ) ≤ 300 * lam ^ 2 := by nlinarith [hlam]
      linarith [h14]
    exact_mod_cast h2
  have h22 : 1 ≤ dS lam := by
    have h2 : (1 : ℝ) ≤ (dS lam : ℝ) := by
      have : (1 : ℝ) ≤ 200 * lam ^ 2 := by nlinarith [hlam]
      linarith [h16]
    exact_mod_cast h2
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22⟩

end Work.BMF.VKF
