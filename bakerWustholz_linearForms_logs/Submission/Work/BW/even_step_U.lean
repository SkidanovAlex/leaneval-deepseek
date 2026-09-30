import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.est16
import Submission.Work.BW.est16_exp_le_evU
import Submission.Work.BW.num_xi
import Submission.Work.BW.split_aux
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.acH_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## The `U`-hypothesis of `extrap_core` in the even step

This node is the `hU` block of `extrap_even_step`: BW's (16) at descent level `J+1` applied to
`f = f^{(J+1)}_{μ'}(·;t)`, with `T* = ξT^{(J)}` and `‖z‖ = R`, `|s| ≤ 4S^{(J)}`.  `est16` supplies
the circle bound with the exponent
`dhT* + 1.055SD + 1.008((‖z‖+|s‖)/2^{J+1})D + kum_{J+1}`, and `est16_exp_le_evU` shows this is
`≤ evU`; the only bookkeeping is `‖z‖ + |s| ≤ R + 4S^{(J)}` and the two range/order hypotheses
`2^{-(J+1)}|s| ≤ 2^r S`, `ξ^{r+1}T^{(J)} ≤ ξT^{(J)} ≤ T`. -/

/-- `d = [K:ℚ] ≥ 1`. -/
private lemma even_step_U_one_le_dK (K : Type*) [Field K] [NumberField K] : 1 ≤ dK K := by
  have h := Module.finrank_pos (R := ℚ) (M := K)
  show 1 ≤ Module.finrank ℚ K
  omega

/-- `a ≤ 4S^{(J)}` implies `a / 2^{J+1} ≤ 2^r S`: the range hypothesis of `(16)` at level `J+1`.
Uses `2ξ^r ≥ 1.07` (`num_xi`), so that `ξ^{-rJ}2^{-J} = (2ξ^r)^{-J} ≤ 1`. -/
private lemma even_step_U_div_two_pow_le {r : ℕ} (hr : 2 ≤ r) {J : ℕ} {a S : ℝ}
    (ha : a ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)) (hS : 0 ≤ S) :
    a / 2 ^ (J + 1) ≤ 2 ^ r * S := by
  have h1 : (1 : ℝ) ≤ 2 * pxi r ^ r := le_trans (by norm_num) (num_xi hr).2.2.2.2
  have hdec : pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ)) ≤ 1 := by
    have key : ((2 * pxi r ^ r) ^ J)⁻¹
        = pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ)) := by
      rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, mul_pow, mul_inv_rev, ← pow_mul]
    rw [← key]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have hpos : (0 : ℝ) < 2 ^ (J + 1) := by positivity
  have hmain : 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) / 2 ^ (J + 1)
      = 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ))) * S := by
    have h2 : (2 : ℝ) ^ (J + 1) = 2 ^ J * 2 := by ring
    have hz2 : (2 : ℝ) ^ (-(J : ℤ)) = ((2 : ℝ) ^ J)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have hxi : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (r * J))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [h2, hz2, hxi]
    field_simp
    ring
  have h2r : (2 : ℝ) ≤ 2 ^ r := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ r)
    simpa using h
  calc a / 2 ^ (J + 1)
      ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) / 2 ^ (J + 1) :=
        div_le_div_of_nonneg_right ha hpos.le
    _ = 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (2 : ℝ) ^ (-(J : ℤ))) * S := hmain
    _ ≤ 2 * 1 * S := by nlinarith [hdec, hS]
    _ = 2 * S := by ring
    _ ≤ 2 ^ r * S := mul_le_mul_of_nonneg_right h2r hS

-- NOTE (dependency status).  The proof below is complete (`est16_exp_le_evU` + `est16`); the only
-- reason the module is not yet axiom-clean is that `est16` uses `est15`, whose file still carries a
-- `sorry`, and `est15`/`est13` use `ulcm_le_three_pow`, which still carries the Hanson `sorry`s.
-- Nothing in this file touches those holes: it uses only the *statements* of `est16`
-- (BW (16) at level `J+1`) and of the arithmetic lemma `est16_exp_le_evU`, as intended.

/-- The `U`-hypothesis of `extrap_core` in the even step: `(16)` at level `J+1` applied to
`f = f^{(J+1)}_{μ'}(·;t)` gives the circle bound with exponent `evU`, the only new ingredient being
`‖z‖ + |s| ≤ R + 4S^{(J)}` (from `‖z‖ = R = 7.2S'` and `|s| ≤ 4S^{(J)}`). -/
theorem even_step_U {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J + 1 ≤ pI r (dK K)) (μ' : Fin r → ℕ)
    (s : ℤ) (hs : ((|s| : ℤ) : ℝ) ≤ 4 * SJ K r b v J) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r ^ (r + 1) * TJ K σ J)
    (hne : acg φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ) ≠ 0) :
    ∀ z : ℂ, ‖z‖ = evR r J (acS K r b v) →
      ‖acf φ α b k L ι v σ p (J + 1) μ' t0 t z‖ ≤
        ‖acf φ α b k L ι v σ p (J + 1) μ' t0 t (s : ℂ)‖ * Real.exp (evU r (dK K) (acH K b v) σ J) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := even_step_U_one_le_dK K
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hDnn : 0 ≤ pD r (dK K) σ := (pD_pos hr hd σ hσ).le
  have hxi0 : 0 < pxi r := pxi_pos hr
  have hxi1 : pxi r ≤ 1 := pxi_le_one r
  have hTnn : (0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := Nat.cast_nonneg _
  have hTJ0 : 0 ≤ TJ K σ J := by
    rw [TJ]
    exact mul_nonneg (pow_nonneg hxi0.le _) hTnn
  have hTleT : pxi r * TJ K σ J ≤ acT K σ := by
    have hpow : pxi r ^ (r * J) ≤ 1 := pow_le_one₀ hxi0.le hxi1
    have hmul : pxi r * pxi r ^ (r * J) ≤ 1 := by
      calc pxi r * pxi r ^ (r * J) ≤ 1 * 1 :=
            mul_le_mul hxi1 hpow (pow_nonneg hxi0.le _) (by norm_num)
        _ = 1 := by ring
    rw [TJ, acT]
    calc pxi r * (pxi r ^ (r * J) * (pT r (dK K) σ : ℝ))
        = (pxi r * pxi r ^ (r * J)) * (pT r (dK K) σ : ℝ) := by ring
      _ ≤ 1 * (pT r (dK K) σ : ℝ) := mul_le_mul_of_nonneg_right hmul hTnn
      _ = (pT r (dK K) σ : ℝ) := one_mul _
  have htr : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ pxi r * TJ K σ J := by
    refine le_trans ht ?_
    have hpow : pxi r ^ (r + 1) ≤ pxi r := by
      rw [pow_succ]
      calc pxi r ^ r * pxi r ≤ 1 * pxi r :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hxi0.le hxi1) hxi0.le
        _ = pxi r := one_mul _
    exact mul_le_mul_of_nonneg_right hpow hTJ0
  have hSnn : 0 ≤ acS K r b v := by
    change (0 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ)
    positivity
  have hs16 : ((|s| : ℤ) : ℝ) / 2 ^ (J + 1) ≤ 2 ^ r * acS K r b v := by
    have ha : ((|s| : ℤ) : ℝ) ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * acS K r b v) := by
      simpa only [SJ] using hs
    have h2 := even_step_U_div_two_pow_le (r := r) hr (J := J) (a := ((|s| : ℤ) : ℝ))
      (S := acS K r b v) ha hSnn
    have h2r : (2 : ℝ) ≤ 2 ^ r := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ r)
      simpa using h
    nlinarith [h2, hSnn, h2r]
  intro z hz
  have h16 := est16 H (J + 1) hJ μ' (pxi r * TJ K σ J) hTleT t0 t htr s hs16 hne z
  refine le_trans h16 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
  have hz' : ‖z‖ = evR r J (pS r (dK K) (acH K b v) : ℝ) := hz
  have hsz : ((|s| : ℤ) : ℝ)
      ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r (dK K) (acH K b v) : ℝ)) := by
    simpa only [SJ, acS] using hs
  have h := est16_exp_le_evU (r := r) (hr := hr) (d := dK K) (h := acH K b v) (J := J)
    (σ := σ) (z := z) (sz := ((|s| : ℤ) : ℝ)) hz' hsz (by positivity) hDnn
  simp only [TJ, kumJ] at h ⊢
  exact h

end Work.BW
