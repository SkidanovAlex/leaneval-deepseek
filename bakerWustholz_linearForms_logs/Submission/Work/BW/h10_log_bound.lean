import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.C1_lower
import Submission.Work.BW.TL_bound
import Submission.Work.BW.final_combine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The numerical coefficient `C = 144·2^r·32^{r+1}·r^{r+1}·h·d²·log(2rd)` that appears in the
`hΛ` estimate of BW §21: `9·2^r·S·D = 2·d^r·C·∏σ`. -/
noncomputable def h10C1 (r d h : ℕ) : ℝ :=
  144 * (2:ℝ)^r * (32:ℝ)^(r+1) * (r:ℝ)^(r+1) * (h:ℝ) * (d:ℝ)^2 * Real.log (2*(r:ℝ)*(d:ℝ))

/-- `pxi r = 1 - 0.536/r` is positive for `r ≥ 2`. -/
lemma h10_pxi_pos {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  unfold pxi
  have : (0.536:ℝ)/(r:ℝ) ≤ 0.464 := by rw [div_le_iff₀ hrpos]; nlinarith
  linarith

/-- `r · log(1/pxi r) ≤ 1` for `r ≥ 2`: the Kummer-descent loss `ξ^{-rI}` costs at most a
factor `e^I`. -/
lemma h10_pxi_log_le_one {r : ℕ} (hr : 2 ≤ r) : (r:ℝ) * (-Real.log (pxi r)) ≤ 1 := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hxpos : (0:ℝ) < pxi r := h10_pxi_pos hr
  have hlog : -Real.log (pxi r) = Real.log ((pxi r)⁻¹) := by rw [Real.log_inv]
  rw [hlog]
  have hinv : Real.log ((pxi r)⁻¹) ≤ (pxi r)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_left hinv (le_of_lt hrpos)) ?_
  have key : (r:ℝ) * ((pxi r)⁻¹ - 1) = 0.536 / pxi r := by
    have h1 : (pxi r)⁻¹ - 1 = (1 - pxi r) * (pxi r)⁻¹ := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ (ne_of_gt hxpos)]
    have h2 : (r:ℝ) * (1 - pxi r) = 0.536 := by
      unfold pxi; field_simp; ring
    rw [h1, ← mul_assoc, h2, div_eq_mul_inv]
  rw [key, div_le_one hxpos]
  unfold pxi
  have : (0.536:ℝ)/(r:ℝ) ≤ 0.464 := by rw [div_le_iff₀ hrpos]; nlinarith
  linarith

/-- `log(r!) ≤ r log r`. -/
lemma h10_log_factorial_le (r : ℕ) : Real.log (r.factorial : ℝ) ≤ (r:ℝ) * Real.log r := by
  have hle : ((r.factorial : ℕ) : ℝ) ≤ ((r^r : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le_pow r
  have hle' : (r.factorial : ℝ) ≤ (r:ℝ)^r := by simpa using hle
  have hpos : (0:ℝ) < (r.factorial : ℝ) := by
    have : 0 < r.factorial := Nat.factorial_pos r
    exact_mod_cast this
  calc Real.log (r.factorial : ℝ) ≤ Real.log ((r:ℝ)^r) := Real.log_le_log hpos hle'
    _ = (r:ℝ) * Real.log r := Real.log_pow r r

/-- `∏σ ≥ d^{-r}` when every `σ j ≥ 1/d` and `d ≥ 1`. -/
lemma h10_prod_inv_pow_le {r d : ℕ} (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : ((d:ℝ)^r)⁻¹ ≤ ∏ j, σ j := by
  have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin r => 1/(d:ℝ)) (g := σ)
    (by intro j _; positivity) (by intro j _; exact hσ j)
  have hc : (∏ _j : Fin r, (1/(d:ℝ))) = ((d:ℝ)^r)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div, inv_pow]
  rwa [hc] at h

/-- Numeric core of the `hΛ` check of BW §21. With `S = pS r d h = 16 r d h`,
`D = pD r d σ = 2 r^r (32d)^{r+1} log(2rd) ∏σ`, `ξ = pxi r = 1 − 0.536/r`, `I = pI r d`:
`log N + log(2 ξ^{-rI} S) < log π + v log 2 + 9·2^r S D`
whenever `r ≥ 2`, `d ≥ 1`, `h ≥ 1`, `v log 2 ≤ h + 1`, `σ_j ≥ 1/d`, `N > 0` and
`N ≤ r! (2^v d)^{2r} (∏σ)²`.
This is exactly the rearrangement of `N·2^{-v}·exp(−9·2^r S D) < π/(2ξ^{-rI}S)`, which combined
with BW's hypothesis (10) `log ‖Λ‖ ≤ −9·2^r S D` gives `N·2^{-v}‖Λ‖ < π/𝒮` for `𝒮 = 2ξ^{-rI}S`.
*Proof:* `log N ≤ log r! + 2r(log 2^v + log d) + 2 log(∏σ)`, `log r! ≤ r log r`,
`log(2ξ^{-rI}S) = log 2 + rI log(1/ξ) + log S` with `r log(1/ξ) ≤ 1` hence `rI log(1/ξ) ≤ I`,
`v log 2 ≤ h+1`, `log(∏σ) ≤ max(0, ∏σ)`, `σ_j ≥ 1/d` hence `∏σ ≥ d^{-r}`, and
`9·2^r S D ≥ 288·2^r r^{r+1} 32^{r+1} d² h log(2rd)·max(1, ∏σ)`; each term is then dominated
(`r log r ≤ r²`, `2r(v log2 + log d) ≤ 4rh + 2r log d`, `log(16rdh) ≤ 16rdh`, and the remaining
constants are `≤ 10^8`, below `288·4·8·32768·log 4 ≈ 4.2·10^8`). -/
theorem h10_log_bound {d h r v : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h)
    (hv : (v : ℝ) * Real.log 2 ≤ (h : ℝ) + 1) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (N : ℝ) (hN : 0 < N)
    (hNb : N ≤ (r.factorial : ℝ) * ((2 : ℝ) ^ v * (d : ℝ)) ^ (2 * r) * (∏ j, σ j) ^ 2) :
    Real.log N + Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ)) <
      Real.log Real.pi + (v : ℝ) * Real.log 2 + 9 * 2 ^ r * (pS r d h : ℝ) * pD r d σ := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hhpos : (0:ℝ) < (h:ℝ) := by exact_mod_cast hh
  have hPpos : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => lt_of_lt_of_le (by positivity) (hσ j))
  have hPne : (∏ j, σ j) ≠ 0 := ne_of_gt hPpos
  have hxpos : 0 < pxi r := h10_pxi_pos hr
  have hxne : pxi r ≠ 0 := ne_of_gt hxpos
  have hxlog : (r:ℝ) * (-Real.log (pxi r)) ≤ 1 := h10_pxi_log_le_one hr
  have hSpos : (0:ℝ) < (pS r d h : ℝ) := by rw [pS]; push_cast; positivity
  have hSpush : (pS r d h : ℝ) = 16*(r:ℝ)*(d:ℝ)*(h:ℝ) := by rw [pS]; push_cast; ring
  -- Step 1: bound `log N` using the explicit upper bound for `N`.
  have hlogM : Real.log ((r.factorial : ℝ) * ((2:ℝ)^v * (d:ℝ))^(2*r) * (∏ j, σ j)^2)
      = Real.log (r.factorial : ℝ) + 2*(r:ℝ)*((v:ℝ)*Real.log 2 + Real.log (d:ℝ))
        + 2*Real.log (∏ j, σ j) := by
    rw [Real.log_mul, Real.log_mul, Real.log_pow, Real.log_pow, Real.log_mul, Real.log_pow]
    · push_cast; ring
    all_goals positivity
  have hNle : Real.log N ≤ Real.log (r.factorial : ℝ)
        + 2*(r:ℝ)*((v:ℝ)*Real.log 2 + Real.log (d:ℝ)) + 2*Real.log (∏ j, σ j) :=
    le_trans (Real.log_le_log hN hNb) hlogM.le
  -- Step 2: bound `log(2 ξ^{-rI} S) ≤ log 2 + I + log S ≤ log 2 + 50 log(2rd) + log S`.
  have hlogX : Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ))
      ≤ Real.log 2 + 50 * Real.log (2*(r:ℝ)*(d:ℝ)) + Real.log (pS r d h : ℝ) := by
    have hxpowne : pxi r ^ (-((r * pI r d : ℕ) : ℤ)) ≠ 0 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_ne_zero (pow_ne_zero _ hxne)
    have h1a : Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ))
        = Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ))) + Real.log (pS r d h : ℝ) :=
      Real.log_mul (by positivity) (ne_of_gt hSpos)
    have h1b : Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)))
        = Real.log 2 + Real.log (pxi r ^ (-((r * pI r d : ℕ) : ℤ))) :=
      Real.log_mul (by norm_num) hxpowne
    have h2 : Real.log (pxi r ^ (-((r * pI r d : ℕ) : ℤ))) ≤ (pI r d : ℝ) := by
      have hz : Real.log (pxi r ^ (-((r * pI r d : ℕ) : ℤ)))
          = (pI r d : ℝ) * ((r:ℝ) * (-Real.log (pxi r))) := by
        rw [Real.log_zpow]; push_cast; ring
      rw [hz]
      calc (pI r d : ℝ) * ((r:ℝ) * (-Real.log (pxi r))) ≤ (pI r d : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hxlog (by positivity)
        _ = (pI r d : ℝ) := by ring
    have h3 : (pI r d : ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(d:ℝ)) := by
      have hnn : (0:ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(d:ℝ)) := by
        have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
        have h1 : (1:ℝ) ≤ 2*(r:ℝ)*(d:ℝ) := by nlinarith [hr2, hd1]
        nlinarith [Real.log_nonneg h1]
      have := Nat.floor_le hnn
      simpa [pI] using this
    calc Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ))
        = Real.log 2 + Real.log (pxi r ^ (-((r * pI r d : ℕ) : ℤ))) + Real.log (pS r d h : ℝ) :=
          h1a.trans (by rw [h1b])
      _ ≤ Real.log 2 + (pI r d : ℝ) + Real.log (pS r d h : ℝ) := by linarith
      _ ≤ Real.log 2 + 50 * Real.log (2*(r:ℝ)*(d:ℝ)) + Real.log (pS r d h : ℝ) := by linarith
  -- Step 3: assemble a single upper bound for the left-hand side.
  have hfact : Real.log (r.factorial : ℝ) ≤ (r:ℝ) * Real.log (r:ℝ) := h10_log_factorial_le r
  have hstep2 : 2*(r:ℝ)*((v:ℝ)*Real.log 2 + Real.log (d:ℝ))
      ≤ 2*(r:ℝ)*((h:ℝ)+1) + 2*(r:ℝ)*Real.log (d:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ) ≤ 2*(r:ℝ))
    nlinarith [h]
  have hstepP : 2*Real.log (∏ j, σ j) ≤ 2*(∏ j, σ j) := by
    have := Real.log_le_self (le_of_lt hPpos); linarith
  have hstepS : Real.log (pS r d h : ℝ) ≤ Real.log (16*(r:ℝ)*(d:ℝ)*(h:ℝ)) := by rw [hSpush]
  have hLHS : Real.log N + Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ))
      ≤ (r:ℝ) * Real.log (r:ℝ) + 2*(r:ℝ)*((h:ℝ)+1) + 2*(r:ℝ)*Real.log (d:ℝ)
        + Real.log 2 + 50*Real.log (2*(r:ℝ)*(d:ℝ)) + Real.log (16*(r:ℝ)*(d:ℝ)*(h:ℝ))
        + 2*(∏ j, σ j) := by
    linarith [hNle, hlogX, hfact, hstep2, hstepP, hstepS]
  -- Step 4: the numeric core: `TL < log π + C1`.
  have hTL : (r:ℝ) * Real.log (r:ℝ) + 2*(r:ℝ)*((h:ℝ)+1) + 2*(r:ℝ)*Real.log (d:ℝ)
      + Real.log 2 + 50*Real.log (2*(r:ℝ)*(d:ℝ)) + Real.log (16*(r:ℝ)*(d:ℝ)*(h:ℝ))
      ≤ 124 * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 := TL_bound hr hd hh
  have hC1low : 18874368 * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 ≤ h10C1 r d h := C1_lower hr hd hh
  have hnum : (r:ℝ) * Real.log (r:ℝ) + 2*(r:ℝ)*((h:ℝ)+1) + 2*(r:ℝ)*Real.log (d:ℝ)
      + Real.log 2 + 50*Real.log (2*(r:ℝ)*(d:ℝ)) + Real.log (16*(r:ℝ)*(d:ℝ)*(h:ℝ))
      < Real.log Real.pi + h10C1 r d h := by
    have h2 : (124:ℝ) * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2
        ≤ 18874368 * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 := by
      have hp : (0:ℝ) ≤ (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 := by positivity
      nlinarith [hp]
    have h3 : (0:ℝ) < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
    linarith
  have hLHSnum : Real.log N + Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ))
      < Real.log Real.pi + h10C1 r d h + 2*(∏ j, σ j) := by linarith [hLHS, hnum]
  -- Step 5: combine `C1 + 2∏σ ≤ v log 2 + 2 d^r C1 ∏σ` with `9·2^r S D = 2 d^r C1 ∏σ`.
  have hdr1 : (1:ℝ) ≤ (d:ℝ)^r := one_le_pow₀ (by exact_mod_cast hd)
  have hPy : ((d:ℝ)^r)⁻¹ ≤ ∏ j, σ j := h10_prod_inv_pow_le hd σ hσ
  have hvL : (0:ℝ) ≤ (v:ℝ) * Real.log 2 := by positivity
  have hC1ge2 : 2 ≤ h10C1 r d h := by
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    have ha' : (1:ℝ) ≤ (r:ℝ)^3 := by
      have h : (2:ℝ)^3 ≤ (r:ℝ)^3 := pow_le_pow_left₀ (by norm_num) hr2 3
      norm_num at h; linarith
    have hc : (1:ℝ) ≤ (d:ℝ)^2 := one_le_pow₀ hd1
    have hprod : (1:ℝ) ≤ (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 := by
      have h2 : (1:ℝ) ≤ (r:ℝ)^3 * (h:ℝ) := by
        have := mul_le_mul ha' hh1 (by norm_num) (by positivity); simpa using this
      have := mul_le_mul h2 hc (by norm_num) (by positivity); simpa using this
    have h1 : (2:ℝ) ≤ 18874368 * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 := by nlinarith [hprod]
    linarith [C1_lower hr hd hh]
  have hfc : h10C1 r d h + 2*(∏ j, σ j)
      ≤ (v:ℝ)*Real.log 2 + 2*(d:ℝ)^r * h10C1 r d h * (∏ j, σ j) :=
    final_combine (r := r) hdr1 hC1ge2 hPy hvL
  have hkey : 9 * (2:ℝ)^r * (pS r d h : ℝ) * pD r d σ
      = 2 * (d:ℝ)^r * h10C1 r d h * (∏ j, σ j) := by
    rw [pD, hSpush, h10C1]
    rw [mul_pow, pow_succ]
    ring
  rw [hkey]
  linarith [hLHSnum, hfc]

end Work.BW
