import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric core of `D_ge`, for an arbitrary degree `d ≥ 1`.

Since each `σ j ≥ 1/d` we have `∏ j, σ j ≥ (1/d)^r`, hence
`(32d)^(r+1) · ∏ j, σ j ≥ 32^(r+1) · d ≥ 32^3 · d`, and together with `r^r ≥ 4`
and `log(2rd) ≥ log 4`:
`pD = 2·r^r·(32d)^(r+1)·log(2rd)·∏σ ≥ 2·4·32768·log 4 · d ≥ 363408·d`. -/
private lemma pD_ge_of {r d : ℕ} (hr : 2 ≤ r) (hd : 0 < d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    363408 * (d : ℝ) ≤ pD r d σ := by
  have hdr : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hσnn : (0:ℝ) ≤ ∏ j : Fin r, σ j :=
    Finset.prod_nonneg (fun j _ => le_trans (by positivity) (hσ j))
  have hprod : (1/(d:ℝ))^r ≤ ∏ j : Fin r, σ j := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun _ : Fin r => 1/(d:ℝ)) (g := σ)
        (fun j _ => by positivity) (fun j _ => hσ j)
    simpa using h
  have hkey : (d:ℝ)^(r+1) * (1/(d:ℝ))^r = (d:ℝ) := by
    have ha : (d:ℝ) ≠ 0 := ne_of_gt hdr
    have h := pow_sub₀ (d:ℝ) ha (show r ≤ r+1 by omega)
    rw [one_div, inv_pow, ← h, show (r+1)-r = 1 by omega, pow_one]
  have hdprod : (d:ℝ) ≤ (d:ℝ)^(r+1) * ∏ j : Fin r, σ j := by
    calc (d:ℝ) = (d:ℝ)^(r+1) * (1/(d:ℝ))^r := hkey.symm
      _ ≤ (d:ℝ)^(r+1) * ∏ j : Fin r, σ j :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  have hpow : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    have h : (32:ℝ)^3 ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h ⊢
    exact h
  have hc : (32768:ℝ) * (d:ℝ) ≤ (32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j := by
    have hdprod' : (32768:ℝ) * (d:ℝ) ≤
        (32:ℝ)^(r+1) * ((d:ℝ)^(r+1) * ∏ j : Fin r, σ j) :=
      mul_le_mul hpow hdprod (by positivity) (by positivity)
    rw [mul_pow]
    simpa only [mul_assoc] using hdprod'
  have hb : (4:ℝ) ≤ (r:ℝ)^r := by
    have h1 : (2:ℝ)^2 ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
    have h2 : (2:ℝ)^r ≤ (r:ℝ)^r := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hr) r
    norm_num at h1
    linarith
  have hle4 : (4:ℝ) ≤ 2 * (r:ℝ) * (d:ℝ) := by
    have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    nlinarith
  have he : Real.log 4 ≤ Real.log (2 * r * d) := Real.log_le_log (by norm_num) hle4
  have hlog4 : (363408:ℝ) ≤ 262144 * Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [h4]
    nlinarith [Real.log_two_gt_d9]
  have hlog4nn : (0:ℝ) ≤ Real.log 4 := by
    have : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hstep1 : 2 * (4 * (32768 * (d:ℝ))) ≤
      2 * ((r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j)) := by
    have h4c : (4:ℝ) * (32768 * (d:ℝ)) ≤
        (r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j) :=
      mul_le_mul hb hc (by positivity) (by positivity)
    linarith [h4c]
  have hXn : (0:ℝ) ≤ 2 * ((r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j)) := by
    have h1 : (0:ℝ) ≤ (r:ℝ)^r := pow_nonneg (by positivity) r
    have h2 : (0:ℝ) ≤ (32*d:ℝ)^(r+1) := pow_nonneg (by positivity) _
    positivity
  have hstep1' : 2 * (4 * (32768 * (d:ℝ))) * Real.log 4
      ≤ 2 * ((r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j)) * Real.log 4 :=
    mul_le_mul_of_nonneg_right hstep1 hlog4nn
  have hstep2 : 2 * ((r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j)) * Real.log 4
      ≤ 2 * ((r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j)) * Real.log (2 * r * d) :=
    mul_le_mul_of_nonneg_left he hXn
  have hpd : pD r d σ =
      2 * ((r:ℝ)^r * ((32*d:ℝ)^(r+1) * ∏ j : Fin r, σ j)) * Real.log (2 * r * d) := by
    rw [pD]; ring
  have hstart : 363408 * (d:ℝ) ≤ 2 * (4 * (32768 * (d:ℝ))) * Real.log 4 := by
    have := mul_le_mul_of_nonneg_right hlog4 (le_of_lt hdr)
    nlinarith [this]
  rw [hpd]
  linarith [hstart, hstep1', hstep2]

/-- `pD r d σ ≥ 363408 * d` under `r ≥ 2`, `σ j ≥ 1/d`, `d = [K:ℚ]`.
Since `∏ j, σ j ≥ (1/d)^r` and `(32d)^(r+1) / d^r = 32^(r+1) * d ≥ 32^3`:
`pD = 2*r^r*(32d)^(r+1)*log(2rd)*∏σ ≥ 2*4*32768*log 4 * d ≥ 363408*d`. In particular `pD > 0`. -/
theorem D_ge {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 2 ≤ r)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    363408 * (Module.finrank ℚ K : ℝ) ≤ pD r (Module.finrank ℚ K) σ := by
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact pD_ge_of hr hd σ hσ

end Work.BW
