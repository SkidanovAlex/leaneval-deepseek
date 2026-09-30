import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.split_aux
import Submission.Work.BW.num_13

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-! ### Helpers for the `D₀`-part of BW (13)/(15)

Write `L = log(2rd)` and `V = r^{r+1}(32d)^{r+1}∏σ`.  The three ingredients are
* `rD = 2LV` (pure `ring`, from the definition of `D = pD`),
* `V ≥ 2^18` for `r ≥ 2`, `d ≥ 1`, `σ_j ≥ 1/d`,
* `1 + log(57rd) + 2/(57rd) ≤ 3.1968 L` for `r ≥ 2`, `d ≥ 2`.
They combine as `(D₀+1) ≤ V + 1 ≤ V(1+2^{-18})` and `3.1968(1+2^{-18})/2 = 1.59841 < 1.6`. -/

/-- `r·D = 2·log(2rd)·V`, `V = r^{r+1}(32d)^{r+1}∏σ` (the numerator of the `D₀`-floor). -/
private lemma arch2_pD_shift {r d : ℕ} (σ : Fin r → ℝ) :
    (r:ℝ) * pD r d σ
      = 2 * Real.log (2*(r:ℝ)*(d:ℝ))
        * ((r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j) := by
  simp only [pD]
  rw [pow_succ]
  ring

/-- `V = r^{r+1}(32d)^{r+1}∏σ ≥ 2^18` for `r ≥ 2`, `d ≥ 1`, `σ_j ≥ 1/d`. -/
private lemma arch2_V_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (262144:ℝ) ≤ (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hσ' : ∀ j, 1 ≤ (d:ℝ) * σ j := by
    intro j
    have h := mul_le_mul_of_nonneg_left (hσ j) (le_of_lt hdpos)
    rwa [mul_one_div, div_self (ne_of_gt hdpos)] at h
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hW : (1:ℝ) ≤ (d:ℝ)^r * ∏ j, σ j := by
    have hdr : (d:ℝ)^r = ∏ j : Fin r, (d:ℝ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hdr, ← Finset.prod_mul_distrib]
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin r => (1:ℝ))
      (g := fun j => (d:ℝ)*σ j) (fun _ _ => by norm_num) (fun j _ => hσ' j)
    simpa using h
  have hA : (8:ℝ) ≤ (r:ℝ)^(r+1) := by
    calc (8:ℝ) = (2:ℝ)^3 := by norm_num
      _ ≤ (2:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (r:ℝ)^(r+1) := pow_le_pow_left₀ (by norm_num) hr2 (r+1)
  have hB : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    calc (32768:ℝ) = (32:ℝ)^3 := by norm_num
      _ ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hVform : (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j
      = (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * ((d:ℝ)^r * ∏ j, σ j) * (d:ℝ) := by
    rw [mul_pow, pow_succ (d:ℝ) r]
    ring
  have hstep1 : (8:ℝ) * 32768 ≤ (r:ℝ)^(r+1) * (32:ℝ)^(r+1) :=
    mul_le_mul hA hB (by norm_num) (by positivity)
  have hstep2 : ((8:ℝ) * 32768) * 1
      ≤ ((r:ℝ)^(r+1) * (32:ℝ)^(r+1)) * ((d:ℝ)^r * ∏ j, σ j) :=
    mul_le_mul hstep1 hW (by norm_num) (by positivity)
  have hstep3 : (((8:ℝ) * 32768) * 1) * 1
      ≤ (((r:ℝ)^(r+1) * (32:ℝ)^(r+1)) * ((d:ℝ)^r * ∏ j, σ j)) * (d:ℝ) :=
    mul_le_mul hstep2 hd1 (by norm_num) (by positivity)
  rw [hVform]
  norm_num at hstep3
  exact hstep3

/-- `1 + log(57rd) + 2/(57rd) ≤ 3.1968 log(2rd)` for `r ≥ 2`, `d ≥ 2`. -/
private lemma arch2_log_term_le {r d : ℕ} (hr : 2 ≤ r) (hd : 2 ≤ d) :
    1 + Real.log (57 * (r : ℝ) * (d : ℝ)) + 2 / (57 * (r : ℝ) * (d : ℝ))
      ≤ 3.1968 * Real.log (2 * (r : ℝ) * (d : ℝ)) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hrd4 : (4:ℝ) ≤ (r:ℝ)*(d:ℝ) := by nlinarith
  have h57 : Real.log (57*(r:ℝ)*(d:ℝ)) = Real.log 28.5 + Real.log (2*(r:ℝ)*(d:ℝ)) := by
    have h1 : (57:ℝ)*(r:ℝ)*(d:ℝ) = 28.5 * (2*(r:ℝ)*(d:ℝ)) := by ring
    rw [h1, Real.log_mul (by norm_num) (by positivity)]
  have hL8 : Real.log 8 ≤ Real.log (2*(r:ℝ)*(d:ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hL8eq : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  have h285 : Real.log 28.5 ≤ 3.35 := num13_log_285_le
  have h57inv : 2/(57*(r:ℝ)*(d:ℝ)) ≤ 2/228 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hlog2 := Real.log_two_gt_d9
  rw [h57]
  linarith [h285, h57inv, hL8, hL8eq, hlog2]

/-- The `D₀`-part of BW (13)/(15) in the units needed for `num_est15_arch2`: for `r ≥ 2`, `d ≥ 2`
and `σ_j ≥ 1/d`,
`(D₀+1)·(1 + log (57 r d) + 1/(57 r d)) + (D₀+1)/(57 r d) ≤ 1.6 · r · D`
where `D₀ = pD0 r d σ` and `D = pD r d σ`.
Route: `D = 2 r^r (32d)^{r+1} log(2rd) ∏σ`, hence `V := r D/(2 log(2rd)) = r^{r+1}(32d)^{r+1}∏σ`
and `D₀ ≤ V`; `V ≥ r^{r+1}32^{r+1} d ≥ 2^18` from `σ_j ≥ 1/d`.  Also
`1 + log (57rd) + 2/(57rd) ≤ 3.1968 · log (2rd)`: indeed `log (57rd) ≤ log 28.5 + log(2rd) ≤ 3.35 + L`
(`num13_log_285_le`), `2/(57rd) ≤ 2/228` and `L = log (2rd) ≥ log 8 ≥ 2.0793`
(`Real.log_two_gt_d9`), so the left side is `≤ L + 4.3588 ≤ 3.1968 L`.  Then
`(D₀+1)(1 + log(57rd) + 2/(57rd)) ≤ V(1 + 1/2^18)·3.1968 L ≤ 3.1969 V L ≤ 3.2 V L = 1.6 r D`.
(Numerically the worst case is `r = d = 2`, ratio `6.4381/6.6469`, margin 3.2%.) -/
theorem arch2_D0_le {r d : ℕ} (hr : 2 ≤ r) (hd : 2 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (((pD0 r d σ : ℕ) : ℝ) + 1) * (1 + Real.log (57 * r * (d : ℝ)) + 1 / (57 * r * (d : ℝ)))
      + (((pD0 r d σ : ℕ) : ℝ) + 1) / (57 * r * (d : ℝ))
      ≤ 1.6 * (r : ℝ) * pD r d σ := by
  have hd1 : 1 ≤ d := by omega
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hDpos : 0 < pD r d σ := pD_pos hr hd1 σ hσ
  have hVpos : 0 < (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j := by
    have h1 : 0 < ∏ j : Fin r, σ j := Finset.prod_pos (fun j _ => by
      have h2 : (0:ℝ) < 1/(d:ℝ) := by positivity
      linarith [hσ j])
    have h3 : (0:ℝ) < (r:ℝ)^(r+1) := by positivity
    have h4 : (0:ℝ) < (32*(d:ℝ))^(r+1) := by positivity
    exact mul_pos (mul_pos h3 h4) h1
  set V : ℝ := (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j with hV
  set L : ℝ := Real.log (2*(r:ℝ)*(d:ℝ)) with hL
  have hLpos : 0 < L := by rw [hL]; exact log_2rd_pos hr hd1
  have hVpos' : 0 < V := by rw [hV]; exact hVpos
  have hshift : (r:ℝ) * pD r d σ = 2 * L * V := by
    rw [hL, hV]
    simp only [pD]
    rw [pow_succ]
    ring
  have hVeq : (r:ℝ) * pD r d σ / (2 * L) = V := by
    rw [hshift]; field_simp
  have hVLeq : V * L = (r:ℝ) * pD r d σ / 2 := by
    rw [← hVeq]; field_simp
  have hD0le : (pD0 r d σ : ℝ) ≤ V := by
    have h := pD0_le hr hd1 σ hσ
    rw [← hL] at h
    linarith
  have hVge : (262144:ℝ) ≤ V := by
    rw [hV]; exact arch2_V_ge hr hd1 σ hσ
  have hD0p1 : (pD0 r d σ : ℝ) + 1 ≤ V * (1 + 1/2^18) := by
    have hV18 : (1:ℝ) ≤ V / 2^18 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have h1 : V + 1 ≤ V + V/2^18 := by linarith
    have h2 : V + V/2^18 = V * (1 + 1/2^18) := by ring
    linarith
  have hlog : 1 + Real.log (57 * (r:ℝ) * (d:ℝ)) + 2/(57*(r:ℝ)*(d:ℝ)) ≤ 3.1968 * L := by
    rw [hL]; exact arch2_log_term_le hr hd
  have hgoal : ((pD0 r d σ : ℝ) + 1) * (1 + Real.log (57 * (r:ℝ) * (d:ℝ)) + 2/(57*(r:ℝ)*(d:ℝ)))
      ≤ 1.6 * (r:ℝ) * pD r d σ := by
    have h57r : (1:ℝ) ≤ 57*(r:ℝ)*(d:ℝ) := by nlinarith
    have hclog : 0 ≤ 1 + Real.log (57*(r:ℝ)*(d:ℝ)) + 2/(57*(r:ℝ)*(d:ℝ)) := by
      have := Real.log_nonneg h57r
      positivity
    have h1 : ((pD0 r d σ : ℝ) + 1) * (1 + Real.log (57 * (r:ℝ) * (d:ℝ)) + 2/(57*(r:ℝ)*(d:ℝ)))
        ≤ (V * (1 + 1/2^18)) * (3.1968 * L) :=
      mul_le_mul hD0p1 hlog hclog (le_of_lt (mul_pos hVpos' (by norm_num)))
    have h2 : (V * (1 + 1/2^18)) * (3.1968 * L) = 3.1968 * (1 + 1/2^18) * (V * L) := by ring
    have h3 : 3.1968 * (1 + 1/2^18) * (V * L) ≤ 1.6 * (r:ℝ) * pD r d σ := by
      rw [hVLeq]
      nlinarith [hDpos, hrpos]
    linarith
  have hsplit : ((pD0 r d σ : ℝ) + 1) * (1 + Real.log (57 * (r:ℝ) * (d:ℝ)) + 1/(57*(r:ℝ)*(d:ℝ)))
      + ((pD0 r d σ : ℝ) + 1)/(57*(r:ℝ)*(d:ℝ))
      = ((pD0 r d σ : ℝ) + 1) * (1 + Real.log (57 * (r:ℝ) * (d:ℝ)) + 2/(57*(r:ℝ)*(d:ℝ))) := by
    ring
  rw [hsplit]
  exact hgoal

end Work.BW
