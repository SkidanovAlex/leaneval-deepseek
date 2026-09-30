import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Numeric bound for the `Θ`-term of BW §13:
`(D₀+1)·(3+log(2+16rd)) ≤ 0.2137·T`, `D₀ = pD0 r d σ`, `T = 11.75 r D`, `σ_j ≥ 1/d`.

Write `L = log(2rd)`, `V = r^{r+1}(32d)^{r+1}·∏σ`.  Then `r·D = 2·L·V` exactly (this is the
`D₀`-denominator: `D₀ = ⌊rD/(2L)⌋₊ ≤ V`), while
`3 + log(2+16rd) ≤ L + 5.15` and `V ≥ 2^18 = 262144`.  The two `nlinarith`-checked numeric
ingredients `V ≥ 262144`, `L ≥ 1.386` then give `(V+1)(L+5.15) ≤ 0.2137·11.75·2LV`. -/

/-- Pure arithmetic tail: with `V ≥ 262144` and `L ≥ 1.386`,
`(V+1)(L+5.15) ≤ 0.2137·11.75·(2LV)`. -/
private lemma key_arith {V L : ℝ} (hV : 262144 ≤ V) (hL : 1.386 ≤ L) :
    (V + 1) * (L + 5.15) ≤ 0.2137 * (11.75 * (2 * L * V)) := by
  nlinarith [hV, hL]

/-- `V = r^{r+1}(32d)^{r+1}∏σ ≥ 2^18` when `r ≥ 2`, `d ≥ 1`, `d σ_j ≥ 1`. -/
private lemma V_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 ≤ (d : ℝ) * σ j) :
    (262144:ℝ) ≤ (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hW : (1:ℝ) ≤ (d:ℝ)^r * ∏ j, σ j := by
    have hdr : (d:ℝ)^r = ∏ j : Fin r, (d:ℝ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hdr, ← Finset.prod_mul_distrib]
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin r => (1:ℝ))
      (g := fun j => (d:ℝ)*σ j) (fun _ _ => by norm_num) (fun j _ => hσ j)
    simpa using h
  have hA : (8:ℝ) ≤ (r:ℝ)^(r+1) := by
    calc (8:ℝ) = (2:ℝ)^3 := by norm_num
      _ ≤ (2:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (r:ℝ)^(r+1) := pow_le_pow_left₀ (by norm_num) hr2 (r+1)
  have hB : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    calc (32768:ℝ) = (32:ℝ)^3 := by norm_num
      _ ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hD : (1:ℝ) ≤ (d:ℝ) := hd1
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
    mul_le_mul hstep2 hD (by norm_num) (by positivity)
  rw [hVform]
  norm_num at hstep3
  exact hstep3

/-- `log(2rd) ≥ 1.386` for `r ≥ 2`, `d ≥ 1`. -/
private lemma L_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (1.386:ℝ) ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hx4 : (4:ℝ) ≤ 2 * (r:ℝ) * (d:ℝ) := by nlinarith
  calc (1.386:ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    _ = Real.log (4:ℝ) := by rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    _ ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) := Real.log_le_log (by norm_num) hx4

/-- `3 + log(2+16rd) ≤ log(2rd) + 5.15` for `r ≥ 2`, `d ≥ 1`. -/
private lemma log_upper {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)) ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) + 5.15 := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hx4 : (4:ℝ) ≤ 2 * (r:ℝ) * (d:ℝ) := by nlinarith
  have hxpos : (0:ℝ) < 2 * (r:ℝ) * (d:ℝ) := by linarith
  have h1 : (2:ℝ) + 16 * (r:ℝ) * (d:ℝ)
      = (2 * (r:ℝ) * (d:ℝ)) * (8 + 2 / (2 * (r:ℝ) * (d:ℝ))) := by
    field_simp
    ring
  have h2 : (8:ℝ) + 2 / (2 * (r:ℝ) * (d:ℝ))
      = 8 * (1 + 1 / (4 * (2 * (r:ℝ) * (d:ℝ)))) := by
    field_simp
    ring
  have hlog : Real.log (2 + 16 * (r:ℝ) * (d:ℝ))
      = Real.log (2 * (r:ℝ) * (d:ℝ))
        + (3 * Real.log 2 + Real.log (1 + 1/(4 * (2*(r:ℝ)*(d:ℝ))))) := by
    rw [h1]
    rw [Real.log_mul hxpos.ne' (by positivity : (8 + 2/(2*(r:ℝ)*(d:ℝ))) ≠ 0)]
    rw [h2]
    rw [Real.log_mul (by norm_num : (8:ℝ) ≠ 0)
      (by positivity : (1 + 1/(4*(2*(r:ℝ)*(d:ℝ)))) ≠ 0)]
    rw [show Real.log (8:ℝ) = 3 * Real.log 2 by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num]
  rw [hlog]
  have h4 : Real.log (1 + 1/(4 * (2*(r:ℝ)*(d:ℝ)))) ≤ 1/(4 * (2*(r:ℝ)*(d:ℝ))) := by
    have := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < 1 + 1/(4 * (2*(r:ℝ)*(d:ℝ))) by positivity)
    linarith
  have h5 : 1/(4 * (2*(r:ℝ)*(d:ℝ))) ≤ 1/16 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h6 := Real.log_two_lt_d9
  linarith

/-- `r·D = 2·log(2rd)·V` with `V = r^{r+1}(32d)^{r+1}∏σ` (the numerator of the `D₀`-floor). -/
private lemma pD_shift {r d : ℕ} (σ : Fin r → ℝ) :
    (r:ℝ) * pD r d σ
      = 2 * Real.log (2*(r:ℝ)*(d:ℝ))
        * ((r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j) := by
  simp only [pD]
  rw [pow_succ]
  ring

/-- `D₀ = ⌊rD/(2 log(2rd))⌋₊ ≤ V`. -/
private lemma pD0_le_V {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 ≤ (d : ℝ) * σ j) :
    (pD0 r d σ : ℝ) ≤ (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hLpos : (0:ℝ) < Real.log (2*(r:ℝ)*(d:ℝ)) := by
    apply Real.log_pos
    nlinarith
  have hσpos : ∀ j, 0 < σ j := fun j =>
    pos_of_mul_pos_right (lt_of_lt_of_le zero_lt_one (hσ j)) (le_of_lt hdpos)
  have hprodn : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσpos j)
  have hpDpos : 0 < pD r d σ := by
    simp only [pD]
    positivity
  have hx : (0:ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * (r:ℝ) * (d:ℝ))) := by
    apply div_nonneg (mul_nonneg (le_of_lt hrpos) (le_of_lt hpDpos))
    positivity
  have hfl : (⌊(r:ℝ) * pD r d σ / (2 * Real.log (2 * (r:ℝ) * (d:ℝ)))⌋₊ : ℝ)
      ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2 * (r:ℝ) * (d:ℝ))) := Nat.floor_le hx
  have hrewrite : (r:ℝ) * pD r d σ / (2 * Real.log (2 * (r:ℝ) * (d:ℝ)))
      = (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j := by
    rw [pD_shift σ]
    field_simp
  change (⌊(r:ℝ) * pD r d σ / (2 * Real.log (2 * (r:ℝ) * (d:ℝ)))⌋₊ : ℝ)
      ≤ (r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j
  linarith [hfl, hrewrite]

/-- Numeric bound for the `Θ`-term: `(D₀+1)·(3+log(2+16rd)) ≤ 0.2137·T` with
`D₀ = pD0 r d σ`, `T = 11.75 r D`, under `σ_j ≥ 1/d`. -/
theorem pD0_succ_mul_log_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 ≤ (d : ℝ) * σ j) :
    ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r : ℝ) * (d : ℝ)))
      ≤ 0.2137 * (11.75 * (r : ℝ) * pD r d σ) := by
  have hV := V_ge hr hd σ hσ
  have hL := L_ge hr hd
  have hlog := log_upper hr hd
  have hpD := pD_shift (r := r) (d := d) σ
  have hD0 := pD0_le_V hr hd σ hσ
  have hc : (0:ℝ) ≤ 3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)) := by
    have h1 : (0:ℝ) ≤ Real.log (2 + 16 * (r:ℝ) * (d:ℝ)) := by
      apply Real.log_nonneg
      have hr1 : (1:ℝ) ≤ (r:ℝ) := by
        have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
        linarith
      have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      nlinarith
    linarith
  have step1 : ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)))
      ≤ ((r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j + 1)
          * (Real.log (2 * (r:ℝ) * (d:ℝ)) + 5.15) :=
    mul_le_mul (by linarith [hD0]) hlog hc (by linarith [hV])
  calc ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)))
      ≤ ((r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j + 1)
          * (Real.log (2 * (r:ℝ) * (d:ℝ)) + 5.15) := step1
    _ ≤ 0.2137 * (11.75 * (2 * Real.log (2 * (r:ℝ) * (d:ℝ))
          * ((r:ℝ)^(r+1) * (32*(d:ℝ))^(r+1) * ∏ j, σ j))) := key_arith hV hL
    _ = 0.2137 * (11.75 * (r:ℝ) * pD r d σ) := by
        rw [hpD.symm]
        ring

end Work.BW
