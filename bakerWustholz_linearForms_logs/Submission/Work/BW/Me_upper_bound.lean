import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.card_multIdx

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BW.Me_upper_bound`

Upper bound for the number `M_e` of **equations** of the Baker–Wüstholz §13 auxiliary
linear system, in the form needed by BW (1982/1993), namely

`M_e · r! ≤ 32.1 · r · d · h · (11.75 r + 1)^r · D^r`,

where `d = [K : ℚ]`, `D = pD r d σ`, `h` is the height parameter, `S = pS r d h = 16 r d h`
and `T = pT r d σ = ⌊11.75 r D⌋`.

With `AuxEqnIdx r S T = {s : ℤ // |s| ≤ S} × MultIdx r T` and `card_multIdx`,
`M_e = (2S+1) · (T+r choose r) = (32 r d h + 1) · (T+r choose r)`.  Hence (`r! · (T+r choose r)
≤ (T+r)^r` and `T + r ≤ (11.75 r + 1) D`)

`M_e · r! ≤ (32 r d h + 1) (T+r)^r ≤ 32.1 r d h (11.75 r + 1)^r D^r`.

The key numeric input is `r ≤ D`, which holds because `σ_j ≥ 1/d` forces
`∏ σ_j ≥ (1/d)^r`, so (`32d)^{r+1} ∏σ_j ≥ 32^{r+1} d`, and then
`D ≥ 2 · 32^{r+1} d log(2rd) · r^r ≥ r`.

The auxiliary statements are proved locally (private) so that this module is self-contained.
-/

namespace Work.BW

open scoped BigOperators

/-- `(n choose k) · k! ≤ n^k`: the falling factorial `n(n-1)⋯(n-k+1)` has `k` factors,
each at most `n`. -/
private lemma choose_mul_factorial_le_pow' (r T : ℕ) :
    ((T + r).choose r : ℝ) * (r.factorial : ℝ) ≤ ((T : ℝ) + (r : ℝ)) ^ r := by
  have h2 : (T + r).descFactorial r ≤ (T + r) ^ r := Nat.descFactorial_le_pow _ _
  have h3 : (T + r).descFactorial r = r.factorial * (T + r).choose r :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h4 : (((T + r).descFactorial r : ℕ) : ℝ) ≤ (((T + r) ^ r : ℕ) : ℝ) := by
    exact_mod_cast h2
  calc ((T + r).choose r : ℝ) * (r.factorial : ℝ)
      = (((T + r).descFactorial r : ℕ) : ℝ) := by rw [h3]; push_cast; ring
    _ ≤ (((T + r) ^ r : ℕ) : ℝ) := h4
    _ = ((T : ℝ) + (r : ℝ)) ^ r := by push_cast; ring

/-- `M_e = (2S+1) · (T+r choose r)`: the ℤ-part `{s // |s| ≤ S}` contributes `2S+1` and the
multi-index part contributes `(T+r choose r)` (`card_multIdx`). -/
private lemma cardAux (r S T : ℕ) (hr : 1 ≤ r) :
    Fintype.card (AuxEqnIdx r S T) = (2 * S + 1) * (T + r).choose r := by
  rw [Fintype.card_prod, card_multIdx r T hr, Fintype.card_coe, Int.card_Icc]
  have h : ((S : ℤ) + 1 - (-(S : ℤ))).toNat = 2 * S + 1 := by omega
  rw [h]

/-- `r ≤ pD r d σ` for `r ≥ 2`, `d ≥ 1` and `σ_j ≥ 1/d`. -/
private lemma le_pD_self {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) : (r : ℝ) ≤ pD r d σ := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by linarith
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hC : (r:ℝ) ≤ (r:ℝ)^r := le_self_pow₀ (by linarith) (by omega)
  have hE : (32:ℝ)^3 ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog : (1:ℝ) ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := by
    have h4 : (4:ℝ) ≤ 2*(r:ℝ)*(d:ℝ) := by nlinarith
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans hlog4 (Real.log_le_log (by norm_num) h4)
  -- `32^(r+1) · d ≤ (32d)^(r+1) · ∏ σ`
  have hA : (32:ℝ)^(r+1) * (d:ℝ) ≤ ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j := by
    have hprod2 : (32:ℝ)^r ≤ ∏ j : Fin r, (32 * (d:ℝ) * σ j) := by
      have h := Finset.prod_le_prod₀ (s := Finset.univ)
          (f := fun _ : Fin r => (32:ℝ)) (g := fun j : Fin r => 32 * (d:ℝ) * σ j)
          (fun i _ => by norm_num)
          (fun j _ => by
            have h1 : 32 * (d:ℝ) * (1/(d:ℝ)) ≤ 32 * (d:ℝ) * σ j :=
              mul_le_mul_of_nonneg_left (hσ j) (by positivity : (0:ℝ) ≤ 32 * (d:ℝ))
            have h2 : 32 * (d:ℝ) * (1/(d:ℝ)) = (32:ℝ) := by
              rw [mul_assoc, mul_one_div, div_self hdne, mul_one]
            linarith [h1, h2])
      simpa [Finset.prod_const, Fintype.card_fin] using h
    have hsplit : ∏ j : Fin r, (32 * (d:ℝ) * σ j) = ((32:ℝ)*(d:ℝ))^r * ∏ j, σ j := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_const, Fintype.card_fin]
    have hstep : ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j
        = 32 * (d:ℝ) * (((32:ℝ)*(d:ℝ))^r * ∏ j : Fin r, σ j) := by
      rw [pow_succ]; ring
    rw [hstep, ← hsplit]
    calc (32:ℝ)^(r+1) * (d:ℝ) = 32 * (d:ℝ) * (32:ℝ)^r := by rw [pow_succ]; ring
      _ ≤ 32 * (d:ℝ) * ∏ j : Fin r, (32 * (d:ℝ) * σ j) :=
          mul_le_mul_of_nonneg_left hprod2 (by positivity : (0:ℝ) ≤ 32 * (d:ℝ))
  have hQ0 : (0:ℝ) ≤ ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j :=
    mul_nonneg (by positivity)
      (Finset.prod_nonneg (fun j _ => le_trans (by positivity : (0:ℝ) ≤ 1/(d:ℝ)) (hσ j)))
  have hDform : pD r d σ
      = (2 * (r:ℝ)^r) * (((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j)
        * Real.log (2*(r:ℝ)*(d:ℝ)) := by
    unfold pD; ring
  have hbig : (1:ℝ) ≤ (2 * (32:ℝ)^3) * (d:ℝ) := by
    have h : (2 * (32:ℝ)^3 : ℝ) = 65536 := by norm_num
    rw [h]; nlinarith [hdR]
  have step0 : (r:ℝ) ≤ (2 * (r:ℝ)) * ((32:ℝ)^3 * (d:ℝ)) :=
    calc (r:ℝ) = (r:ℝ) * 1 := by ring
      _ ≤ (r:ℝ) * ((2 * (32:ℝ)^3) * (d:ℝ)) := mul_le_mul_of_nonneg_left hbig hr0
      _ = (2 * (r:ℝ)) * ((32:ℝ)^3 * (d:ℝ)) := by ring
  have step1 : (2 * (r:ℝ)) * ((32:ℝ)^3 * (d:ℝ)) ≤ (2 * (r:ℝ)^r) * ((32:ℝ)^(r+1) * (d:ℝ)) :=
    mul_le_mul (by linarith : (2:ℝ) * (r:ℝ) ≤ 2 * (r:ℝ)^r)
      (mul_le_mul hE le_rfl (by positivity : (0:ℝ) ≤ (d:ℝ))
        (by positivity : (0:ℝ) ≤ (32:ℝ)^(r+1)))
      (by positivity : (0:ℝ) ≤ (32:ℝ)^3 * (d:ℝ)) (by positivity : (0:ℝ) ≤ 2 * (r:ℝ)^r)
  have step2 : (2 * (r:ℝ)^r) * ((32:ℝ)^(r+1) * (d:ℝ))
      ≤ (2 * (r:ℝ)^r) * (((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j) :=
    mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 2 * (r:ℝ)^r)
  have hX0 : (0:ℝ) ≤ 2 * (r:ℝ)^r * (((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j) :=
    mul_nonneg (by positivity) hQ0
  have step3 : (2 * (r:ℝ)^r) * (((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j) * 1
      ≤ (2 * (r:ℝ)^r) * (((32:ℝ)*(d:ℝ))^(r+1) * ∏ j : Fin r, σ j)
        * Real.log (2*(r:ℝ)*(d:ℝ)) :=
    mul_le_mul_of_nonneg_left hlog hX0
  rw [hDform]
  exact le_trans step0 (le_trans step1 (le_trans step2 (le_trans (le_of_eq (by ring)) step3)))

/-- `T + r ≤ (11.75 r + 1) D` where `T = ⌊11.75 r D⌋`: `T ≤ 11.75 r D` (floor) and `r ≤ D`. -/
private lemma pT_add_r_le_aux {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (pT r d σ : ℝ) + (r : ℝ) ≤ (11.75 * (r : ℝ) + 1) * pD r d σ := by
  have hrR : (0:ℝ) ≤ (r:ℝ) := by
    have h : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  have hrD : (r:ℝ) ≤ pD r d σ := le_pD_self hr hd σ hσ
  have hD0 : (0:ℝ) ≤ pD r d σ := le_trans hrR hrD
  have hTle : (pT r d σ : ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by
    unfold pT
    exact Nat.floor_le (mul_nonneg (mul_nonneg (by norm_num) hrR) hD0)
  nlinarith [hTle, hrD]

/-- The general form of the statement, with `d : ℕ` in place of `Module.finrank ℚ K`. -/
private theorem Me_upper_bound_gen (r h d : ℕ) (hr : 2 ≤ r) (hh : 19 ≤ h) (hd : 1 ≤ d)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (Fintype.card (AuxEqnIdx r (pS r d h) (pT r d σ)) : ℝ) * (r.factorial : ℝ) ≤
      32.1 * (r : ℝ) * (d : ℝ) * (h : ℝ) * (11.75 * (r : ℝ) + 1) ^ r * (pD r d σ) ^ r := by
  have hr1 : 1 ≤ r := by omega
  -- `M_e · r! ≤ (2S+1) (T+r)^r`
  have hcard : (Fintype.card (AuxEqnIdx r (pS r d h) (pT r d σ)) : ℝ) * (r.factorial : ℝ)
      ≤ ((2 * pS r d h + 1 : ℕ) : ℝ) * ((pT r d σ : ℝ) + (r : ℝ)) ^ r := by
    rw [cardAux r (pS r d h) (pT r d σ) hr1]
    calc (((2 * pS r d h + 1) * (pT r d σ + r).choose r : ℕ) : ℝ) * (r.factorial : ℝ)
        = ((2 * pS r d h + 1 : ℕ) : ℝ)
            * (((pT r d σ + r).choose r : ℝ) * (r.factorial : ℝ)) := by push_cast; ring
      _ ≤ ((2 * pS r d h + 1 : ℕ) : ℝ) * (((pT r d σ : ℝ) + (r : ℝ)) ^ r) :=
          mul_le_mul_of_nonneg_left (choose_mul_factorial_le_pow' r (pT r d σ)) (by positivity)
  -- `(T+r)^r ≤ (11.75 r + 1)^r D^r`
  have hpow : ((pT r d σ : ℝ) + (r : ℝ)) ^ r
      ≤ (11.75 * (r : ℝ) + 1) ^ r * (pD r d σ) ^ r := by
    have hT : (pT r d σ : ℝ) + (r : ℝ) ≤ (11.75 * (r : ℝ) + 1) * pD r d σ :=
      pT_add_r_le_aux hr hd σ hσ
    have hnn : (0:ℝ) ≤ (pT r d σ : ℝ) + (r : ℝ) := by positivity
    have h1 := pow_le_pow_left₀ hnn hT r
    rwa [mul_pow] at h1
  have hS : ((2 * pS r d h + 1 : ℕ) : ℝ) = 32 * (r:ℝ) * (d:ℝ) * (h:ℝ) + 1 := by
    simp only [pS]; push_cast; ring
  -- `32 r d h + 1 ≤ 32.1 r d h` (since `r d h ≥ 38`)
  have hfac : 32 * (r:ℝ) * (d:ℝ) * (h:ℝ) + 1 ≤ 32.1 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
    have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    have h2 : (2:ℝ) ≤ (r:ℝ) * (d:ℝ) := by nlinarith
    have h3 : (38:ℝ) ≤ (r:ℝ) * (d:ℝ) * (h:ℝ) := by nlinarith
    nlinarith [h3]
  calc (Fintype.card (AuxEqnIdx r (pS r d h) (pT r d σ)) : ℝ) * (r.factorial : ℝ)
      ≤ ((2 * pS r d h + 1 : ℕ) : ℝ) * ((pT r d σ : ℝ) + (r : ℝ)) ^ r := hcard
    _ = (32 * (r:ℝ) * (d:ℝ) * (h:ℝ) + 1) * ((pT r d σ : ℝ) + (r : ℝ)) ^ r := by rw [hS]
    _ ≤ (32.1 * (r:ℝ) * (d:ℝ) * (h:ℝ))
          * ((11.75 * (r:ℝ) + 1) ^ r * (pD r d σ) ^ r) := by
        exact mul_le_mul hfac hpow (by positivity) (by positivity)
    _ = 32.1 * (r : ℝ) * (d : ℝ) * (h : ℝ) * (11.75 * (r : ℝ) + 1) ^ r
          * (pD r d σ) ^ r := by ring

set_option maxHeartbeats 800000 in
theorem Me_upper_bound {K : Type*} [Field K] [NumberField K] (r h : ℕ) (hr : 2 ≤ r) (hh : 19 ≤ h) (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) : (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h) (pT r (Module.finrank ℚ K) σ)) : ℝ) * (r.factorial : ℝ) ≤ 32.1 * (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) * (11.75 * (r : ℝ) + 1) ^ r * (pD r (Module.finrank ℚ K) σ) ^ r := by
  have hd : 1 ≤ Module.finrank ℚ K := by
    have h := Module.finrank_pos (R := ℚ) (M := K)
    omega
  exact Me_upper_bound_gen r h (Module.finrank ℚ K) hr hh hd σ hσ

end Work.BW
