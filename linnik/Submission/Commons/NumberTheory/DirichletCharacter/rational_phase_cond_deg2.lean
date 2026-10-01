import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative

namespace Commons.NumberTheory.DirichletCharacter

/-- If `p` divides every coefficient of `P : ℤ[X]`, then `p` divides `P.eval y`. -/
lemma ratPhase_int_dvd_eval_of_dvd_coeff {p : ℤ} {P : Polynomial ℤ}
    (h : ∀ i, p ∣ P.coeff i) (y : ℤ) : p ∣ P.eval y := by
  rw [← Polynomial.C_dvd_iff_dvd_coeff] at h
  obtain ⟨Q, hQ⟩ := h
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_C]
  exact dvd_mul_right p (Q.eval y)

/-- In a field, `((a * c) * c⁻¹ ^ 2).val = 0` iff `a = 0` (for `c ≠ 0`). -/
lemma ratPhase_zmod_mul_inv_sq_val_eq_zero_iff {p : ℕ} [Fact p.Prime]
    (a c : ZMod p) (hc : c ≠ 0) : ((a * c) * c⁻¹ ^ 2).val = 0 ↔ a = 0 := by
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hsimp : (a * c) * c⁻¹ ^ 2 = a * c⁻¹ := by
    calc (a * c) * c⁻¹ ^ 2 = a * (c * c⁻¹) * c⁻¹ := by ring
      _ = a * c⁻¹ := by rw [hcc, mul_one]
  rw [hsimp, ZMod.val_eq_zero, mul_eq_zero]
  simp [inv_ne_zero hc]

theorem rational_phase_cond_deg2 (p : ℕ) [Fact p.Prime] (N₂ G₂ : Polynomial ℤ)
    (hG : G₂.natDegree ≤ 2)
    (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0) (y : ℕ) :
    ((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
        * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val = 0
      ↔ (p : ℤ) ∣ (Polynomial.derivative N₂).eval (y : ℤ) := by
  have hcoeffZero : ∀ i, 2 < i → G₂.coeff i = 0 :=
    (Polynomial.natDegree_le_iff_coeff_eq_zero (n := 2)).mp hG
  -- coefficients of `G₂ - C (G₂.coeff 0)` are divisible by `p`
  have hGcoeff : ∀ i, (p : ℤ) ∣ (G₂ - Polynomial.C (G₂.coeff 0)).coeff i := by
    intro i
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C]
    rcases eq_or_ne i 0 with h0 | h0
    · subst h0; simp
    · rw [if_neg h0, sub_zero]
      rcases eq_or_ne i 1 with h1 | h1
      · subst h1; exact hG1
      · rcases eq_or_ne i 2 with h2 | h2
        · subst h2; exact hG2
        · rw [hcoeffZero i (by omega)]
          exact dvd_zero _
  -- coefficients of `G₂.derivative` are divisible by `p`
  have hDcoeff : ∀ i, (p : ℤ) ∣ G₂.derivative.coeff i := by
    intro i
    rw [Polynomial.coeff_derivative]
    rcases eq_or_ne i 0 with h0 | h0
    · subst h0; simpa using hG1
    · rcases eq_or_ne i 1 with h1 | h1
      · subst h1; simpa using dvd_mul_of_dvd_left hG2 (2 : ℤ)
      · rw [hcoeffZero (i + 1) (by omega), zero_mul]
        exact dvd_zero _
  -- `G₂.eval y ≡ G₂.coeff 0 (mod p)`
  have hGy : ((G₂.eval (y : ℤ) : ℤ) : ZMod p) = ((G₂.coeff 0 : ℤ) : ZMod p) := by
    have h1 : (((G₂ - Polynomial.C (G₂.coeff 0)).eval (y : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
        (ratPhase_int_dvd_eval_of_dvd_coeff hGcoeff (y : ℤ))
    rw [Polynomial.eval_sub, Polynomial.eval_C] at h1
    push_cast at h1
    exact sub_eq_zero.mp h1
  -- `G₂'.eval y ≡ 0 (mod p)`
  have hGdy : (((G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
      (ratPhase_int_dvd_eval_of_dvd_coeff hDcoeff (y : ℤ))
  have hc_ne : (((G₂.coeff 0 : ℤ) : ZMod p)) ≠ 0 := by
    intro h
    exact hG0 ((ZMod.intCast_zmod_eq_zero_iff_dvd (G₂.coeff 0) p).mp h)
  -- the whole evaluation reduces modulo `p` to `N₂'(y) * G₂.coeff 0`
  have hE : ((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p))
      = (((Polynomial.derivative N₂).eval (y : ℤ) : ℤ) : ZMod p)
        * ((G₂.coeff 0 : ℤ) : ZMod p) := by
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
    simp only [Int.cast_sub, Int.cast_mul]
    rw [hGy, hGdy]
    ring
  rw [hE, ratPhase_zmod_mul_inv_sq_val_eq_zero_iff _ _ hc_ne]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ p

end Commons.NumberTheory.DirichletCharacter