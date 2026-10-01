import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Derivative

namespace Commons.NumberTheory.DirichletCharacter

/-- For a polynomial `Q : ℤ[X]` of degree at most two, the formal derivative is the
linear polynomial `(2 * Q.coeff 2) * X + Q.coeff 1`. -/
private lemma deriv_eq_of_natDegree_le_two (Q : Polynomial ℤ) (hdeg : Q.natDegree ≤ 2) :
    Polynomial.derivative Q
      = Polynomial.C (Q.coeff 1) + Polynomial.C (2 * Q.coeff 2) * Polynomial.X := by
  ext n
  rcases n with _ | _ | n
  · simp [Polynomial.coeff_derivative]
  · simp only [Polynomial.coeff_derivative, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
    norm_num
    ring
  · have hcoeff : Q.coeff (n + 2 + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    simp only [Polynomial.coeff_derivative, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X, hcoeff]
    norm_num

/-- The solution set of a non-degenerate linear congruence modulo a nonzero `p`. -/
private lemma linear_dvd_iff (p : ℕ) [Fact p.Prime] (A B : ℤ) (hA : (A : ZMod p) ≠ 0) :
    ∃ a₀ : ℕ, a₀ < p ∧ ∀ y : ℕ,
      ((p : ℤ) ∣ (A * (y : ℤ) + B) ↔ (y : ZMod p) = (a₀ : ZMod p)) := by
  set r : ZMod p := -(B : ZMod p) / (A : ZMod p) with hr
  refine ⟨r.val, ZMod.val_lt r, ?_⟩
  intro y
  have hval : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_zmod_val r
  rw [hval, hr]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (A * (y : ℤ) + B) p]
  push_cast
  rw [add_eq_zero_iff_eq_neg, eq_div_iff hA]
  rw [mul_comm (y : ZMod p) (A : ZMod p)]

theorem quadratic_deriv_dvd_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ 2) (hQ : ¬ (p : ℤ) ∣ Q.coeff 2) :
    ∃ a₀ : ℕ, a₀ < p ∧ ∀ y : ℕ,
      ((p : ℤ) ∣ (Polynomial.derivative Q).eval (y : ℤ) ↔ (y : ZMod p) = (a₀ : ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hc2 : (Q.coeff 2 : ZMod p) ≠ 0 :=
    fun h => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd (Q.coeff 2) p).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdvd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 2 ≤ p := hp.two_le
      omega
    exact ((ZMod.isUnit_iff_coprime 2 p).mpr hcop).ne_zero
  have hA : ((2 * Q.coeff 2 : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero h2 hc2
  obtain ⟨a₀, ha₀lt, ha₀⟩ := linear_dvd_iff p (2 * Q.coeff 2) (Q.coeff 1) hA
  refine ⟨a₀, ha₀lt, fun y => ?_⟩
  rw [deriv_eq_of_natDegree_le_two Q hdeg]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [add_comm (Q.coeff 1) ((2 * Q.coeff 2) * (y : ℤ))]
  exact ha₀ y

end Commons.NumberTheory.DirichletCharacter