import Mathlib.Data.Nat.Choose.Lucas

namespace Commons.Algebra.CharP

/-- For a prime `p`, if `a < p ^ e` then `Nat.choose (a + p ^ e * N) (p ^ e * N) ≡ 1 [MOD p]`. -/
private theorem choose_pow_mul_modEq_one (p : ℕ) [Fact p.Prime] (e : ℕ) :
    ∀ a : ℕ, a < p ^ e → ∀ N : ℕ,
      Nat.choose (a + p ^ e * N) (p ^ e * N) ≡ 1 [MOD p] := by
  induction e with
  | zero =>
    intro a ha N
    have ha0 : a = 0 := Nat.lt_one_iff.mp (by simpa using ha)
    subst ha0
    simp only [pow_zero, zero_add, Nat.choose_self]
    exact Nat.ModEq.refl 1
  | succ e ih =>
    intro a ha N
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    have ha' : a / p < p ^ e := by
      apply Nat.div_lt_of_lt_mul
      simpa [pow_succ'] using ha
    have h1 : (a + p ^ (e + 1) * N) % p = a % p := by
      rw [pow_succ', mul_assoc]
      exact Nat.add_mul_mod_self_left a p (p ^ e * N)
    have h2 : (p ^ (e + 1) * N) % p = 0 := by
      rw [pow_succ', mul_assoc]
      exact Nat.mul_mod_right p (p ^ e * N)
    have h3 : (a + p ^ (e + 1) * N) / p = a / p + p ^ e * N := by
      rw [pow_succ', mul_assoc]
      exact Nat.add_mul_div_left a (p ^ e * N) hp_pos
    have h4 : (p ^ (e + 1) * N) / p = p ^ e * N := by
      rw [pow_succ', mul_assoc]
      exact Nat.mul_div_cancel_left (p ^ e * N) hp_pos
    have hrec := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)
      (n := a + p ^ (e + 1) * N) (k := p ^ (e + 1) * N)
    rw [h1, h2, h3, h4, Nat.choose_zero_right, one_mul] at hrec
    exact hrec.trans (ih (a / p) ha' N)

theorem choose_add_mul_pow_eq_one {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {e a N : ℕ} (h : a < p ^ e) :
    ((Nat.choose (a + p ^ e * N) (p ^ e * N) : ℕ) : R) = 1 := by
  have hmod : Nat.choose (a + p ^ e * N) (p ^ e * N) % p = 1 := by
    have hC := choose_pow_mul_modEq_one p e a h N
    simp only [Nat.ModEq] at hC
    rwa [Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at hC
  rw [CharP.cast_eq_mod R p, hmod, Nat.cast_one]

end Commons.Algebra.CharP