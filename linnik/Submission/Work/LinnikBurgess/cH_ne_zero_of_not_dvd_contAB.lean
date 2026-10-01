import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.commons_cube_api

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.LinnikBurgess

open Polynomial

namespace cHnezero

/-- **Wronskian identity for two monic cubics.**  For `A = X³ + a₁X² + a₂X + a₃` and
`B = X³ + b₁X² + b₂X + b₃` over a commutative ring, `A'B - B'A` has the displayed
coefficients. -/
lemma wronskian_identity {R : Type*} [CommRing R] (a1 a2 a3 b1 b2 b3 : R) :
    (Polynomial.X^3 + Polynomial.C a1 * Polynomial.X^2 + Polynomial.C a2 * Polynomial.X
        + Polynomial.C a3 : R[X]).derivative
      * (Polynomial.X^3 + Polynomial.C b1 * Polynomial.X^2 + Polynomial.C b2 * Polynomial.X
        + Polynomial.C b3)
    - (Polynomial.X^3 + Polynomial.C b1 * Polynomial.X^2 + Polynomial.C b2 * Polynomial.X
        + Polynomial.C b3).derivative
      * (Polynomial.X^3 + Polynomial.C a1 * Polynomial.X^2 + Polynomial.C a2 * Polynomial.X
        + Polynomial.C a3)
    = Polynomial.C (b1 - a1) * Polynomial.X^4
      + Polynomial.C (2*(b2 - a2)) * Polynomial.X^3
      + Polynomial.C (-a2*b1 + a1*b2 + 3*(b3-a3)) * Polynomial.X^2
      + Polynomial.C (2*a1*b3 - 2*b1*a3) * Polynomial.X
      + Polynomial.C (a2*b3 - b2*a3) := by
  have h2 : (Polynomial.C (2:R) : R[X]) = 2 := map_ofNat Polynomial.C 2
  have h3 : (Polynomial.C (3:R) : R[X]) = 3 := map_ofNat Polynomial.C 3
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.C_add, Polynomial.C_mul,
    Polynomial.C_neg, Polynomial.C_sub, Nat.cast_ofNat]
  simp only [h2, h3]
  ring

/-- Coefficient at `X⁴` of the right-hand side of `wronskian_identity`. -/
lemma coeff_four {R : Type*} [CommRing R] (c4 c3 c2 c1 c0 : R) :
    (Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3
      + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X
      + Polynomial.C c0 : R[X]).coeff 4 = c4 := by
  simp

/-- Coefficient at `X³` of the right-hand side of `wronskian_identity`. -/
lemma coeff_three {R : Type*} [CommRing R] (c4 c3 c2 c1 c0 : R) :
    (Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3
      + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X
      + Polynomial.C c0 : R[X]).coeff 3 = c3 := by
  simp

/-- Coefficient at `X²` of the right-hand side of `wronskian_identity`. -/
lemma coeff_two {R : Type*} [CommRing R] (c4 c3 c2 c1 c0 : R) :
    (Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3
      + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X
      + Polynomial.C c0 : R[X]).coeff 2 = c2 := by
  simp

/-- The explicit expansion of the monic cubic `cA p a`. -/
lemma cA_eq (p : ℕ) (a : Fin 3 → ℕ) :
    Commons.NumberTheory.DirichletCharacter.cA p a
      = Polynomial.X^3 + Polynomial.C ((esymm3 a 0 : ℤ) : ZMod p) * Polynomial.X^2
        + Polynomial.C ((esymm3 a 1 : ℤ) : ZMod p) * Polynomial.X
        + Polynomial.C ((esymm3 a 2 : ℤ) : ZMod p) := by
  rw [Commons.NumberTheory.DirichletCharacter.cA, Fin.prod_univ_three]
  simp only [esymm3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_mul]
  ring

/-- If an integer vanishes modulo `p`, then `p` divides its absolute value. -/
lemma dvd_natAbs_of_zmod_eq (p : ℕ) (k : ℤ) (h : ((k : ℤ) : ZMod p) = 0) : p ∣ k.natAbs := by
  have hd : (p : ℤ) ∣ k := (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h
  have hd2 : (p : ℤ) ∣ (k.natAbs : ℤ) := (Int.dvd_natAbs).mpr hd
  exact_mod_cast hd2

end cHnezero

open cHnezero

/-- **The content criterion for the critical polynomial.**  For `p ≥ 5` and triples `a b : Fin 3 → ℕ`,
if `p` does not divide the content `contAB a b = gcd_k |e_k(a) - e_k(b)|` of the pair, then the
critical polynomial `cH p a b = A' B - B' A` (with `A = ∏_l (X + a_l)`, `B = ∏_l (X + b_l)` over
`ZMod p`) is nonzero.

Route (a pure coefficient computation).  With `A = X^3 + A₁X² + A₂X + A₃`,
`B = X^3 + B₁X² + B₂X + B₃` and `g = A - B = c₂X² + c₁X + c₀` (`c_j` the casts of
`esymm3 a j - esymm3 b j`), one has `cH = g'B - gB'` and
`cH = C(-c₂)·X^4 + C(-2c₁)·X^3 + C(c₂B₂ - c₁B₁ - 3c₀)·X^2 + …`; so `cH = 0` forces
`c₂ = 0`, `c₁ = 0` (as `2 ≠ 0` in `ZMod p`) and then `3 c₀ = 0` (as `3 ≠ 0` in `ZMod p`), i.e. `p`
divides all three `e_k(a) - e_k(b)`, hence `contAB a b`. -/
theorem cH_ne_zero_of_not_dvd_contAB {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ)
    (hc : ¬ p ∣ Work.LinnikBurgess.contAB a b) :
    Commons.NumberTheory.DirichletCharacter.cH p a b ≠ 0 := by
  intro hH
  apply hc
  set A1 : ZMod p := ((esymm3 a 0 : ℤ) : ZMod p) with hA1
  set A2 : ZMod p := ((esymm3 a 1 : ℤ) : ZMod p) with hA2
  set A3 : ZMod p := ((esymm3 a 2 : ℤ) : ZMod p) with hA3
  set B1 : ZMod p := ((esymm3 b 0 : ℤ) : ZMod p) with hB1
  set B2 : ZMod p := ((esymm3 b 1 : ℤ) : ZMod p) with hB2
  set B3 : ZMod p := ((esymm3 b 2 : ℤ) : ZMod p) with hB3
  have hca : Commons.NumberTheory.DirichletCharacter.cA p a
      = Polynomial.X^3 + Polynomial.C A1 * Polynomial.X^2 + Polynomial.C A2 * Polynomial.X
        + Polynomial.C A3 := by
    rw [cA_eq, ← hA1, ← hA2, ← hA3]
  have hcb : Commons.NumberTheory.DirichletCharacter.cA p b
      = Polynomial.X^3 + Polynomial.C B1 * Polynomial.X^2 + Polynomial.C B2 * Polynomial.X
        + Polynomial.C B3 := by
    rw [cA_eq, ← hB1, ← hB2, ← hB3]
  have hzero : Polynomial.derivative (Commons.NumberTheory.DirichletCharacter.cA p a)
        * Commons.NumberTheory.DirichletCharacter.cA p b
      - Polynomial.derivative (Commons.NumberTheory.DirichletCharacter.cA p b)
        * Commons.NumberTheory.DirichletCharacter.cA p a = 0 := by
    simpa only [Commons.NumberTheory.DirichletCharacter.cH] using hH
  have hkey : Polynomial.derivative (Commons.NumberTheory.DirichletCharacter.cA p a)
        * Commons.NumberTheory.DirichletCharacter.cA p b
      - Polynomial.derivative (Commons.NumberTheory.DirichletCharacter.cA p b)
        * Commons.NumberTheory.DirichletCharacter.cA p a
      = Polynomial.C (B1 - A1) * Polynomial.X^4
        + Polynomial.C (2*(B2 - A2)) * Polynomial.X^3
        + Polynomial.C (-A2*B1 + A1*B2 + 3*(B3-A3)) * Polynomial.X^2
        + Polynomial.C (2*A1*B3 - 2*B1*A3) * Polynomial.X
        + Polynomial.C (A2*B3 - B2*A3) := by
    rw [hca, hcb]
    exact wronskian_identity A1 A2 A3 B1 B2 B3
  -- coefficient of X^4
  have h4 : B1 - A1 = 0 := by
    have h := congrArg (fun q : Polynomial (ZMod p) => q.coeff 4) hkey
    rw [hzero, Polynomial.coeff_zero, coeff_four] at h
    exact h.symm
  -- coefficient of X^3
  have h3 : 2*(B2 - A2) = 0 := by
    have h := congrArg (fun q : Polynomial (ZMod p) => q.coeff 3) hkey
    rw [hzero, Polynomial.coeff_zero, coeff_three] at h
    exact h.symm
  -- coefficient of X^2
  have h2 : -A2*B1 + A1*B2 + 3*(B3 - A3) = 0 := by
    have h := congrArg (fun q : Polynomial (ZMod p) => q.coeff 2) hkey
    rw [hzero, Polynomial.coeff_zero, coeff_two] at h
    exact h.symm
  -- 2 and 3 are nonzero in ZMod p
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hA1B1 : A1 = B1 := (sub_eq_zero.mp h4).symm
  have hA2B2 : A2 = B2 := by
    have : B2 - A2 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h h2ne
      · exact h
    exact (sub_eq_zero.mp this).symm
  have hA3B3 : A3 = B3 := by
    have hkey3 : 3*(B3 - A3) = 0 := by
      rw [hA1B1, hA2B2, show -B2*B1 + B1*B2 = 0 by ring] at h2
      simpa using h2
    have : B3 - A3 = 0 := by
      rcases mul_eq_zero.mp hkey3 with h | h
      · exact absurd h h3ne
      · exact h
    exact (sub_eq_zero.mp this).symm
  -- divisibility of the contents
  have hsub0 : ((esymm3 a 0 - esymm3 b 0 : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, ← hA1, ← hB1, hA1B1, sub_self]
  have hsub1 : ((esymm3 a 1 - esymm3 b 1 : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, ← hA2, ← hB2, hA2B2, sub_self]
  have hsub2 : ((esymm3 a 2 - esymm3 b 2 : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, ← hA3, ← hB3, hA3B3, sub_self]
  refine Nat.dvd_gcd (dvd_natAbs_of_zmod_eq p _ hsub0) (Nat.dvd_gcd (dvd_natAbs_of_zmod_eq p _ hsub1)
    (dvd_natAbs_of_zmod_eq p _ hsub2))

end Work.LinnikBurgess
