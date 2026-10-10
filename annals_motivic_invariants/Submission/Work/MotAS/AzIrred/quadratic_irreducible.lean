import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.AzIrred

open Polynomial

/-- Coefficient of `X ^ 2` in a quadratic written in coefficient form. -/
private lemma coeffTwo {R : Type*} [CommRing R] (a b c : R) :
    (C a * X ^ 2 + C b * X + C c).coeff 2 = a := by simp

/-- Coefficient of `X` in a quadratic written in coefficient form. -/
private lemma coeffOne {R : Type*} [CommRing R] (a b c : R) :
    (C a * X ^ 2 + C b * X + C c).coeff 1 = b := by simp

/-- Constant coefficient of a quadratic written in coefficient form. -/
private lemma coeffZero {R : Type*} [CommRing R] (a b c : R) :
    (C a * X ^ 2 + C b * X + C c).coeff 0 = c := by simp

/-- A product of two polynomials of `natDegree` `1` expanded in coefficient form. -/
private lemma mul_eq_of_natDegree_eq_one {R : Type*} [CommRing R] {p q : R[X]}
    (hp : p.natDegree = 1) (hq : q.natDegree = 1) :
    p * q = C (p.coeff 1 * q.coeff 1) * X ^ 2
      + C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X
      + C (p.coeff 0 * q.coeff 0) := by
  have hpdeg : p.degree ≤ 1 := Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hp)
  have hqdeg : q.degree ≤ 1 := Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hq)
  conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hpdeg]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hqdeg]
  simp only [Polynomial.C_mul, Polynomial.C_add]
  first | refl_ring1 | ring

theorem quadratic_irreducible {R : Type*} [CommRing R] [IsDomain R] (A B c : R)
    (hA : A ≠ 0) (hcop : ∀ d, d ∣ A → d ∣ B → d ∣ c → IsUnit d)
    (hnsq : ∀ s : R, B ^ 2 - 4 * A * c ≠ s ^ 2) :
    Irreducible (Polynomial.C A * Polynomial.X ^ 2 + Polynomial.C B * Polynomial.X
      + Polynomial.C c) := by
  set f : R[X] := C A * X ^ 2 + C B * X + C c with hf
  have hf2 : f.coeff 2 = A := by rw [hf]; exact coeffTwo A B c
  have hf1 : f.coeff 1 = B := by rw [hf]; exact coeffOne A B c
  have hf0 : f.coeff 0 = c := by rw [hf]; exact coeffZero A B c
  have hdeg : f.natDegree = 2 := by rw [hf]; exact Polynomial.natDegree_quadratic hA
  have hfne : f ≠ 0 := by
    intro h0
    exact hA (by rw [← hf2, h0]; simp)
  refine ⟨?_, ?_⟩
  · exact Polynomial.not_isUnit_of_natDegree_pos f (by rw [hdeg]; norm_num)
  · intro p q hpq
    have hp0 : p ≠ 0 := fun hp => hfne (by rw [hpq, hp, zero_mul])
    have hq0 : q ≠ 0 := fun hq => hfne (by rw [hpq, hq, mul_zero])
    have hsum : p.natDegree + q.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul hp0 hq0, ← hpq, hdeg]
    rcases Nat.lt_or_ge p.natDegree 1 with hp_lt | hp_ge
    · -- the left factor is a nonzero constant: it divides `A`, `B`, `c`
      have hpnd : p.natDegree = 0 := by omega
      have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpnd
      have hdA : p.coeff 0 ∣ A := by
        refine ⟨q.coeff 2, ?_⟩
        rw [← hf2, hpq]
        conv_lhs => rw [hpC]
        exact Polynomial.coeff_C_mul q
      have hdB : p.coeff 0 ∣ B := by
        refine ⟨q.coeff 1, ?_⟩
        rw [← hf1, hpq]
        conv_lhs => rw [hpC]
        exact Polynomial.coeff_C_mul q
      have hdc : p.coeff 0 ∣ c := by
        refine ⟨q.coeff 0, ?_⟩
        rw [← hf0, hpq]
        conv_lhs => rw [hpC]
        exact Polynomial.coeff_C_mul q
      have hh : IsUnit (C (p.coeff 0)) := Polynomial.isUnit_C.mpr (hcop _ hdA hdB hdc)
      rw [← hpC] at hh
      exact Or.inl hh
    · rcases Nat.lt_or_ge q.natDegree 1 with hq_lt | hq_ge
      · -- the right factor is a nonzero constant: it divides `A`, `B`, `c`
        have hqnd : q.natDegree = 0 := by omega
        have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqnd
        have hdA : q.coeff 0 ∣ A := by
          refine ⟨p.coeff 2, ?_⟩
          rw [← hf2, hpq]
          conv_lhs => rw [hqC]
          rw [Polynomial.coeff_mul_C]
          first | refl_ring1 | ring
        have hdB : q.coeff 0 ∣ B := by
          refine ⟨p.coeff 1, ?_⟩
          rw [← hf1, hpq]
          conv_lhs => rw [hqC]
          rw [Polynomial.coeff_mul_C]
          first | refl_ring1 | ring
        have hdc : q.coeff 0 ∣ c := by
          refine ⟨p.coeff 0, ?_⟩
          rw [← hf0, hpq]
          conv_lhs => rw [hqC]
          rw [Polynomial.coeff_mul_C]
          first | refl_ring1 | ring
        have hh : IsUnit (C (q.coeff 0)) := Polynomial.isUnit_C.mpr (hcop _ hdA hdB hdc)
        rw [← hqC] at hh
        exact Or.inr hh
      · -- both factors have `natDegree` `1`; the discriminant is then a square
        have hpnd : p.natDegree = 1 := by omega
        have hqnd : q.natDegree = 1 := by omega
        have hexp : p * q = C (p.coeff 1 * q.coeff 1) * X ^ 2
            + C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X
            + C (p.coeff 0 * q.coeff 0) := mul_eq_of_natDegree_eq_one hpnd hqnd
        have hf' : f = C (p.coeff 1 * q.coeff 1) * X ^ 2
            + C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X
            + C (p.coeff 0 * q.coeff 0) := by rw [hpq]; exact hexp
        have hA' : A = p.coeff 1 * q.coeff 1 := by
          rw [← hf2, hf']
          exact coeffTwo _ _ _
        have hB' : B = p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1 := by
          rw [← hf1, hf']
          exact coeffOne _ _ _
        have hc' : c = p.coeff 0 * q.coeff 0 := by
          rw [← hf0, hf']
          exact coeffZero _ _ _
        have hdisc : B ^ 2 - 4 * A * c = (p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1) ^ 2 := by
          rw [hA', hB', hc']; ring
        exact absurd hdisc (hnsq _)

end Work.MotAS.AzIrred
