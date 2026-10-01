import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.cH_ne_zero_of_not_dvd_contAB

/-!
# The content criterion for the critical polynomial `critN`

For `p ≥ 5` and triples `a b : Fin 3 → ℕ`, the prime power `p^k` divides *every* coefficient of
the Wronskian `critN a b = f_a' f_b - f_a f_b'` (with `f_a = ∏_l (X + a_l)` as an integral
polynomial) if and only if `p^k` divides the content `contAB a b = gcd_k |e_k(a) - e_k(b)|`.

Writing `f_a = X^3 + A₁X² + A₂X + A₃` and `f_b = X^3 + B₁X² + B₂X + B₃`, the expansion of the
Wronskian (`cHnezero.wronskian_identity`) is

`critN = C(B₁-A₁)X⁴ + C(2(B₂-A₂))X³ + C(-A₂B₁ + A₁B₂ + 3(B₃-A₃))X² + C(2A₁B₃ - 2B₁A₃)X + C(A₂B₃ - B₂A₃)`.

Since `p ≥ 5`, `2` and `3` are invertible modulo `p^k`, so the coefficients in degrees `3` and `2`
force `p^k ∣ A₂-B₂` and `p^k ∣ A₃-B₃` once `p^k ∣ A₁-B₁` is known from degree `4`; conversely,
if the three differences are divisible the displayed form shows every coefficient is.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

namespace critNcontent

/-- Explicit expansion of the cubic `∏_l (X + a_l)`. -/
lemma cubicZ_eq_expand (a : Fin 3 → ℕ) :
    cubicZ a = X^3 + C (esymm3 a 0) * X^2 + C (esymm3 a 1) * X + C (esymm3 a 2) := by
  rw [cubicZ, Fin.prod_univ_three]
  simp [esymm3]
  ring

/-- Explicit coefficient expansion of the Wronskian `critN a b`. -/
lemma critN_eq_expand (a b : Fin 3 → ℕ) :
    critN a b
      = C (esymm3 b 0 - esymm3 a 0) * X^4
        + C (2 * (esymm3 b 1 - esymm3 a 1)) * X^3
        + C (-esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
              + 3 * (esymm3 b 2 - esymm3 a 2)) * X^2
        + C (2 * esymm3 a 0 * esymm3 b 2 - 2 * esymm3 b 0 * esymm3 a 2) * X
        + C (esymm3 a 1 * esymm3 b 2 - esymm3 b 1 * esymm3 a 2) := by
  rw [critN, cubicZ_eq_expand a, cubicZ_eq_expand b]
  have h := cHnezero.wronskian_identity (esymm3 a 0) (esymm3 a 1) (esymm3 a 2)
      (esymm3 b 0) (esymm3 b 1) (esymm3 b 2)
  rw [← h]
  ring

lemma coeff_four_exp {c4 c3 c2 c1 c0 : ℤ} :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff 4 = c4 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

lemma coeff_three_exp {c4 c3 c2 c1 c0 : ℤ} :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff 3 = c3 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

lemma coeff_two_exp {c4 c3 c2 c1 c0 : ℤ} :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff 2 = c2 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

lemma coeff_one_exp {c4 c3 c2 c1 c0 : ℤ} :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff 1 = c1 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

lemma coeff_zero_exp {c4 c3 c2 c1 c0 : ℤ} :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff 0 = c0 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

lemma coeff_of_ge_five {c4 c3 c2 c1 c0 : ℤ} {n : ℕ} (hn : 5 ≤ n) :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff n = 0 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  rw [if_neg (by omega : ¬ (n = 4)), if_neg (by omega : ¬ (n = 3)),
      if_neg (by omega : ¬ (n = 2)), if_neg (by omega : ¬ (1 = n)),
      if_neg (by omega : ¬ (n = 0))]
  ring

/-- Unfolding of the content of a pair of triples. -/
lemma contAB_eq (a b : Fin 3 → ℕ) :
    contAB a b = Nat.gcd (esymm3 a 0 - esymm3 b 0).natAbs
      (Nat.gcd (esymm3 a 1 - esymm3 b 1).natAbs (esymm3 a 2 - esymm3 b 2).natAbs) := rfl

/-- A natural number divides `x.natAbs` iff, viewed in `ℤ`, it divides `x`. -/
lemma nat_dvd_natAbs_iff (d : ℕ) (x : ℤ) : d ∣ x.natAbs ↔ (d : ℤ) ∣ x := by
  have := Int.natAbs_dvd_natAbs (a := (d : ℤ)) (b := x)
  rwa [Int.natAbs_natCast] at this

end critNcontent

open critNcontent

theorem critN_content_iff {p k : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (a b : Fin 3 → ℕ) :
    (∀ n, ((p ^ k : ℕ) : ℤ) ∣ (critN a b).coeff n) ↔ p ^ k ∣ contAB a b := by
  have hp : Nat.Prime p := Fact.out
  have h2p : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h; omega
  have h3p : ¬ p ∣ 3 := fun h => by
    have := Nat.le_of_dvd (by norm_num : 0 < 3) h; omega
  have hcop2 : IsCoprime (((p ^ k : ℕ) : ℤ)) (2 : ℤ) :=
    (Nat.isCoprime_iff_coprime).mpr (Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr h2p))
  have hcop3 : IsCoprime (((p ^ k : ℕ) : ℤ)) (3 : ℤ) :=
    (Nat.isCoprime_iff_coprime).mpr (Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr h3p))
  constructor
  · -- Forward: divisibility of every coefficient forces the three differences.
    intro h
    have h4 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := by
      have hh := h 4
      rw [critN_eq_expand, coeff_four_exp] at hh
      have := (dvd_neg).mpr hh
      rwa [neg_sub] at this
    have h3 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := by
      have hh := h 3
      rw [critN_eq_expand, coeff_three_exp] at hh
      have hh2 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 b 1 - esymm3 a 1 :=
        hcop2.dvd_of_dvd_mul_left hh
      have := (dvd_neg).mpr hh2
      rwa [neg_sub] at this
    have h2 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 a 2 - esymm3 b 2 := by
      have h2c : ((p ^ k : ℕ) : ℤ) ∣ -esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
          + 3 * (esymm3 b 2 - esymm3 a 2) := by
        have hh := h 2
        rw [critN_eq_expand, coeff_two_exp] at hh
        exact hh
      have hbase : ((p ^ k : ℕ) : ℤ) ∣ (esymm3 a 0 - esymm3 b 0) * esymm3 b 1
          - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0 :=
        dvd_sub (dvd_mul_of_dvd_left h4 _) (dvd_mul_of_dvd_left h3 _)
      have hdiff : -esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
            + 3 * (esymm3 b 2 - esymm3 a 2)
          - ((esymm3 a 0 - esymm3 b 0) * esymm3 b 1
              - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0)
          = 3 * (esymm3 b 2 - esymm3 a 2) := by ring
      have h3mul : ((p ^ k : ℕ) : ℤ) ∣ 3 * (esymm3 b 2 - esymm3 a 2) := by
        have := dvd_sub h2c hbase
        rwa [hdiff] at this
      have hh2 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 b 2 - esymm3 a 2 :=
        hcop3.dvd_of_dvd_mul_left h3mul
      have := (dvd_neg).mpr hh2
      rwa [neg_sub] at this
    rw [contAB_eq]
    exact Nat.dvd_gcd ((nat_dvd_natAbs_iff _ _).mpr h4)
      (Nat.dvd_gcd ((nat_dvd_natAbs_iff _ _).mpr h3) ((nat_dvd_natAbs_iff _ _).mpr h2))
  · -- Backward: divisibility of the content gives divisibility of every coefficient.
    intro hd
    obtain ⟨hd1, hd2, hd3⟩ : p ^ k ∣ (esymm3 a 0 - esymm3 b 0).natAbs
        ∧ p ^ k ∣ (esymm3 a 1 - esymm3 b 1).natAbs
        ∧ p ^ k ∣ (esymm3 a 2 - esymm3 b 2).natAbs := by
      rw [contAB_eq, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff] at hd
      exact ⟨hd.1, hd.2.1, hd.2.2⟩
    have hD1 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := (nat_dvd_natAbs_iff _ _).mp hd1
    have hD2 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := (nat_dvd_natAbs_iff _ _).mp hd2
    have hD3 : ((p ^ k : ℕ) : ℤ) ∣ esymm3 a 2 - esymm3 b 2 := (nat_dvd_natAbs_iff _ _).mp hd3
    intro n
    rcases lt_or_ge n 5 with hn | hn
    · interval_cases n
      · rw [critN_eq_expand, coeff_zero_exp]
        have hsplit : esymm3 a 1 * esymm3 b 2 - esymm3 b 1 * esymm3 a 2
            = (esymm3 a 1 - esymm3 b 1) * esymm3 b 2
              - esymm3 b 1 * (esymm3 a 2 - esymm3 b 2) := by ring
        rw [hsplit]
        exact dvd_sub (dvd_mul_of_dvd_left hD2 _) (dvd_mul_of_dvd_right hD3 _)
      · rw [critN_eq_expand, coeff_one_exp]
        have hsplit : 2 * esymm3 a 0 * esymm3 b 2 - 2 * esymm3 b 0 * esymm3 a 2
            = 2 * ((esymm3 a 0 - esymm3 b 0) * esymm3 b 2
              - esymm3 b 0 * (esymm3 a 2 - esymm3 b 2)) := by ring
        rw [hsplit]
        exact dvd_mul_of_dvd_right
          (dvd_sub (dvd_mul_of_dvd_left hD1 _) (dvd_mul_of_dvd_right hD3 _)) 2
      · rw [critN_eq_expand, coeff_two_exp]
        have hsplit : -esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
              + 3 * (esymm3 b 2 - esymm3 a 2)
            = (esymm3 a 0 - esymm3 b 0) * esymm3 b 1
              - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0
              - 3 * (esymm3 a 2 - esymm3 b 2) := by ring
        rw [hsplit]
        exact dvd_sub (dvd_sub (dvd_mul_of_dvd_left hD1 _) (dvd_mul_of_dvd_left hD2 _))
          (dvd_mul_of_dvd_right hD3 3)
      · rw [critN_eq_expand, coeff_three_exp]
        have hsplit : 2 * (esymm3 b 1 - esymm3 a 1)
            = -(esymm3 a 1 - esymm3 b 1) * 2 := by ring
        rw [hsplit]
        exact dvd_mul_of_dvd_left (dvd_neg.mpr hD2) 2
      · rw [critN_eq_expand, coeff_four_exp]
        have := (dvd_neg).mpr hD1
        rwa [neg_sub] at this
    · rw [critN_eq_expand, coeff_of_ge_five hn]
      exact dvd_zero _

end Work.LinnikBurgess
