import Mathlib
import Submission.Work.MotAS.FdivASGen3
import Submission.Work.MotAS.CensusASGen
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Work.MotAS

open MvPolynomial

/-!
# `Work.MotAS.censusAS_sAS_ne_zero`
-/

/-- Transport of the AS secant quintic along a ring homomorphism. -/
lemma map_kleinSecAS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (y : Fin 5 → R) :
    φ (kleinSecAS a b g y) = kleinSecAS (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinSecAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]

/-- The sparse evaluation of the AS secant quintic. -/
lemma kleinSecAS_sparse {R : Type*} [CommRing R] (a b g Y0 Y2 Y4 : R) :
    kleinSecAS a b g (fun i => ![Y0, 0, Y2, 0, Y4] i) =
  (-a^(10:ℕ) + a^(5:ℕ)*b^(5:ℕ) + b^(10:ℕ)) * (Y0^(5:ℕ) * Y2^(0:ℕ) * Y4^(0:ℕ)) +
  (a^(10:ℕ) - a^(5:ℕ)*b^(5:ℕ) - b^(10:ℕ)) * (Y0^(4:ℕ) * Y2^(0:ℕ) * Y4^(1:ℕ)) +
  (2*a^(10:ℕ) - 2*a^(5:ℕ)*b^(5:ℕ) - 2*b^(10:ℕ)) * (Y0^(3:ℕ) * Y2^(2:ℕ) * Y4^(0:ℕ)) +
  (-a^(10:ℕ) - 2*a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) - a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) + a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - 2*a*b^(9:ℕ) + b^(10:ℕ)) * (Y0^(3:ℕ) * Y2^(0:ℕ) * Y4^(2:ℕ)) +
  (-a^(10:ℕ) + 2*a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) - a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)) * (Y0^(2:ℕ) * Y2^(2:ℕ) * Y4^(1:ℕ)) +
  (a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ) + 2*a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)) * (Y0^(2:ℕ) * Y2^(1:ℕ) * Y4^(2:ℕ)) +
  (a^(10:ℕ) - 2*a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) - a^(6:ℕ)*b^(4:ℕ) - a^(5:ℕ)*b^(5:ℕ) + a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) - 2*a*b^(9:ℕ) - b^(10:ℕ)) * (Y0^(2:ℕ) * Y2^(0:ℕ) * Y4^(3:ℕ)) +
  (-a^(10:ℕ) + 2*a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) - a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)) * (Y0^(1:ℕ) * Y2^(4:ℕ) * Y4^(0:ℕ)) +
  (-a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) - a^(7:ℕ)*b^(3:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ) + a*b^(9:ℕ)) * (Y0^(1:ℕ) * Y2^(3:ℕ) * Y4^(1:ℕ)) +
  (2*a^(10:ℕ) + 2*a^(9:ℕ)*b + a^(8:ℕ)*b^(2:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) - 2*a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ) - a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) - 2*b^(10:ℕ)) * (Y0^(1:ℕ) * Y2^(2:ℕ) * Y4^(2:ℕ)) +
  (-a^(10:ℕ)*g^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) - a^(2:ℕ)*b^(8:ℕ) + b^(10:ℕ)*g^(2:ℕ)) * (Y0^(1:ℕ) * Y2^(1:ℕ) * Y4^(3:ℕ)) +
  (-a^(10:ℕ) + 2*a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)) * (Y0^(1:ℕ) * Y2^(0:ℕ) * Y4^(4:ℕ)) +
  (-a^(10:ℕ)*g^(2:ℕ) + 2*a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) - a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - 2*a*b^(9:ℕ) + b^(10:ℕ)*g^(2:ℕ)) * (Y0^(0:ℕ) * Y2^(5:ℕ) * Y4^(0:ℕ)) +
  (-a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)) * (Y0^(0:ℕ) * Y2^(4:ℕ) * Y4^(1:ℕ)) +
  (2*a^(10:ℕ)*g^(2:ℕ) - a^(9:ℕ)*b + a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) + a*b^(9:ℕ) - 2*b^(10:ℕ)*g^(2:ℕ)) * (Y0^(0:ℕ) * Y2^(3:ℕ) * Y4^(2:ℕ)) +
  (-a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)) * (Y0^(0:ℕ) * Y2^(2:ℕ) * Y4^(3:ℕ)) +
  (-a^(10:ℕ)*g^(2:ℕ) - a^(9:ℕ)*b*g^(2:ℕ) - a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ)*g^(2:ℕ) + 2*a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*g^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ)*g^(2:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ)*g^(2:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*g^(2:ℕ) - a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ)*g^(2:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)*g^(2:ℕ) + a*b^(9:ℕ) + b^(10:ℕ)*g^(2:ℕ)) * (Y0^(0:ℕ) * Y2^(1:ℕ) * Y4^(4:ℕ)) +
  (-a^(10:ℕ)*g^(4:ℕ) + a^(9:ℕ)*b*g^(2:ℕ) + 2*a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ)*g^(2:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) + 2*a^(4:ℕ)*b^(6:ℕ)*g^(2:ℕ) - a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)*g^(2:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)*g^(4:ℕ)) * (Y0^(0:ℕ) * Y2^(0:ℕ) * Y4^(5:ℕ)) := by
  simp only [kleinSecAS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1

/-- Coefficient at `a + b` of a product, when the degrees are bounded. -/
lemma coeff_mul_top {R : Type*} [Semiring R] (f g : Polynomial R) (a b : ℕ)
    (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  rcases lt_or_eq_of_le hf with hf' | hf'
  · have h1 : (f * g).natDegree ≤ f.natDegree + g.natDegree := Polynomial.natDegree_mul_le
    have h2 : (f * g).natDegree < a + b := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h2,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < a), zero_mul]
  rcases lt_or_eq_of_le hg with hg' | hg'
  · have h1 : (f * g).natDegree ≤ f.natDegree + g.natDegree := Polynomial.natDegree_mul_le
    have h2 : (f * g).natDegree < a + b := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h2,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < b), mul_zero]
  rw [← hf', ← hg']
  exact Polynomial.coeff_mul_degree_add_degree f g

/-- The leading coefficient of a fifth power of a polynomial of degree at most `2`. -/
lemma coeff_pow_five_top {R : Type*} [CommRing R] [NoZeroDivisors R] (p : Polynomial R)
    (hp : p.natDegree ≤ 2) : (p ^(5:ℕ)).coeff 10 = (p.coeff 2) ^(5:ℕ) := by
  rcases lt_or_eq_of_le hp with h | h
  · have h1 : (p ^(5:ℕ)).natDegree ≤ 5 * p.natDegree := Polynomial.natDegree_pow_le
    have h2 : (p ^(5:ℕ)).natDegree < 10 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h2,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < 2)]
    refl_ring1
  · have h3 : (p ^(5:ℕ)).natDegree = 5 * p.natDegree := Polynomial.natDegree_pow p 5
    rw [show (10:ℕ) = (p^(5:ℕ)).natDegree from by omega]
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_pow]
    rw [show p.coeff 2 = p.leadingCoeff from by rw [Polynomial.leadingCoeff, h]]

/-- Vanishing of the `X^10`-coefficient of a monomial of `X`-degree at most `9`. -/
lemma coeff_ten_mon {R : Type*} [CommRing R] {Y0 Y2 Y4 : Polynomial R} (h0 : Y0.natDegree ≤ 2)
    (h2 : Y2.natDegree ≤ 1) (h4 : Y4.natDegree ≤ 0) (e0 e2 e4 : ℕ) (he : 2 * e0 + e2 ≤ 9) :
    (Y0 ^ e0 * Y2 ^ e2 * Y4 ^ e4).coeff 10 = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hA : (Y0 ^ e0).natDegree ≤ e0 * 2 :=
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left e0 h0)
  have hB : (Y2 ^ e2).natDegree ≤ e2 * 1 :=
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left e2 h2)
  have hD : (Y4 ^ e4).natDegree ≤ e4 * 0 :=
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left e4 h4)
  calc (Y0 ^ e0 * Y2 ^ e2 * Y4 ^ e4).natDegree
      ≤ (Y0 ^ e0 * Y2 ^ e2).natDegree + (Y4 ^ e4).natDegree := Polynomial.natDegree_mul_le
    _ ≤ ((Y0 ^ e0).natDegree + (Y2 ^ e2).natDegree) + (Y4 ^ e4).natDegree := by
        gcongr; exact Polynomial.natDegree_mul_le
    _ ≤ (e0 * 2 + e2 * 1) + e4 * 0 := by gcongr
    _ < 10 := by omega

/-- The `X^10`-coefficient of the leading monomial of the sparse evaluation. -/
lemma coeff_ten_top {R : Type*} [CommRing R] [NoZeroDivisors R] {Y0 Y2 Y4 : Polynomial R}
    (h0 : Y0.natDegree ≤ 2) : (Y0 ^(5:ℕ) * Y2 ^(0:ℕ) * Y4 ^(0:ℕ)).coeff 10 = (Y0.coeff 2) ^(5:ℕ) := by
  simp only [pow_zero, mul_one]
  exact coeff_pow_five_top Y0 h0

/-- **The `X^10`-coefficient of the sparse evaluation.** -/
lemma coeff_ten_sparse {K : Type*} [CommRing K] [NoZeroDivisors K] (a b g : K)
    (Y0 Y2 Y4 : Polynomial K) (h0 : Y0.natDegree ≤ 2) (h2 : Y2.natDegree ≤ 1)
    (h4 : Y4.natDegree ≤ 0) :
    (kleinSecAS (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
      (fun i => ![Y0, 0, Y2, 0, Y4] i)).coeff 10
      = (-(a ^(10:ℕ)) + a ^(5:ℕ) * b ^(5:ℕ) + b ^(10:ℕ)) * (Y0.coeff 2) ^(5:ℕ) := by
  rw [kleinSecAS_sparse]
  have hc0 : (-(Polynomial.C a)^(10:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) + (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ) + a^(5:ℕ)*b^(5:ℕ) + b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc1 : ((Polynomial.C a)^(10:ℕ) - (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) - (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (a^(10:ℕ) - a^(5:ℕ)*b^(5:ℕ) - b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc2 : (2*(Polynomial.C a)^(10:ℕ) - 2*(Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) - 2*(Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (2*a^(10:ℕ) - 2*a^(5:ℕ)*b^(5:ℕ) - 2*b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc3 : (-(Polynomial.C a)^(10:ℕ) - 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) - (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) + (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) + (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ) - 2*a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) - a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) + a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - 2*a*b^(9:ℕ) + b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc4 : (-(Polynomial.C a)^(10:ℕ) + 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) + 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) - (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) - 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ) + 2*a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) - a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc5 : ((Polynomial.C a)^(9:ℕ)*(Polynomial.C b) + 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - (Polynomial.C a)*(Polynomial.C b)^(9:ℕ) : Polynomial K) = Polynomial.C (a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ) + 2*a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc6 : ((Polynomial.C a)^(10:ℕ) - 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) - (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) - (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) + (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) - (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (a^(10:ℕ) - 2*a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) - a^(6:ℕ)*b^(4:ℕ) - a^(5:ℕ)*b^(5:ℕ) + a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) - 2*a*b^(9:ℕ) - b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc7 : (-(Polynomial.C a)^(10:ℕ) + 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) + 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) - (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) - 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ) + 2*a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) - a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc8 : (-(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) - 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) - 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) + (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) - 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + (Polynomial.C a)*(Polynomial.C b)^(9:ℕ) : Polynomial K) = Polynomial.C (-a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) - a^(7:ℕ)*b^(3:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) - 2*a^(2:ℕ)*b^(8:ℕ) + a*b^(9:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc9 : (2*(Polynomial.C a)^(10:ℕ) + 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) + (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) - 2*(Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) - (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) + 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) - (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) - 2*(Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (2*a^(10:ℕ) + 2*a^(9:ℕ)*b + a^(8:ℕ)*b^(2:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) - 2*a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ) - a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) - 2*b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc10 : (-(Polynomial.C a)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ)*(Polynomial.C g)^(2:ℕ) - 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) - (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + (Polynomial.C b)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ)*g^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) - a^(2:ℕ)*b^(8:ℕ) + b^(10:ℕ)*g^(2:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc11 : (-(Polynomial.C a)^(10:ℕ) + 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) - (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ) + 2*a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) - a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc12 : (-(Polynomial.C a)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) + 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) + 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) - (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ)*g^(2:ℕ) + 2*a^(9:ℕ)*b + 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) - a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - a^(4:ℕ)*b^(6:ℕ) - a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - 2*a*b^(9:ℕ) + b^(10:ℕ)*g^(2:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc13 : (-(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) - 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) + (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - (Polynomial.C a)*(Polynomial.C b)^(9:ℕ) : Polynomial K) = Polynomial.C (-a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc14 : (2*(Polynomial.C a)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(9:ℕ)*(Polynomial.C b) + (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) - 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) - 2*(Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ)*(Polynomial.C g)^(2:ℕ) - 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) + 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) + (Polynomial.C a)*(Polynomial.C b)^(9:ℕ) - 2*(Polynomial.C b)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) : Polynomial K) = Polynomial.C (2*a^(10:ℕ)*g^(2:ℕ) - a^(9:ℕ)*b + a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) + a*b^(9:ℕ) - 2*b^(10:ℕ)*g^(2:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc15 : (-(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) - 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - (Polynomial.C a)*(Polynomial.C b)^(9:ℕ) : Polynomial K) = Polynomial.C (-a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc16 : (-(Polynomial.C a)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(9:ℕ)*(Polynomial.C b)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - (Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ)*(Polynomial.C g)^(2:ℕ) + 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) - 2*(Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ)*(Polynomial.C g)^(2:ℕ) + (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ)*(Polynomial.C g)^(2:ℕ) - 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ)*(Polynomial.C g)^(2:ℕ) - 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ)*(Polynomial.C g)^(2:ℕ) - 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) - 2*(Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + (Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ)*(Polynomial.C g)^(2:ℕ) + 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - (Polynomial.C a)*(Polynomial.C b)^(9:ℕ)*(Polynomial.C g)^(2:ℕ) + (Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ)*(Polynomial.C g)^(2:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ)*g^(2:ℕ) - a^(9:ℕ)*b*g^(2:ℕ) - a^(9:ℕ)*b - a^(8:ℕ)*b^(2:ℕ)*g^(2:ℕ) + 2*a^(8:ℕ)*b^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*g^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ)*g^(2:ℕ) - 2*a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(2:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ)*g^(2:ℕ) - 2*a^(4:ℕ)*b^(6:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*g^(2:ℕ) - a^(3:ℕ)*b^(7:ℕ) + a^(2:ℕ)*b^(8:ℕ)*g^(2:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)*g^(2:ℕ) + a*b^(9:ℕ) + b^(10:ℕ)*g^(2:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  have hc17 : (-(Polynomial.C a)^(10:ℕ)*(Polynomial.C g)^(4:ℕ) + (Polynomial.C a)^(9:ℕ)*(Polynomial.C b)*(Polynomial.C g)^(2:ℕ) + 2*(Polynomial.C a)^(9:ℕ)*(Polynomial.C b) - 2*(Polynomial.C a)^(8:ℕ)*(Polynomial.C b)^(2:ℕ) + (Polynomial.C a)^(7:ℕ)*(Polynomial.C b)^(3:ℕ) + 2*(Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ)*(Polynomial.C g)^(2:ℕ) + (Polynomial.C a)^(6:ℕ)*(Polynomial.C b)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ)*(Polynomial.C g)^(4:ℕ) + (Polynomial.C a)^(5:ℕ)*(Polynomial.C b)^(5:ℕ) + 2*(Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ)*(Polynomial.C g)^(2:ℕ) - (Polynomial.C a)^(4:ℕ)*(Polynomial.C b)^(6:ℕ) + (Polynomial.C a)^(3:ℕ)*(Polynomial.C b)^(7:ℕ) + 2*(Polynomial.C a)^(2:ℕ)*(Polynomial.C b)^(8:ℕ) - (Polynomial.C a)*(Polynomial.C b)^(9:ℕ)*(Polynomial.C g)^(2:ℕ) + 2*(Polynomial.C a)*(Polynomial.C b)^(9:ℕ) + (Polynomial.C b)^(10:ℕ)*(Polynomial.C g)^(4:ℕ) : Polynomial K) = Polynomial.C (-a^(10:ℕ)*g^(4:ℕ) + a^(9:ℕ)*b*g^(2:ℕ) + 2*a^(9:ℕ)*b - 2*a^(8:ℕ)*b^(2:ℕ) + a^(7:ℕ)*b^(3:ℕ) + 2*a^(6:ℕ)*b^(4:ℕ)*g^(2:ℕ) + a^(6:ℕ)*b^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ)*g^(4:ℕ) + a^(5:ℕ)*b^(5:ℕ) + 2*a^(4:ℕ)*b^(6:ℕ)*g^(2:ℕ) - a^(4:ℕ)*b^(6:ℕ) + a^(3:ℕ)*b^(7:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ) - a*b^(9:ℕ)*g^(2:ℕ) + 2*a*b^(9:ℕ) + b^(10:ℕ)*g^(4:ℕ)) := by
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.C_inj] <;> ring

  simp only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rw [show (Y0 ^(5:ℕ) * Y2 ^(0:ℕ) * Y4 ^(0:ℕ)).coeff 10 = (Y0.coeff 2) ^(5:ℕ) from coeff_ten_top h0
    , coeff_ten_mon h0 h2 h4 4 0 1 (by norm_num)
    , coeff_ten_mon h0 h2 h4 3 2 0 (by norm_num)
    , coeff_ten_mon h0 h2 h4 3 0 2 (by norm_num)
    , coeff_ten_mon h0 h2 h4 2 2 1 (by norm_num)
    , coeff_ten_mon h0 h2 h4 2 1 2 (by norm_num)
    , coeff_ten_mon h0 h2 h4 2 0 3 (by norm_num)
    , coeff_ten_mon h0 h2 h4 1 4 0 (by norm_num)
    , coeff_ten_mon h0 h2 h4 1 3 1 (by norm_num)
    , coeff_ten_mon h0 h2 h4 1 2 2 (by norm_num)
    , coeff_ten_mon h0 h2 h4 1 1 3 (by norm_num)
    , coeff_ten_mon h0 h2 h4 1 0 4 (by norm_num)
    , coeff_ten_mon h0 h2 h4 0 5 0 (by norm_num)
    , coeff_ten_mon h0 h2 h4 0 4 1 (by norm_num)
    , coeff_ten_mon h0 h2 h4 0 3 2 (by norm_num)
    , coeff_ten_mon h0 h2 h4 0 2 3 (by norm_num)
    , coeff_ten_mon h0 h2 h4 0 1 4 (by norm_num)
    , coeff_ten_mon h0 h2 h4 0 0 5 (by norm_num)
    ]
  refl_ring1

/-- **The source ruling quintic of the AS chart is a non-zero polynomial.** -/
theorem censusAS_sAS_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 := by
  intro h0
  have hd : aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ) ≠ 0 := aK_sq_sub_ne D hD
  -- the substitution `X₀ ↦ 0, X₁ ↦ X, X₂ ↦ 0`
  set Ψ : MvPolynomial (Fin 3) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] Polynomial (RatFunc 𝕜) :=
    MvPolynomial.aeval
      (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial (RatFunc 𝕜)) i)
    with hΨdef
  -- the image of the chart vector
  set Y0 : Polynomial (RatFunc 𝕜) := Polynomial.C (288 : RatFunc 𝕜) *
      (Polynomial.C (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * aK D ^(2:ℕ) + 2 * bK D ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * aK D ^(2:ℕ) - aK D * bK D - 2 * bK D ^(2:ℕ)))) with hY0def
  set Y4 : Polynomial (RatFunc 𝕜) := (576 : Polynomial (RatFunc 𝕜)) *
      ((Polynomial.C (aK D)) ^(2:ℕ) - Polynomial.C (aK D) * Polynomial.C (bK D)
        - (Polynomial.C (bK D)) ^(2:ℕ)) with hY4def
  set Y2 : Polynomial (RatFunc 𝕜) := Y4 * Polynomial.X with hY2def
  -- the values of `Ψ` on the chart data
  have hQΨ : Ψ (kleinQAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
        (Work.MotK.chart3 (RatFunc 𝕜)))
      = Polynomial.C (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * aK D ^(2:ℕ) + 2 * bK D ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * aK D ^(2:ℕ) - aK D * bK D - 2 * bK D ^(2:ℕ))) := by
    have h1c : (Work.MotK.chart3 (RatFunc 𝕜)) 0 = (0 : MvPolynomial (Fin 3) (RatFunc 𝕜)) := rfl
    have h2c : (Work.MotK.chart3 (RatFunc 𝕜)) 1 = MvPolynomial.X 0 := rfl
    have h3c : (Work.MotK.chart3 (RatFunc 𝕜)) 2 = MvPolynomial.X 1 := rfl
    have h4c : (Work.MotK.chart3 (RatFunc 𝕜)) 3 = MvPolynomial.X 2 := rfl
    have h5c : (Work.MotK.chart3 (RatFunc 𝕜)) 4 = (1 : MvPolynomial (Fin 3) (RatFunc 𝕜)) := rfl
    simp only [hΨdef, kleinQAS, h1c, h2c, h3c, h4c, h5c, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, map_zero, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      ← Polynomial.C_eq_algebraMap]
    simp
    refl_ring1
  have hBΨ : Ψ (kleinBilinAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
        (pAS (RatFunc 𝕜)) (Work.MotK.chart3 (RatFunc 𝕜)))
      = -(576 : Polynomial (RatFunc 𝕜)) * ((Polynomial.C (aK D)) ^(2:ℕ)
          - Polynomial.C (aK D) * Polynomial.C (bK D) - (Polynomial.C (bK D)) ^(2:ℕ)) := by
    rw [show kleinBilinAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D)) (pAS (RatFunc 𝕜))
        (Work.MotK.chart3 (RatFunc 𝕜)) = linAS (aK D) (bK D) from rfl, linAS_eq, hΨdef]
    simp only [map_mul, map_sub, map_pow, map_neg, map_ofNat, MvPolynomial.aeval_C,
      ← Polynomial.C_eq_algebraMap] <;> ring
  have hpASΨ : ∀ i : Fin 5, Ψ (pAS (RatFunc 𝕜) i)
      = Polynomial.C (if i = 0 then (288 : RatFunc 𝕜) else 0) := by
    intro i
    rw [hΨdef]
    simp only [pAS, MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
  have hchartΨ : ∀ i : Fin 5, Ψ (Work.MotK.chart3 (RatFunc 𝕜) i)
      = ![0, 0, Polynomial.X, 0, 1] i := by
    intro i
    rw [hΨdef]
    fin_cases i <;> simp [Work.MotK.chart3, MvPolynomial.aeval_X]
  have hvec : (fun i => Ψ (kleinStereoAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
        (pAS (RatFunc 𝕜)) (Work.MotK.chart3 (RatFunc 𝕜)) i)) = ![Y0, 0, Y2, 0, Y4] := by
    funext i
    fin_cases i <;>
      · simp only [kleinStereoAS, map_mul, map_sub, hpASΨ, hchartΨ, hQΨ, hBΨ, hY0def, hY2def,
          hY4def] <;> simp <;> ring
  -- the transport of `kleinSecAS` along `Ψ`
  have hΨ : Ψ (sAS (aK D) (bK D) (Work.MotV.fAS 𝕜))
      = kleinSecAS (Polynomial.C (aK D)) (Polynomial.C (bK D)) (Polynomial.C (Work.MotV.fAS 𝕜))
          (fun i => ![Y0, 0, Y2, 0, Y4] i) := by
    rw [show sAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
        = kleinSecAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
            (MvPolynomial.C (Work.MotV.fAS 𝕜))
            (kleinStereoAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D)) (pAS (RatFunc 𝕜))
              (Work.MotK.chart3 (RatFunc 𝕜))) from rfl]
    change (Ψ : MvPolynomial (Fin 3) (RatFunc 𝕜) →+* Polynomial (RatFunc 𝕜))
        (kleinSecAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
          (MvPolynomial.C (Work.MotV.fAS 𝕜))
          (kleinStereoAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D)) (pAS (RatFunc 𝕜))
            (Work.MotK.chart3 (RatFunc 𝕜))))
      = kleinSecAS (Polynomial.C (aK D)) (Polynomial.C (bK D)) (Polynomial.C (Work.MotV.fAS 𝕜))
          (fun i => ![Y0, 0, Y2, 0, Y4] i)
    rw [map_kleinSecAS (φ := (Ψ : MvPolynomial (Fin 3) (RatFunc 𝕜) →+* Polynomial (RatFunc 𝕜)))]
    have hCa : (Ψ : MvPolynomial (Fin 3) (RatFunc 𝕜) →+* Polynomial (RatFunc 𝕜))
        (MvPolynomial.C (aK D)) = Polynomial.C (aK D) := by
      rw [hΨdef]
      show (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial (RatFunc 𝕜)) i))
          (MvPolynomial.C (aK D)) = Polynomial.C (aK D)
      rw [MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
    have hCb : (Ψ : MvPolynomial (Fin 3) (RatFunc 𝕜) →+* Polynomial (RatFunc 𝕜))
        (MvPolynomial.C (bK D)) = Polynomial.C (bK D) := by
      rw [hΨdef]
      show (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial (RatFunc 𝕜)) i))
          (MvPolynomial.C (bK D)) = Polynomial.C (bK D)
      rw [MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
    have hCg : (Ψ : MvPolynomial (Fin 3) (RatFunc 𝕜) →+* Polynomial (RatFunc 𝕜))
        (MvPolynomial.C (Work.MotV.fAS 𝕜)) = Polynomial.C (Work.MotV.fAS 𝕜) := by
      rw [hΨdef]
      show (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial (RatFunc 𝕜)) i))
          (MvPolynomial.C (Work.MotV.fAS 𝕜)) = Polynomial.C (Work.MotV.fAS 𝕜)
      rw [MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
    rw [hCa, hCb, hCg]
    change kleinSecAS (Polynomial.C (aK D)) (Polynomial.C (bK D))
        (Polynomial.C (Work.MotV.fAS 𝕜))
        (fun i => Ψ (kleinStereoAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
          (pAS (RatFunc 𝕜)) (Work.MotK.chart3 (RatFunc 𝕜)) i))
      = kleinSecAS (Polynomial.C (aK D)) (Polynomial.C (bK D)) (Polynomial.C (Work.MotV.fAS 𝕜))
          (fun i => ![Y0, 0, Y2, 0, Y4] i)
    rw [hvec]
  have hzero : kleinSecAS (Polynomial.C (aK D)) (Polynomial.C (bK D))
      (Polynomial.C (Work.MotV.fAS 𝕜)) (fun i => ![Y0, 0, Y2, 0, Y4] i) = 0 := by
    rw [← hΨ, h0, map_zero]
  -- degree bounds
  have hY0deg : Y0.natDegree ≤ 2 := by
    rw [hY0def]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    have hA : (Polynomial.C (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        ).natDegree ≤ 2 :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) (by simpa using Polynomial.natDegree_X_pow_le 2)
    have hB : (Polynomial.C (-(2 * aK D ^(2:ℕ) + 2 * bK D ^(2:ℕ))) * Polynomial.X).natDegree ≤ 2 :=
      le_trans (le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le)
        (by norm_num)
    have hC : (Polynomial.C (-(2 * aK D ^(2:ℕ) - aK D * bK D - 2 * bK D ^(2:ℕ)))).natDegree ≤ 2 :=
      le_trans (le_of_eq (Polynomial.natDegree_C _)) (by norm_num)
    calc (Polynomial.C (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
          + Polynomial.C (-(2 * aK D ^(2:ℕ) + 2 * bK D ^(2:ℕ))) * Polynomial.X
          + Polynomial.C (-(2 * aK D ^(2:ℕ) - aK D * bK D - 2 * bK D ^(2:ℕ)))).natDegree
        ≤ max (Polynomial.C (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
            + Polynomial.C (-(2 * aK D ^(2:ℕ) + 2 * bK D ^(2:ℕ))) * Polynomial.X).natDegree
            (Polynomial.C (-(2 * aK D ^(2:ℕ) - aK D * bK D - 2 * bK D ^(2:ℕ)))).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ 2 := max_le (le_trans (Polynomial.natDegree_add_le _ _) (max_le hA hB)) hC
  have hY4deg : Y4.natDegree ≤ 0 := by
    rw [hY4def]
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.coeff_C]
    simp [hN.ne']
  have hY2deg : Y2.natDegree ≤ 1 := by
    rw [hY2def]
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : Y4.natDegree ≤ 0 := hY4deg
    have h2 : (Polynomial.X : Polynomial (RatFunc 𝕜)).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega
  -- the coefficient of `X^10`
  have hcoeff := coeff_ten_sparse (aK D) (bK D) (Work.MotV.fAS 𝕜) Y0 Y2 Y4 hY0deg hY2deg hY4deg
  have hthis : ((-(aK D ^(10:ℕ)) + (aK D) ^(5:ℕ) * (bK D) ^(5:ℕ) + (bK D) ^(10:ℕ)) * (Y0.coeff 2) ^(5:ℕ)
      : RatFunc 𝕜) = 0 := by
    rw [← hcoeff, hzero, Polynomial.coeff_zero]
  have hY0c2 : Y0.coeff 2
      = (288 : RatFunc 𝕜) * (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) := by
    rw [hY0def, Polynomial.coeff_C_mul]
    have hq : (Polynomial.C (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * aK D ^(2:ℕ) + 2 * bK D ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * aK D ^(2:ℕ) - aK D * bK D - 2 * bK D ^(2:ℕ)))).coeff 2
        = -(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ)) := by
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    rw [hq]
  -- the final contradiction
  have h288 : (288 : RatFunc 𝕜) ≠ 0 := by
    show ((288 : ℕ) : RatFunc 𝕜) ≠ 0
    have h : ((288 : ℕ) : RatFunc 𝕜) = ((3 : ℕ) : RatFunc 𝕜) := by
      rw [show (288 : ℕ) = 5 * 57 + 3 from by norm_num, Nat.cast_add, Nat.cast_mul,
        CharP.cast_eq_zero (RatFunc 𝕜) 5, zero_mul, zero_add]
    rw [h]
    intro h3
    have hdiv : 5 ∣ 3 := (CharP.cast_eq_zero_iff (RatFunc 𝕜) 5 3).mp h3
    norm_num at hdiv
  have hfrob : (aK D) ^(10:ℕ) - (aK D) ^(5:ℕ) * (bK D) ^(5:ℕ) - (bK D) ^(10:ℕ)
      = (aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ)) ^(5:ℕ) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hA := sub_pow_char_pow (aK D ^(2:ℕ) - aK D * bK D) (bK D ^(2:ℕ)) 1
    have hB := sub_pow_char_pow (aK D ^(2:ℕ)) (aK D * bK D) 1
    simp only [pow_one] at hA hB
    rw [hA, hB]
    refl_ring1
  rw [hY0c2] at hthis
  have hneg : (-(aK D ^(10:ℕ)) + (aK D) ^(5:ℕ) * (bK D) ^(5:ℕ) + (bK D) ^(10:ℕ))
      = -((aK D) ^(10:ℕ) - (aK D) ^(5:ℕ) * (bK D) ^(5:ℕ) - (bK D) ^(10:ℕ)) := by ring
  have hval : (-(aK D ^(10:ℕ)) + (aK D) ^(5:ℕ) * (bK D) ^(5:ℕ) + (bK D) ^(10:ℕ))
      * ((288 : RatFunc 𝕜) * (-(aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ)))) ^(5:ℕ)
      = (288 : RatFunc 𝕜) ^(5:ℕ) * (aK D ^(2:ℕ) - aK D * bK D - bK D ^(2:ℕ)) ^(10:ℕ) := by
    rw [hneg, hfrob]
    refl_ring1
  rw [hval] at hthis
  exact (mul_ne_zero (pow_ne_zero 5 h288) (pow_ne_zero 10 hd)) hthis

end Work.MotAS
