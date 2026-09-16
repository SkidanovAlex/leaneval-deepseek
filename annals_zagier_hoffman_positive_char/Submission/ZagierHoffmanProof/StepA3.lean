import Mathlib.FieldTheory.Finite.Basic
import Submission.ZagierHoffmanProof.StepA2

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Step A: degree bounds

Crude (but sufficient) natural-degree bounds for the level-one ingredients:
`[1] = X^q - X` has degree `q`, `Q_c` has degree `q - 1`, and `A_n` has degree at most
`n (q - 1)`.  From these, the degree of the `(P1)`-difference `Q` is bounded by
`(a + b) q - 1 < q (a + b) = deg [1]^{a+b}`, which (with translation invariance and the
pairwise-coprime factor argument) forces `Q = 0`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `[1] = X^q - X` has natural degree `q`. -/
lemma carlitzOne_natDegree :
    (carlitzOne F).natDegree = Nat.card F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [carlitzOne]
  have hq : 1 < Nat.card F := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  have h1 : (X : F[X]).degree < (X ^ Nat.card F : F[X]).degree := by
    rw [Polynomial.degree_X, Polynomial.degree_X_pow]
    exact_mod_cast hq
  have hd := Polynomial.degree_sub_eq_left_of_degree_lt h1
  rw [natDegree_eq_of_degree_eq hd]
  exact Polynomial.natDegree_X_pow (R := F) (Nat.card F)

/-- `Q_c` has natural degree `q - 1` (from `[1] = (X + C c) * Q_c`). -/
lemma qPoly_natDegree (c : F) :
    (qPoly F c).natDegree = Nat.card F - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq := carlitzOne_eq_mul_qPoly F c
  have hdeg := congrArg Polynomial.natDegree hq
  -- hdeg : natDegree (carlitzOne F) = natDegree ((X + C c) * qPoly F c)
  rw [carlitzOne_natDegree F] at hdeg
  have hX : X + C c ≠ (0 : F[X]) := Polynomial.X_add_C_ne_zero (R := F) c
  have hQ : qPoly F c ≠ (0 : F[X]) := by
    intro hz
    have hzero : carlitzOne F = 0 := by
      rw [hq, hz]
      simp
    have hdeg0 : (carlitzOne F).natDegree = 0 := by rw [hzero]; simp
    rw [carlitzOne_natDegree F] at hdeg0
    have h1 : 1 < Nat.card F := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.one_lt_card
    omega
  have hmul := Polynomial.natDegree_mul hX hQ
  -- hmul : natDegree ((X + C c) * qPoly F c) = natDegree (X + C c) + natDegree (qPoly F c)
  rw [hmul] at hdeg
  rw [Polynomial.natDegree_X_add_C] at hdeg
  omega

/-- `A_n` has natural degree at most `n (q - 1)`. -/
lemma A_natDegree_le (n : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    (A F n).natDegree ≤ n * (Nat.card F - 1) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [show A F n = ∑ c ∈ (Finset.univ : Finset F), (qPoly F c) ^ n by rfl]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c hc
  calc
    ((qPoly F c) ^ n).natDegree = n * (qPoly F c).natDegree := Polynomial.natDegree_pow _ _
    _ = n * (Nat.card F - 1) := by rw [qPoly_natDegree F c]
    _ ≤ n * (Nat.card F - 1) := le_rfl

/-- Linear factors with distinct constants are coprime. -/
lemma linFactor_coprime {c c' : F} (h : c ≠ c') :
    IsCoprime (X + C c : F[X]) (X + C c') := by
  let a : F[X] := C ((c - c')⁻¹)
  refine ⟨a, -a, ?_⟩
  have hdiff : c - c' ≠ 0 := sub_ne_zero.mpr h
  have hlinv : (c - c')⁻¹ * (c - c') = 1 := inv_mul_cancel₀ hdiff
  calc
    a * (X + C c) + (-a) * (X + C c') = a * (C c - C c') := by ring
    _ = 1 := by
          rw [show C c - C c' = C (c - c') by rw [Polynomial.C_sub]]
          rw [show a = C ((c - c')⁻¹) by rfl]
          rw [← Polynomial.C_mul]
          rw [hlinv]
          simp

/-- If a translation-invariant polynomial is divisible by `X ^ n`, it is divisible by
`(X + C c) ^ n` for every shift `c`. -/
lemma shift_dvd_of_dvd_comp (Q : F[X]) (n : ℕ) (c : F)
    (hcomp : Q.comp (X + C c) = Q) (hdvd : X ^ n ∣ Q) :
    (X + C c) ^ n ∣ Q := by
  rcases hdvd with ⟨R, hR⟩
  refine ⟨R.comp (X + C c), ?_⟩
  calc
    Q = Q.comp (X + C c) := hcomp.symm
    _ = (X ^ n * R).comp (X + C c) := by rw [hR]
    _ = (X + C c) ^ n * R.comp (X + C c) := by
          rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]

/-- Divisibility by every shifted factor implies divisibility by `[1] ^ n`:
if `(X + C c) ^ n ∣ Q` for all `c : F`, then `(carlitzOne F) ^ n ∣ Q`. -/
lemma carlitzOne_pow_dvd_of_shift_dvd (Q : F[X]) (n : ℕ)
    (h : ∀ c : F, (X + C c) ^ n ∣ Q) :
    letI : Fintype F := Fintype.ofFinite F
    (carlitzOne F) ^ n ∣ Q := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hpd : (∏ c : F, (X + C c) ^ n) ∣ Q := by
    change (∏ c ∈ (Finset.univ : Finset F), (X + C c) ^ n) ∣ Q
    refine Finset.prod_dvd_of_coprime (t := (Finset.univ : Finset F))
      (s := fun c : F => (X + C c) ^ n) ?_ ?_
    · intro c hc c' hc' hcc'
      exact ((linFactor_coprime F hcc').pow_left : IsCoprime ((X + C c) ^ n) (X + C c')).pow_right
    · intro c hc
      exact h c
  have hA : (∏ c : F, (X + C c) ^ n) = (carlitzOne F) ^ n := by
    calc
      (∏ c : F, (X + C c) ^ n)
          = (∏ c ∈ (Finset.univ : Finset F), (X + C c)) ^ n := by
              change (∏ c ∈ (Finset.univ : Finset F), (X + C c) ^ n)
                = (∏ c ∈ (Finset.univ : Finset F), (X + C c)) ^ n
              rw [Finset.prod_pow]
      _ = (carlitzOne F) ^ n := by
              rw [carlitzOne_eq_prod_X_add_C F]
  rwa [hA] at hpd
