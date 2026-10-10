import Mathlib
import Submission.Work.MotAS.AzDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `azDisc` is not a square (both cases) by a weighted-degree argument

The discriminant `azDisc a b g` of the `X₀`-quadratic form `azQ a b g` is not a square in
`MvPolynomial (Fin 2) K`, for any field `K` of characteristic `5` and `A = azA a b ≠ 0`, `g ≠ 0`.

**Proof.**  Substitute `X₁ ↦ X`, `X₂ ↦ X²` (the weighted-degree substitution with weights
`(1,2)`), obtaining the *univariate* polynomial
`P = aeval ![X, X²] (azDisc a b g) ∈ K[X]` (`azDisc_subs`, an explicit `ring` identity).  Its two
top coefficients are `-320·a²b²·B·A` and `-128·g·A⁴`; since `320 = 64·5 = 0` in characteristic `5`
while `A⁴ ≠ 0`, `g ≠ 0`, `128 ≠ 0`, the top coefficient vanishes and the next one does not, so
`P.natDegree = 7`.  But if `azDisc a b g = s²` then `P = (aeval ![X,X²] s)²`, a square, and the
`natDegree` of a square is even: contradiction.

The same argument covers both `B = 0` and `B ≠ 0`; no case distinction is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotAS.AzDiscSubst

open MvPolynomial

/-- The image of `azDisc` under `X₁ ↦ X`, `X₂ ↦ X²`: a polynomial of degree `8` whose top two
coefficients are `-320·a²b²BA` and `-128·g·A⁴`. -/
theorem azDisc_subs (K : Type*) [Field K] (a b g : K) :
    MvPolynomial.aeval (R := K) ![Polynomial.X, Polynomial.X ^ 2]
        (Work.MotAS.azDisc a b g)
      = Polynomial.C (-320 * a ^ 2 * b ^ 2 * Work.MotAS.azB a b * Work.MotAS.azA a b)
          * Polynomial.X ^ 8
        + Polynomial.C (-128 * g * Work.MotAS.azA a b ^ 4) * Polynomial.X ^ 7
        + Polynomial.C (-64 * Work.MotAS.azA a b ^ 2
            * (3 * a ^ 4 * g - 3 * a ^ 3 * b * g - 2 * a ^ 3 * b - 8 * a ^ 2 * b ^ 2
              - 3 * a * b ^ 3 * g + 2 * a * b ^ 3 - 3 * b ^ 4 * g)) * Polynomial.X ^ 6
        + Polynomial.C (128 * a * b * Work.MotAS.azB a b * Work.MotAS.azA a b
            * (a ^ 2 + 9 * a * b - b ^ 2)) * Polynomial.X ^ 5
        + Polynomial.C (16 * Work.MotAS.azA a b
            * (4 * a ^ 6 * g - a ^ 6 - 12 * a ^ 5 * b * g + 6 * a ^ 5 * b - 24 * a ^ 4 * b ^ 2
              + 20 * a ^ 3 * b ^ 3 * g - 8 * a ^ 3 * b ^ 3 + 24 * a ^ 2 * b ^ 4 - 12 * a * b ^ 5 * g
              + 2 * a * b ^ 5 - 4 * b ^ 6 * g - b ^ 6)) * Polynomial.X ^ 4
        + Polynomial.C (128 * Work.MotAS.azB a b * Work.MotAS.azA a b ^ 2
            * (a ^ 2 * g - a ^ 2 - a * b * g - b ^ 2 * g - b ^ 2)) * Polynomial.X ^ 3
        + Polynomial.C (-32 * Work.MotAS.azA a b
            * (6 * a ^ 6 * g + 8 * a ^ 6 - 8 * a ^ 5 * b * g - 3 * a ^ 5 * b - 10 * a ^ 4 * b ^ 2 * g
              + 17 * a ^ 4 * b ^ 2 + 10 * a ^ 3 * b ^ 3 * g + 10 * a ^ 2 * b ^ 4 * g + 17 * a ^ 2 * b ^ 4
              - 8 * a * b ^ 5 * g + 3 * a * b ^ 5 - 6 * b ^ 6 * g + 8 * b ^ 6)) * Polynomial.X ^ 2
        + Polynomial.C (16 * Work.MotAS.azA a b
            * (4 * a ^ 6 * g ^ 2 - 12 * a ^ 5 * b * g ^ 2 + 4 * a ^ 5 * b - a ^ 4 * b ^ 2
              + 20 * a ^ 3 * b ^ 3 * g ^ 2 - a ^ 2 * b ^ 4 - 12 * a * b ^ 5 * g ^ 2 - 4 * a * b ^ 5
              - 4 * b ^ 6 * g ^ 2)) := by
  simp only [Work.MotAS.azDisc, Work.MotAS.azC1, Work.MotAS.azC2, Work.MotAS.azC0,
    Work.MotAS.azq0, Work.MotAS.azA, Work.MotAS.azB, Work.MotAS.azD, Work.MotAS.azc,
    Work.MotAS.azE, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat]
  first | refl_ring1 | ring

/-- The coefficient of `C c * X ^ j` in degree `m`. -/
private lemma coeff_C_mul_X_pow {K : Type*} [Semiring K] (c : K) (j m : ℕ) :
    (Polynomial.C c * Polynomial.X ^ j : Polynomial K).coeff m = if m = j then c else 0 := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp

/-- **`azDisc a b g` is not a square** in `MvPolynomial (Fin 2) K` for `K` of characteristic `5`,
`A = azA a b ≠ 0` and `g ≠ 0`.  (The argument does not distinguish the cases `B = 0` and
`B ≠ 0`.) -/
theorem azDisc_not_square (K : Type*) [Field K] [CharP K 5] (a b g : K)
    (hA : Work.MotAS.azA a b ≠ 0) (hg : g ≠ 0) :
    ∀ s : MvPolynomial (Fin 2) K, Work.MotAS.azDisc a b g ≠ s ^ 2 := by
  intro s hs
  have h320 : (320 : K) = 0 := (CharP.cast_eq_zero_iff K 5 320).mpr (by norm_num)
  have h128 : (128 : K) ≠ 0 := by
    intro h
    have hd : (5 : ℕ) ∣ 128 := (CharP.cast_eq_zero_iff K 5 128).mp h
    norm_num at hd
  have hc8 : (-320 * a ^ 2 * b ^ 2 * Work.MotAS.azB a b * Work.MotAS.azA a b : K) = 0 := by
    rw [show (-320 : K) = -(320 : K) from rfl, h320, neg_zero]
    first | refl_ring1 | ring
  have h8z : (Polynomial.C (-320 * a ^ 2 * b ^ 2 * Work.MotAS.azB a b * Work.MotAS.azA a b)
      * Polynomial.X ^ 8 : Polynomial K) = 0 := by
    rw [hc8, Polynomial.C_0, zero_mul]
  set Q : Polynomial K :=
    MvPolynomial.aeval (R := K) ![Polynomial.X, Polynomial.X ^ 2] s with hQ
  set P : Polynomial K :=
    MvPolynomial.aeval (R := K) ![Polynomial.X, Polynomial.X ^ 2] (Work.MotAS.azDisc a b g)
    with hP
  have hPsq : P = Q ^ 2 := by
    rw [hP, hQ, hs, map_pow]
  have hexp := azDisc_subs K a b g
  have hcoeff : P.coeff 7 = -128 * g * Work.MotAS.azA a b ^ 4 := by
    rw [hP, hexp]
    simp only [Polynomial.coeff_add, coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num
  have hnatle : P.natDegree ≤ 7 := by
    rw [hP, hexp, h8z, zero_add]
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => ?_)
    simp only [Polynomial.coeff_add, coeff_C_mul_X_pow, Polynomial.coeff_C]
    rw [if_neg (by omega : ¬ (m = 7)), if_neg (by omega : ¬ (m = 6)),
      if_neg (by omega : ¬ (m = 5)), if_neg (by omega : ¬ (m = 4)),
      if_neg (by omega : ¬ (m = 3)), if_neg (by omega : ¬ (m = 2)),
      if_neg (by omega : ¬ (m = 0))]
    first | refl_ring1 | ring
  have hnat : P.natDegree = 7 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnatle
      (by rw [hcoeff]
          exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h128) hg) (pow_ne_zero 4 hA))
  have hQ0 : Q ≠ 0 := by
    intro h0
    rw [h0] at hPsq
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hPsq
    rw [hPsq, Polynomial.natDegree_zero] at hnat
    exact absurd hnat (by norm_num)
  have hnd : P.natDegree = 2 * Q.natDegree := by
    rw [hPsq, pow_two, Polynomial.natDegree_mul hQ0 hQ0]
    first | refl_ring1 | ring
  omega

end Work.MotAS.AzDiscSubst
