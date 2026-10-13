/-
# `Work.FTS.PhiStar.FlatWAux.PhiAjFlatDecayU` — the `α`-uniform flat decay of `𝒜^j φ`

`Work.FTS.PhiStar.PhiAjFlatDecay` (`Submission/Work/FTS/PhiStar/PhiAjFlatDecay.lean`) proves, for
each *fixed* `α ∈ (0, 1/5]`, the flat decay estimates

`|∂_t^k (phiAj j α) t| ≤ A/(1+t^{k+1})`,  `|∂_t^k (phiAj j α · / ·) t| ≤ A/(1+t^{k+2})`

(`k ≤ 14`, `t > 0`) with `phiAj j α = 𝒜_α^j φ`, `𝒜_α = α z²∂_zz + (5+α) z∂_z`, `φ = VocabO.phiR`,
but the constant `boundA α` it produces *depends on* `α`.  The consumers need the estimates
uniformly in `α ∈ (0, 1/5]`, and for `j ≤ 9` rather than `j ≤ 6`.

## How uniformity is obtained

The proof of `PhiAjFlatDecay` exhibits `phiAj j α` as a rational function with a single pole at
`-1`: `phiAj j α = P_j(α)/(1+z)^{2j+2}` with `P_j(α) = phiAjNum α j` of degree `≤ 2j+1`, and
`phiAj j α / z = (P_j(α).divX)/(1+z)^{2j+2}`; the constants are sums of absolute values of
coefficients of iterated `numStep`-derivatives of these polynomials.  The `α`-dependence enters
only through the recursion

`phiAjNum α (j+1) = C α · X² · Q₂ + C (5+α) · X · (1+X) · Q₁`,   `Q₁ = numStep (2j+2) P_j`,
`Q₂ = numStep (2j+3) Q₁`,

so it suffices to bound the *coefficient `ℓ¹`-norm* `cl1 P = ∑_i |P.coeff i|` of every polynomial
occurring, uniformly in `α`:

* `cl1 (P * X^k) ≤ cl1 P` and `cl1 (derivative P) ≤ deg P · cl1 P`, whence
  `cl1 (numStep n P) ≤ (2 deg P + 2 + n) · cl1 P` and, by induction on `k`,
  `cl1 (numIter n P k) ≤ cit d n k · cl1 P` for `deg P ≤ d` (`cit d n k` recursive);
* `cl1 (phiAjNum α j) ≤ nb j` with the `α`-free recursion `nb (j+1) = fac j · nb j` coming from
  `|α| ≤ 1/5`, `|5+α| ≤ 6` (`fac j = (1/5)(6j+6)(6j+7) + 12(6j+6)`).

The `j`- and `k`-dependence is then packaged as the single constant
`AU = 1 + ∑_{j<10} ∑_{k<15} (B1 j k + B2 j k)`, `B1 j k = 2·cit (2j+1) (2j+2) k · nb j`,
`B2 j k = 2·cit (2j) (2j+2) k · nb j`, which is the `A` of the statement; the final assembly is
verbatim the one of `PhiAjFlatDecay`, with `boundA α` replaced by `AU`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.PhiAjFlatDecay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology
open Set Polynomial

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Unif

/-! ## 1. The coefficient norm `cl1` and its calculus -/

/-- `cl1 P` is the sum of the absolute values of the coefficients of the real polynomial `P`. -/
noncomputable def cl1 (P : Polynomial ℝ) : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|

lemma cl1_nonneg (P : Polynomial ℝ) : 0 ≤ cl1 P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Summing the absolute values of the coefficients over any range containing the degree gives
`cl1`. -/
lemma sum_range_coeff_eq_cl1 {P : Polynomial ℝ} {D : ℕ} (h : P.natDegree ≤ D) :
    ∑ i ∈ Finset.range (D + 1), |P.coeff i| = cl1 P := by
  rw [cl1]
  refine (Finset.sum_subset ?_ ?_).symm
  · rw [Finset.range_subset_range]; omega
  · intro i hi hni
    have hi' : P.natDegree < i := by
      simp only [Finset.mem_range] at hi hni
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi', abs_zero]

lemma cl1_le_sum_range {P : Polynomial ℝ} {D : ℕ} (h : P.natDegree ≤ D) :
    cl1 P ≤ ∑ i ∈ Finset.range (D + 1), |P.coeff i| :=
  (sum_range_coeff_eq_cl1 h).ge

lemma cl1_add_le (P Q : Polynomial ℝ) : cl1 (P + Q) ≤ cl1 P + cl1 Q := by
  have hPQ : (P + Q).natDegree ≤ max P.natDegree Q.natDegree := Polynomial.natDegree_add_le P Q
  calc cl1 (P + Q)
      = ∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1), |(P + Q).coeff i| :=
        (sum_range_coeff_eq_cl1 hPQ).symm
    _ ≤ ∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1),
          (|P.coeff i| + |Q.coeff i|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Polynomial.coeff_add]
        exact abs_add_le _ _
    _ = (∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1), |P.coeff i|)
        + ∑ i ∈ Finset.range (max P.natDegree Q.natDegree + 1), |Q.coeff i| :=
        Finset.sum_add_distrib
    _ = cl1 P + cl1 Q := by
        rw [sum_range_coeff_eq_cl1 (le_max_left P.natDegree Q.natDegree),
          sum_range_coeff_eq_cl1 (le_max_right P.natDegree Q.natDegree)]

lemma cl1_neg (P : Polynomial ℝ) : cl1 (-P) = cl1 P := by
  rw [cl1, cl1, Polynomial.natDegree_neg]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_neg, abs_neg]

lemma cl1_sub_le (P Q : Polynomial ℝ) : cl1 (P - Q) ≤ cl1 P + cl1 Q := by
  calc cl1 (P - Q) = cl1 (P + -Q) := by rw [sub_eq_add_neg]
    _ ≤ cl1 P + cl1 (-Q) := cl1_add_le P (-Q)
    _ = cl1 P + cl1 Q := by rw [cl1_neg]

lemma cl1_C_mul (a : ℝ) (P : Polynomial ℝ) : cl1 (C a * P) = |a| * cl1 P := by
  have h : (C a * P).natDegree ≤ P.natDegree := Polynomial.natDegree_C_mul_le a P
  calc cl1 (C a * P) = ∑ i ∈ Finset.range (P.natDegree + 1), |(C a * P).coeff i| :=
        (sum_range_coeff_eq_cl1 h).symm
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |a| * |P.coeff i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_C_mul, abs_mul]
    _ = |a| * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by rw [Finset.mul_sum]
    _ = |a| * cl1 P := by rw [cl1]

/-- Multiplying by a monomial does not increase the coefficient norm. -/
lemma cl1_mul_X_pow_le (P : Polynomial ℝ) (k : ℕ) : cl1 (P * X ^ k) ≤ cl1 P := by
  have hdeg : (P * X ^ k).natDegree ≤ P.natDegree + k := by
    have h := Polynomial.natDegree_mul_le (p := P) (q := X ^ k)
    have hX := Polynomial.natDegree_X_pow_le (R := ℝ) k
    omega
  have hmain : cl1 (P * X ^ k) = cl1 P := by
    calc cl1 (P * X ^ k)
        = ∑ i ∈ Finset.range (P.natDegree + k + 1), |(P * X ^ k).coeff i| :=
          (sum_range_coeff_eq_cl1 hdeg).symm
      _ = ∑ i ∈ Finset.range k, |(P * X ^ k).coeff i|
          + ∑ i ∈ Finset.range (P.natDegree + 1), |(P * X ^ k).coeff (k + i)| := by
          rw [show P.natDegree + k + 1 = k + (P.natDegree + 1) from by omega,
            Finset.sum_range_add]
      _ = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by
          have h0 : ∑ i ∈ Finset.range k, |(P * X ^ k).coeff i| = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            rw [Polynomial.coeff_mul_X_pow']
            have hik : ¬ (k ≤ i) := by simpa using Finset.mem_range.mp hi
            rw [if_neg hik, abs_zero]
          have h1 : ∑ i ∈ Finset.range (P.natDegree + 1), |(P * X ^ k).coeff (k + i)|
              = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show k + i = i + k from by omega, Polynomial.coeff_mul_X_pow]
          rw [h0, zero_add, h1]
      _ = cl1 P := sum_range_coeff_eq_cl1 (le_refl P.natDegree)
  exact hmain.le

/-- `X^k` on the left does not increase the coefficient norm. -/
lemma cl1_X_pow_mul_le (P : Polynomial ℝ) (k : ℕ) : cl1 (X ^ k * P) ≤ cl1 P := by
  rw [mul_comm]
  exact cl1_mul_X_pow_le P k

/-- The `X²`-multiple of a polynomial has no larger coefficient norm. -/
lemma cl1_X_sq_mul_le (P : Polynomial ℝ) : cl1 (X ^ 2 * P) ≤ cl1 P :=
  cl1_X_pow_mul_le P 2

/-- The `X(1+X)`-multiple has coefficient norm at most twice that of the polynomial. -/
lemma cl1_mul_one_add_X_le (P : Polynomial ℝ) : cl1 (P * (1 + X)) ≤ 2 * cl1 P := by
  have h : P * (1 + X) = P + P * X := by rw [mul_add, mul_one]
  calc cl1 (P * (1 + X)) = cl1 (P + P * X) := by rw [h]
    _ ≤ cl1 P + cl1 (P * X) := cl1_add_le P (P * X)
    _ ≤ cl1 P + cl1 P :=
        add_le_add le_rfl (by simpa [pow_one] using cl1_mul_X_pow_le P 1)
    _ = 2 * cl1 P := by ring

lemma cl1_X_mul_one_add_X_le (P : Polynomial ℝ) : cl1 (X * ((1 + X) * P)) ≤ 2 * cl1 P := by
  calc cl1 (X * ((1 + X) * P)) = cl1 ((X ^ 1) * ((1 + X) * P)) := by rw [pow_one]
    _ ≤ cl1 ((1 + X) * P) := cl1_X_pow_mul_le ((1 + X) * P) 1
    _ = cl1 (P * (1 + X)) := by rw [mul_comm]
    _ ≤ 2 * cl1 P := cl1_mul_one_add_X_le P

/-- The first `phiAjNum` summand stays bounded by `|a| · cl1` of the numerator. -/
lemma cl1_C_X_sq_mul_le (a : ℝ) (Q : Polynomial ℝ) :
    cl1 (C a * X ^ 2 * Q) ≤ |a| * cl1 Q := by
  have h1 : C a * X ^ 2 * Q = C a * (X ^ 2 * Q) := by rw [mul_assoc]
  rw [h1, cl1_C_mul]
  exact mul_le_mul_of_nonneg_left (cl1_X_sq_mul_le Q) (abs_nonneg a)

/-- The second `phiAjNum` summand stays bounded by `2|a| · cl1` of the numerator. -/
lemma cl1_C_X_one_add_X_mul_le (a : ℝ) (Q : Polynomial ℝ) :
    cl1 (C a * X * (1 + X) * Q) ≤ 2 * |a| * cl1 Q := by
  have h1 : C a * X * (1 + X) * Q = C a * (X * ((1 + X) * Q)) := by
    rw [mul_assoc, mul_assoc]
  rw [h1, cl1_C_mul]
  calc |a| * cl1 (X * ((1 + X) * Q)) ≤ |a| * (2 * cl1 Q) :=
        mul_le_mul_of_nonneg_left (cl1_X_mul_one_add_X_le Q) (abs_nonneg a)
    _ = 2 * |a| * cl1 Q := by ring

/-- Differentiating multiplies the coefficient norm by at most the degree. -/
lemma cl1_derivative_le (P : Polynomial ℝ) :
    cl1 (derivative P) ≤ (P.natDegree : ℝ) * cl1 P := by
  have hdeg : (derivative P).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le _ _)
  calc cl1 (derivative P)
      = ∑ i ∈ Finset.range (P.natDegree + 1), |(derivative P).coeff i| :=
        (sum_range_coeff_eq_cl1 hdeg).symm
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff (i + 1)| * ((i : ℝ) + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_derivative, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
    _ = ∑ i ∈ Finset.range P.natDegree, |P.coeff (i + 1)| * ((i : ℝ) + 1) := by
        rw [Finset.sum_range_succ, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _),
          abs_zero, zero_mul, add_zero]
    _ ≤ ∑ i ∈ Finset.range P.natDegree, |P.coeff (i + 1)| * (P.natDegree : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i + 1 ≤ P.natDegree := by simpa using Finset.mem_range.mp hi
        have h1 : ((i : ℝ) + 1) ≤ (P.natDegree : ℝ) := by exact_mod_cast hi'
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (∑ i ∈ Finset.range P.natDegree, |P.coeff (i + 1)|) * (P.natDegree : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|) * (P.natDegree : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Finset.sum_range_succ' (f := fun i => |P.coeff i|) (n := P.natDegree)]
        linarith [abs_nonneg (P.coeff 0)]
    _ = cl1 P * (P.natDegree : ℝ) := by rw [sum_range_coeff_eq_cl1 (le_refl P.natDegree)]
    _ = (P.natDegree : ℝ) * cl1 P := by ring

/-- The one-step estimate for the derivative numerator of a rational function with a single pole
at `-1`. -/
lemma cl1_numStep_le (n d : ℕ) {P : Polynomial ℝ} (hP : P.natDegree ≤ d) :
    cl1 (numStep n P) ≤ ((2 * d + 2 + n : ℕ) : ℝ) * cl1 P := by
  have hder : cl1 (derivative P) ≤ (d : ℝ) * cl1 P :=
    (cl1_derivative_le P).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hP) (cl1_nonneg P))
  have hA : cl1 (derivative P * (1 + X)) ≤ 2 * ((d : ℝ) * cl1 P) :=
    (cl1_mul_one_add_X_le (derivative P)).trans
      (mul_le_mul_of_nonneg_left hder (by norm_num))
  have hB : cl1 (C (n : ℝ) * P) ≤ (n : ℝ) * cl1 P := by
    rw [cl1_C_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hsum : 2 * ((d : ℝ) * cl1 P) + (n : ℝ) * cl1 P
      ≤ ((2 * d + 2 + n : ℕ) : ℝ) * cl1 P := by
    push_cast
    nlinarith [cl1_nonneg P]
  calc cl1 (numStep n P) = cl1 (derivative P * (1 + X) - C (n : ℝ) * P) := by rw [numStep]
    _ ≤ cl1 (derivative P * (1 + X)) + cl1 (C (n : ℝ) * P) := cl1_sub_le _ _
    _ ≤ 2 * ((d : ℝ) * cl1 P) + (n : ℝ) * cl1 P := add_le_add hA hB
    _ ≤ ((2 * d + 2 + n : ℕ) : ℝ) * cl1 P := hsum

/-- The `k`-fold recursion constant for `cl1 (numIter n P k)` under the degree bound `deg P ≤ d`. -/
def cit (d n : ℕ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => ((2 * d + 2 + n + k : ℕ) : ℝ) * cit d n k

lemma cit_nonneg (d n k : ℕ) : 0 ≤ cit d n k := by
  induction k with
  | zero => simp [cit]
  | succ k ih =>
      have h : cit d n (k + 1) = ((2 * d + 2 + n + k : ℕ) : ℝ) * cit d n k := rfl
      rw [h]
      positivity

lemma cl1_numIter_le (n d k : ℕ) {P : Polynomial ℝ} (hP : P.natDegree ≤ d) :
    cl1 (numIter n P k) ≤ cit d n k * cl1 P := by
  induction k with
  | zero => simp [numIter, cit]
  | succ k ih =>
      have hdeg : (numIter n P k).natDegree ≤ d := (numIter_natDegree_le n P k).trans hP
      have hstep : cl1 (numStep (n + k) (numIter n P k))
          ≤ ((2 * d + 2 + (n + k) : ℕ) : ℝ) * cl1 (numIter n P k) :=
        cl1_numStep_le (n + k) d hdeg
      calc cl1 (numIter n P (k + 1)) = cl1 (numStep (n + k) (numIter n P k)) := by
            rw [numIter_succ]
        _ ≤ ((2 * d + 2 + (n + k) : ℕ) : ℝ) * cl1 (numIter n P k) := hstep
        _ ≤ ((2 * d + 2 + (n + k) : ℕ) : ℝ) * (cit d n k * cl1 P) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = cit d n (k + 1) * cl1 P := by
            rw [show cit d n (k + 1) = ((2 * d + 2 + n + k : ℕ) : ℝ) * cit d n k from rfl,
              show 2 * d + 2 + (n + k) = 2 * d + 2 + n + k from by omega]
            ring

lemma cl1_divX_le (P : Polynomial ℝ) : cl1 (P.divX) ≤ cl1 P := by
  have hdeg : P.divX.natDegree ≤ P.natDegree := Polynomial.natDegree_divX_le
  calc cl1 P.divX = ∑ i ∈ Finset.range (P.natDegree + 1), |P.divX.coeff i| :=
        (sum_range_coeff_eq_cl1 hdeg).symm
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff (i + 1)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_divX]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 2), |P.coeff i| := by
        rw [show P.natDegree + 2 = (P.natDegree + 1) + 1 from by omega,
          Finset.sum_range_succ' (f := fun i => |P.coeff i|) (n := P.natDegree + 1)]
        linarith [abs_nonneg (P.coeff 0)]
    _ = cl1 P := by
        rw [show P.natDegree + 2 = (P.natDegree + 1) + 1 from by omega,
          Finset.sum_range_succ, sum_range_coeff_eq_cl1 (le_refl P.natDegree),
          Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), abs_zero, add_zero]

lemma cl1_X : cl1 (Polynomial.X : Polynomial ℝ) = 1 := by
  rw [cl1, Polynomial.natDegree_X, Finset.sum_range_succ, Finset.sum_range_one,
    Polynomial.coeff_X_zero, Polynomial.coeff_X_one]
  norm_num

/-! ## 2. The `α`-free recursive bounds -/

/-- The `α`-free factor by which `cl1` grows in one `phiAjNum` step
(`|α| ≤ 1/5`, `|5+α| ≤ 6`). -/
noncomputable def fac (j : ℕ) : ℝ :=
  (1 / 5 : ℝ) * ((6 * j + 6 : ℕ) : ℝ) * ((6 * j + 7 : ℕ) : ℝ)
    + 12 * ((6 * j + 6 : ℕ) : ℝ)

lemma fac_nonneg (j : ℕ) : 0 ≤ fac j := by
  rw [fac]; positivity

/-- An `α`-free bound on `cl1 (phiAjNum α j)`, uniform in `α ∈ (0, 1/5]`. -/
noncomputable def nb : ℕ → ℝ
  | 0 => 2
  | (j + 1) => fac j * nb j

lemma nb_nonneg (j : ℕ) : 0 ≤ nb j := by
  induction j with
  | zero => norm_num [nb]
  | succ j ih =>
      have h : nb (j + 1) = fac j * nb j := rfl
      rw [h]
      exact mul_nonneg (fac_nonneg j) ih

/-- One `numStep` of the `phiAjNum` recursion. -/
lemma cl1_numStep_one_le (α : ℝ) (j : ℕ) :
    cl1 (numStep (2 * j + 2) (phiAjNum α j))
      ≤ ((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j) := by
  have hP : (phiAjNum α j).natDegree ≤ 2 * j + 1 := phiAjNum_natDegree_le α j
  have h := cl1_numStep_le (2 * j + 2) (2 * j + 1) hP
  rwa [show (2 * (2 * j + 1) + 2 + (2 * j + 2) : ℕ) = 6 * j + 6 from by omega] at h

/-- Two `numStep`s of the `phiAjNum` recursion. -/
lemma cl1_numStep_pair_le (α : ℝ) (j : ℕ) :
    cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ ((6 * j + 7 : ℕ) : ℝ) * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j)) := by
  have hP : (phiAjNum α j).natDegree ≤ 2 * j + 1 := phiAjNum_natDegree_le α j
  have hQ1 : (numStep (2 * j + 2) (phiAjNum α j)).natDegree ≤ 2 * j + 1 :=
    numStep_natDegree_le (by omega) hP
  have h2 : cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ ((6 * j + 7 : ℕ) : ℝ) * cl1 (numStep (2 * j + 2) (phiAjNum α j)) := by
    have h := cl1_numStep_le (2 * j + 3) (2 * j + 1) hQ1
    rwa [show (2 * (2 * j + 1) + 2 + (2 * j + 3) : ℕ) = 6 * j + 7 from by omega] at h
  exact h2.trans (mul_le_mul_of_nonneg_left (cl1_numStep_one_le α j) (Nat.cast_nonneg _))

/-- The algebraic splitting of one `phiAjNum` step. -/
lemma cl1_phiAjNum_split (α : ℝ) (j : ℕ) :
    cl1 (phiAjNum α (j + 1))
      ≤ |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
        + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j))) := by
  rw [phiAjNum]
  refine (cl1_add_le _ _).trans (add_le_add ?_ ?_)
  · exact cl1_C_X_sq_mul_le α (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
  · refine (cl1_C_X_one_add_X_mul_le (5 + α)
      (numStep (2 * j + 2) (phiAjNum α j))).trans (le_of_eq ?_)
    ring

/-- The numeric step: `|α| ≤ 1/5`, `|5 + α| ≤ 6` bound the two coefficients. -/
lemma cl1_pair_step (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j : ℕ) :
    |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ fac j * cl1 (phiAjNum α j) := by
  have hαabs : |α| ≤ 1 / 5 := by rw [abs_of_pos hα]; exact hα5
  have h5abs : |5 + α| ≤ 6 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 5 + α)]
    linarith
  have hpair := cl1_numStep_pair_le α j
  have hone := cl1_numStep_one_le α j
  have h4 : |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ (1 / 5) * (((6 * j + 7 : ℕ) : ℝ)
          * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j))) :=
    mul_le_mul hαabs hpair (cl1_nonneg _) (by norm_num)
  have h5 : |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ 6 * (2 * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j))) := by
    refine mul_le_mul h5abs ?_ ?_ (by norm_num)
    · exact mul_le_mul_of_nonneg_left hone (by norm_num)
    · exact mul_nonneg (by norm_num) (cl1_nonneg _)
  calc |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
        + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j)))
      ≤ (1 / 5) * (((6 * j + 7 : ℕ) : ℝ)
            * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j)))
        + 6 * (2 * (((6 * j + 6 : ℕ) : ℝ) * cl1 (phiAjNum α j))) := add_le_add h4 h5
    _ = fac j * cl1 (phiAjNum α j) := by rw [fac]; ring

/-- **The uniform coefficient bound.**  For `α ∈ (0, 1/5]` the numerator polynomial of
`phiAj j α` has coefficient norm at most `nb j`, independently of `α`. -/
lemma cl1_phiAjNum_le (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j : ℕ) :
    cl1 (phiAjNum α j) ≤ nb j := by
  induction j with
  | zero =>
      have h : phiAjNum α 0 = C 2 * X := rfl
      rw [h, cl1_C_mul, cl1_X, mul_one]
      norm_num [nb]
  | succ j ih =>
      calc cl1 (phiAjNum α (j + 1))
          ≤ |α| * cl1 (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
            + |5 + α| * (2 * cl1 (numStep (2 * j + 2) (phiAjNum α j))) :=
            cl1_phiAjNum_split α j
        _ ≤ fac j * cl1 (phiAjNum α j) := cl1_pair_step α hα hα5 j
        _ ≤ fac j * nb j := mul_le_mul_of_nonneg_left ih (fac_nonneg j)
        _ = nb (j + 1) := rfl

/-! ## 3. The uniform slot bounds and the constant `AU` -/

/-- The uniform bound on `2 · slotC1 α j k`. -/
noncomputable def B1 (j k : ℕ) : ℝ := 2 * (cit (2 * j + 1) (2 * j + 2) k * nb j)

/-- The uniform bound on `2 · slotC2 α j k`. -/
noncomputable def B2 (j k : ℕ) : ℝ := 2 * (cit (2 * j) (2 * j + 2) k * nb j)

lemma B1_nonneg (j k : ℕ) : 0 ≤ B1 j k := by
  rw [B1]
  exact mul_nonneg (by norm_num) (mul_nonneg (cit_nonneg _ _ _) (nb_nonneg j))

lemma B2_nonneg (j k : ℕ) : 0 ≤ B2 j k := by
  rw [B2]
  exact mul_nonneg (by norm_num) (mul_nonneg (cit_nonneg _ _ _) (nb_nonneg j))

/-- The constant of the statement. -/
noncomputable def AU : ℝ :=
  1 + ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 15, (B1 j k + B2 j k)

lemma AU_pos : 0 < AU := by
  rw [AU]
  have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range 10, ∑ k ∈ Finset.range 15, (B1 j k + B2 j k) :=
    Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => add_nonneg (B1_nonneg j k) (B2_nonneg j k)
  linarith

lemma B1_le_AU {j k : ℕ} (hj : j ≤ 9) (hk : k ≤ 14) : B1 j k ≤ AU := by
  have hj10 : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hk15 : k ∈ Finset.range 15 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range 10,
      0 ≤ ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') := fun j' _ =>
    Finset.sum_nonneg fun k' _ => add_nonneg (B1_nonneg j' k') (B2_nonneg j' k')
  have h1 : B1 j k ≤ ∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k') :=
    (le_add_of_nonneg_right (B2_nonneg j k)).trans
      (Finset.single_le_sum (fun k' _ => add_nonneg (B1_nonneg j k') (B2_nonneg j k')) hk15)
  have h2 : (∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k'))
      ≤ ∑ j' ∈ Finset.range 10, ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') :=
    Finset.single_le_sum hinner hj10
  rw [AU]
  linarith

lemma B2_le_AU {j k : ℕ} (hj : j ≤ 9) (hk : k ≤ 14) : B2 j k ≤ AU := by
  have hj10 : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hk15 : k ∈ Finset.range 15 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range 10,
      0 ≤ ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') := fun j' _ =>
    Finset.sum_nonneg fun k' _ => add_nonneg (B1_nonneg j' k') (B2_nonneg j' k')
  have h1 : B2 j k ≤ ∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k') :=
    (le_add_of_nonneg_left (B1_nonneg j k)).trans
      (Finset.single_le_sum (fun k' _ => add_nonneg (B1_nonneg j k') (B2_nonneg j k')) hk15)
  have h2 : (∑ k' ∈ Finset.range 15, (B1 j k' + B2 j k'))
      ≤ ∑ j' ∈ Finset.range 10, ∑ k' ∈ Finset.range 15, (B1 j' k' + B2 j' k') :=
    Finset.single_le_sum hinner hj10
  rw [AU]
  linarith

lemma slotC1_le_B1 (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j k : ℕ) :
    2 * slotC1 α j k ≤ B1 j k := by
  have hP : (phiAjNum α j).natDegree ≤ 2 * j + 1 := phiAjNum_natDegree_le α j
  have hdeg : (numIter (2 * j + 2) (phiAjNum α j) k).natDegree ≤ 2 * j + 1 :=
    (numIter_natDegree_le (2 * j + 2) (phiAjNum α j) k).trans hP
  have hslot : slotC1 α j k = cl1 (numIter (2 * j + 2) (phiAjNum α j) k) := by
    have hcongr : Finset.range (2 * j + 2) = Finset.range ((2 * j + 1) + 1) := by
      rw [show 2 * j + 2 = (2 * j + 1) + 1 from by omega]
    rw [slotC1]
    exact (Finset.sum_congr hcongr (fun _ _ => rfl)).trans (sum_range_coeff_eq_cl1 hdeg)
  rw [hslot, B1]
  have hiter := cl1_numIter_le (2 * j + 2) (2 * j + 1) k hP
  have hnb := cl1_phiAjNum_le α hα hα5 j
  calc 2 * cl1 (numIter (2 * j + 2) (phiAjNum α j) k)
      ≤ 2 * (cit (2 * j + 1) (2 * j + 2) k * cl1 (phiAjNum α j)) :=
        mul_le_mul_of_nonneg_left hiter (by norm_num)
    _ ≤ 2 * (cit (2 * j + 1) (2 * j + 2) k * nb j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnb (cit_nonneg _ _ _)) (by norm_num)

lemma slotC2_le_B2 (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (j k : ℕ) :
    2 * slotC2 α j k ≤ B2 j k := by
  have hP : (phiAjNumDiv α j).natDegree ≤ 2 * j := phiAjNumDiv_natDegree_le α j
  have hdeg : (numIter (2 * j + 2) (phiAjNumDiv α j) k).natDegree ≤ 2 * j :=
    (numIter_natDegree_le (2 * j + 2) (phiAjNumDiv α j) k).trans hP
  have hslot : slotC2 α j k = cl1 (numIter (2 * j + 2) (phiAjNumDiv α j) k) := by
    rw [slotC2]
    exact sum_range_coeff_eq_cl1 hdeg
  have hdiv : cl1 (phiAjNumDiv α j) ≤ nb j := by
    have h : phiAjNumDiv α j = (phiAjNum α j).divX := rfl
    rw [h]
    exact (cl1_divX_le (phiAjNum α j)).trans (cl1_phiAjNum_le α hα hα5 j)
  rw [hslot, B2]
  have hiter := cl1_numIter_le (2 * j + 2) (2 * j) k hP
  calc 2 * cl1 (numIter (2 * j + 2) (phiAjNumDiv α j) k)
      ≤ 2 * (cit (2 * j) (2 * j + 2) k * cl1 (phiAjNumDiv α j)) :=
        mul_le_mul_of_nonneg_left hiter (by norm_num)
    _ ≤ 2 * (cit (2 * j) (2 * j + 2) k * nb j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv (cit_nonneg _ _ _)) (by norm_num)

end Unif

open Unif

theorem PhiAjFlatDecayU : ∃ A : ℝ, 0 < A ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ j : ℕ, j ≤ 9 →
    (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (Work.FTS.PhiStar.phiAj j α) t| ≤ A / (1 + t ^ (k + 1))) ∧
    (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (fun t => Work.FTS.PhiStar.phiAj j α t / t) t| ≤ A / (1 + t ^ (k + 2))) := by
  refine ⟨AU, AU_pos, fun α hα hα5 j hj => ⟨?_, ?_⟩⟩
  · intro k hk t ht
    have hC1 : 2 * slotC1 α j k ≤ AU := (slotC1_le_B1 α hα hα5 j k).trans (B1_le_AU hj hk)
    have hC1nn : 0 ≤ slotC1 α j k := slotC1_nonneg α j k
    have ht1 : (-1 : ℝ) < t := by linarith
    have heq : iteratedDeriv k (Work.FTS.PhiStar.phiAj j α) t
        = iteratedDeriv k (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) t :=
      iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi (phiAj_eqOn_num α j) k ht1
    have hb : |iteratedDeriv k (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) t|
        ≤ slotC1 α j k / (1 + t) ^ (k + 1) := by
      have h := rat_iteratedDeriv_bound (phiAjNum α j) (2 * j + 1) 1 k (by norm_num)
        (phiAjNum_natDegree_le α j) t ht
      rw [show (2 * j + 1 + 1 : ℕ) = 2 * j + 2 from by omega,
        show (1 + k : ℕ) = k + 1 from by omega] at h
      exact h
    rw [heq]
    exact bound_of_le (k + 1) hC1nn hC1 ht hb
  · intro k hk t ht
    have hC2 : 2 * slotC2 α j k ≤ AU := (slotC2_le_B2 α hα hα5 j k).trans (B2_le_AU hj hk)
    have hC2nn : 0 ≤ slotC2 α j k := slotC2_nonneg α j k
    have heq : iteratedDeriv k (fun t : ℝ => Work.FTS.PhiStar.phiAj j α t / t) t
        = iteratedDeriv k (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) t :=
      iteratedDeriv_congr_of_eqOn_isOpen isOpen_Ioi (phiAj_div_eqOn_num α j) k ht
    have hb : |iteratedDeriv k (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) t|
        ≤ slotC2 α j k / (1 + t) ^ (k + 2) := by
      have h := rat_iteratedDeriv_bound (phiAjNumDiv α j) (2 * j) 2 k (by norm_num)
        (phiAjNumDiv_natDegree_le α j) t ht
      rw [show (2 + k : ℕ) = k + 2 from by omega] at h
      exact h
    rw [heq]
    exact bound_of_le (k + 2) hC2nn hC2 ht hb

end Work.FTS.PhiStar.FlatWAux
