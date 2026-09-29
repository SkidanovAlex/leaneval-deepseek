import Mathlib
import Submission.Work.A14.defs
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def

/-!
# `Work.A14D` — data for `adjointZ_no_solution`

The target

`dRat (dRat (P·β)) − dRat (P'·β) + R·β = Σ_{i<3} c_i · y^{−i}·y'   (y = x²/(x−1))`

where `P = x − 10x² + 9x³ = x(1−x)(1−9x)`, `P' = 1 − 20x + 27x²`, `R = −3 + 9x` is
the *self-adjoint* form `P·β'' + P'·β' + R·β` of Zagier's operator (`LZf` below coincides
with the hypothesis operator `LZc`).

The mathematical content of `adjointZ_no_solution` is that this inhomogeneous equation has
only the trivial solution.  The proof follows the C-side template
(`Work.C17adj.adjoint_divisor_boundC`), with the smaller data below:

* `DZ = x²(x−1)` is the universal denominator: `ordAt α β ≥ 0` away from `α = 0, 1`,
  `≥ −2` at `0` and `≥ −1` at `1`, so `DZ·β` is a polynomial `W` (the *divisor bound*);
* `PhiNumZ W` is the cleared numerator `DZ³·(LZf (W/DZ))`;
* the equation forces `PhiNumZ W = PsiZ c · x³(x−1)`, and the degree chase (`W.natDegree ≤ 2`)
  plus a `6 × 6` linear system (`Zsolve`) gives `W = 0`, `c = 0`.
-/

open Polynomial

noncomputable section
namespace Work.A14D

/-- `P = x − 10x² + 9x³ = x(1−x)(1−9x)`. -/
def P2Z : Polynomial ℂ := X - 10 * X ^ 2 + 9 * X ^ 3

/-- `P' = 1 − 20x + 27x²`. -/
def P1Z : Polynomial ℂ := 1 - 20 * X + 27 * X ^ 2

/-- `R = −3 + 9x`. -/
def P0Z : Polynomial ℂ := -3 + 9 * X

/-- The universal denominator `x²(x−1)`. -/
def DZ : Polynomial ℂ := X ^ 2 * (X - 1)

/-- The common denominator `x³(x−1)²` of the three summands of the right hand side. -/
def QZ : Polynomial ℂ := X ^ 3 * (X - 1) ^ 2

/-- The left hand side of the target equation, as a function of `β` (this is literally the
expression occurring in `Work.A14D.adjointZ_no_solution`). -/
def LZc (β : RatFunc ℂ) : RatFunc ℂ :=
  Submission.CDT.dRat (Submission.CDT.dRat
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 10 * X ^ 2 + 9 * X ^ 3) * β))
    - Submission.CDT.dRat ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - 20 * X + 27 * X ^ 2)) * β)
    + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (-3 + 9 * X)) * β

/-- The same operator in expanded (self-adjoint, `P β'' + P' β' + R β`) form. -/
def LZf (β : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) P2Z * Submission.CDT.dRat (Submission.CDT.dRat β)
    + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1Z * Submission.CDT.dRat β
    + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0Z * β

/-- The right hand side `Σ_{i<3} c_i·y^{−i}·y'`. -/
def RhsZ (c : Fin 3 → ℂ) : RatFunc ℂ :=
  ∑ i : Fin 3, (algebraMap ℂ (RatFunc ℂ) (c i)) * rQc i

/-- The numerator of `RhsZ c` over the common denominator `x³(x−1)²`. -/
def PsiZ (c : Fin 3 → ℂ) : Polynomial ℂ :=
  C (c 0) * (X ^ 4 * (X - 2)) + C (c 1) * (X ^ 2 * (X - 2) * (X - 1))
    + C (c 2) * ((X - 2) * (X - 1) ^ 2)

/-- The cleared numerator `DZ³·(P β'' + P' β' + R β)` for `β = W/DZ`. -/
def PhiNumZ (W : Polynomial ℂ) : Polynomial ℂ :=
  P2Z * (W.derivative.derivative * DZ ^ 2 - 2 * W.derivative * DZ * DZ.derivative
        + W * (2 * DZ.derivative ^ 2 - DZ * DZ.derivative.derivative))
    + P1Z * (W.derivative * DZ - W * DZ.derivative) * DZ
    + P0Z * W * DZ ^ 2

/-- A polynomial of degree `≤ 2`, written with its three coefficients. -/
def Wlin (n : Fin 3 → ℂ) : Polynomial ℂ := C (n 0) + C (n 1) * X + C (n 2) * X ^ 2

lemma DZ_ne_zero : DZ ≠ 0 := by
  unfold DZ
  exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) (X_sub_C_ne_zero 1)

lemma QZ_ne_zero : QZ ≠ 0 := by
  unfold QZ
  exact mul_ne_zero (pow_ne_zero 3 X_ne_zero) (pow_ne_zero 2 (X_sub_C_ne_zero 1))

lemma P2Z_ne_zero : P2Z ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℂ => p.eval 2) h
  simp [P2Z] at this
  norm_num at this

/-- `P' = P1Z`. -/
lemma derivative_P2Z : P2Z.derivative = P1Z := by
  unfold P2Z P1Z
  simp only [Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.derivative_ofNat, Polynomial.C_eq_natCast]
  ring_nf

lemma eval_P2Z (z : ℂ) : P2Z.eval z = z * (1 - z) * (1 - 9 * z) := by
  unfold P2Z; simp; ring

lemma eval_P1Z (z : ℂ) : P1Z.eval z = 1 - 20 * z + 27 * z ^ 2 := by
  unfold P1Z; simp

lemma eval_P0Z (z : ℂ) : P0Z.eval z = -3 + 9 * z := by
  unfold P0Z; simp

/-- `P = x·F₀` with `F₀ = (1−x)(1−9x)`. -/
def Zs0 : Polynomial ℂ := (1 - X) * (1 - 9 * X)

/-- `P = (x−1)·F₁` with `F₁ = −x(1−9x)`. -/
def Zs1 : Polynomial ℂ := -(X * (1 - 9 * X))

/-- `P = (x−1/9)·F₉` with `F₉ = −9x(1−x)`. -/
def Zs9 : Polynomial ℂ := -(9 * (X * (1 - X)))

lemma P2Z_eq_X_mul_Zs0 : P2Z = (X - C (0:ℂ)) * Zs0 := by
  apply Polynomial.funext
  intro z
  simp [P2Z, Zs0]
  ring

lemma Zs0_eval_zero : Zs0.eval (0:ℂ) = 1 := by simp [Zs0]

lemma P2Z_eq_Xsub1_mul_Zs1 : P2Z = (X - C (1:ℂ)) * Zs1 := by
  apply Polynomial.funext
  intro z
  simp [P2Z, Zs1]
  ring

lemma Zs1_eval_one : Zs1.eval (1:ℂ) = 8 := by simp [Zs1]; norm_num

lemma P2Z_eq_Xsub9_mul_Zs9 : P2Z = (X - C ((1:ℂ)/9)) * Zs9 := by
  apply Polynomial.funext
  intro z
  simp [P2Z, Zs9]
  ring

lemma Zs9_eval_ninth : Zs9.eval ((1:ℂ)/9) = -(8/9) := by simp [Zs9]; norm_num

lemma eval_P2Z_deriv_one : P1Z.eval (1:ℂ) = 8 := by rw [eval_P1Z]; norm_num
lemma eval_P2Z_deriv_ninth : P1Z.eval ((1:ℂ)/9) = -(8/9) := by rw [eval_P1Z]; norm_num

lemma PsiZ_natDegree_le (c : Fin 3 → ℂ) : (PsiZ c).natDegree ≤ 5 := by
  have e2 : (2 : Polynomial ℂ) = C (2:ℂ) := (map_ofNat Polynomial.C 2).symm
  have e1 : (1 : Polynomial ℂ) = C (1:ℂ) := (map_one Polynomial.C).symm
  have h0 : (C (c 0) * (X ^ 4 * (X - 2)) : Polynomial ℂ).natDegree ≤ 5 := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, e2, Polynomial.natDegree_X_sub_C]
  have h1 : (C (c 1) * (X ^ 2 * (X - 2) * (X - 1)) : Polynomial ℂ).natDegree ≤ 5 := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_mul_le).trans ?_
    have h : (X ^ 2 * (X - 2) : Polynomial ℂ).natDegree ≤ 3 := by
      refine (natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, e2, Polynomial.natDegree_X_sub_C]
    rw [e1, Polynomial.natDegree_X_sub_C]
    omega
  have h2 : (C (c 2) * ((X - 2) * (X - 1) ^ 2) : Polynomial ℂ).natDegree ≤ 5 := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_mul_le).trans ?_
    rw [e2, Polynomial.natDegree_X_sub_C, e1, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C]
    norm_num
  unfold PsiZ
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h0 h1) h2

end Work.A14D

end
