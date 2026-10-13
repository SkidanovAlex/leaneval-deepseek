import Submission.Work.Wilkies.Defs
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Area H (counting) — vocabulary

This is the vocabulary of the point-counting area (BNZ, *Wilkie's conjecture for
Pfaffian structures*, §6).  The counting argument proceeds by

* covering a definable set `X` by `C^r` charts with bounded derivatives (the
  algebraic lemma, area G, available here as the hypothesis `AlgLemma`);
* interpolating the points of bounded degree and height lying near a chart by
  hypersurfaces of controlled degree, either through the *interpolation
  determinant* `interpDet` or through Siegel's lemma;
* running a dimension induction, using that a positive-dimensional connected
  semialgebraic subset of `X` lies in `X.alg` (so `X.trans` contains no such
  set).

This file fixes the vocabulary: exponent vectors, monomials, the interpolation
determinant, and the predicate "lies on a hypersurface of degree `≤ d`".
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-- Exponent vectors of total degree at most `d` in `n` variables.  We index
monomials by the finite type of functions `Fin n → Fin (d+1)` whose values sum
to at most `d`, which carries `Fintype` and `DecidableEq` instances
automatically. -/
abbrev ExpVec (n d : ℕ) : Type := {f : Fin n → Fin (d + 1) // ∑ i, ((f i : ℕ)) ≤ d}

namespace ExpVec

variable {n d : ℕ}

/-- The exponent vector as an ordinary function. -/
def toFun (α : ExpVec n d) : Fin n → ℕ := fun i => (α.val i : ℕ)

/-- The exponent vector, as a finitely supported function. -/
def toFinsupp (α : ExpVec n d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (toFun α)

lemma toFinsupp_apply (α : ExpVec n d) (i : Fin n) : toFinsupp α i = toFun α i := rfl

lemma toFun_sum_le (α : ExpVec n d) : ∑ i, toFun α i ≤ d := α.prop

lemma toFun_le (α : ExpVec n d) (i : Fin n) : toFun α i ≤ d :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (toFun_sum_le α)

lemma sum_toFinsupp (α : ExpVec n d) : (toFinsupp α).sum (fun _ e => e) = ∑ i, toFun α i := by
  rw [Finsupp.sum]
  refine (Finset.sum_subset (Finset.subset_univ (Finsupp.support (toFinsupp α))) ?_).trans ?_
  · intro i _ hi
    simpa using Finsupp.notMem_support_iff.mp hi
  · exact Finset.sum_congr rfl fun i _ => toFinsupp_apply α i

/-- The monomial with exponent vector `α`. -/
def mono (α : ExpVec n d) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.monomial (toFinsupp α) 1

lemma totalDegree_mono_le (α : ExpVec n d) : (mono α).totalDegree ≤ d := by
  rw [mono, MvPolynomial.totalDegree_monomial _ one_ne_zero, sum_toFinsupp]
  exact toFun_sum_le α

/-- Evaluation of the monomial `x ^ α` at a point. -/
def eval (α : ExpVec n d) (x : Fin n → ℝ) : ℝ := (mono α).eval x

lemma eval_eq_prod (α : ExpVec n d) (x : Fin n → ℝ) :
    eval α x = ∏ i, x i ^ toFun α i := by
  rw [eval, mono, MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  refine (Finset.prod_subset (Finset.subset_univ (Finsupp.support (toFinsupp α))) ?_).trans ?_
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  · exact Finset.prod_congr rfl fun i _ => by rw [toFinsupp_apply]

end ExpVec

/-- The number of monomials of total degree at most `d` in `n` variables. -/
def monoCount (n d : ℕ) : ℕ := Fintype.card (ExpVec n d)

/-- The interpolation determinant: the determinant of the matrix of monomial
evaluations `p i ^ α` where the points are indexed by the monomials of degree
`≤ d`. -/
def interpDet {n d : ℕ} (p : ExpVec n d → (Fin n → ℝ)) : ℝ :=
  (Matrix.of fun i α => ExpVec.eval α (p i)).det

/-- The evaluation matrix of a finite family of polynomials at a tuple of
points.  Used for the general interpolation/kernel lemma. -/
def evalMat {n k : ℕ} (κ : Fin k → MvPolynomial (Fin n) ℝ) (p : Fin k → (Fin n → ℝ)) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => (κ j).eval (p i)

/-- If the evaluation matrix of a family of polynomials at a tuple of points is
singular, then some nonzero linear combination of the family vanishes at all
the points. -/
lemma exists_coeff_of_det_eq_zero {n k : ℕ} (κ : Fin k → MvPolynomial (Fin n) ℝ)
    (p : Fin k → (Fin n → ℝ)) (h : (evalMat κ p).det = 0) :
    ∃ c : Fin k → ℝ, c ≠ 0 ∧ ∀ i, ∑ j, c j * (κ j).eval (p i) = 0 := by
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, fun i => ?_⟩
  have h1 := congrFun hv0 i
  rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply] at h1
  exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans h1

/-- `S` lies on the zero set of a nonzero real polynomial of total degree `≤ d`. -/
def LiesOnHypersurf {n : ℕ} (d : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ d ∧ ∀ x ∈ S, P.eval x = 0

end Work.WilkiesH
