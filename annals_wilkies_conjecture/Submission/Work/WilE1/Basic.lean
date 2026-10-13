/-
  Area E1 (WilE1): Bezout-type bounds for nondegenerate real zeros of polynomial systems.

  This file is pure vocabulary: it translates the frozen `EAPoly k 0`-systems (which use the
  variable type `Fin k ⊕ Fin 0`) into ordinary `MvPolynomial (Fin k) ℝ`-systems, so that the
  rest of the area can work with Mathlib's polynomial API (resultants, `pderiv`, degrees).

  Everything here is mechanical; the mathematical content lives in the later files.
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE1
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The dictionary `EAPoly k 0 ≃ MvPolynomial (Fin k) ℝ` -/

/-- `Fin k ⊕ Fin 0` is `Fin k`: an `EAPoly k 0` has no `Sum.inr` variables. -/
def sumFinZeroEquiv (k : ℕ) : (Fin k ⊕ Fin 0) ≃ Fin k where
  toFun v := match v with
    | Sum.inl i => i
    | Sum.inr j => j.elim0
  invFun i := Sum.inl i
  left_inv v := by
    cases v with
    | inl i => rfl
    | inr j => exact j.elim0
  right_inv i := rfl

/-- Renaming variables along `Fin k ⊕ Fin 0 ≃ Fin k`. -/
def eaPolyEquiv (k : ℕ) : EAPoly k 0 ≃ₐ[ℝ] MvPolynomial (Fin k) ℝ :=
  MvPolynomial.renameEquiv ℝ (sumFinZeroEquiv k)

theorem eaPolyEquiv_apply (k : ℕ) (Q : EAPoly k 0) :
    eaPolyEquiv k Q = MvPolynomial.rename (sumFinZeroEquiv k) Q := rfl

theorem eaPolyEquiv_injective (k : ℕ) : Function.Injective (eaPolyEquiv k) :=
  (eaPolyEquiv k).injective

@[simp] theorem eaPolyEquiv_X_inl (k : ℕ) (i : Fin k) :
    eaPolyEquiv k (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i := by
  simp [eaPolyEquiv, sumFinZeroEquiv]

@[simp] theorem eaPolyEquiv_C (k : ℕ) (r : ℝ) :
    eaPolyEquiv k (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [eaPolyEquiv]

/-- `eaEval` for the empty chain is evaluation of the renamed polynomial. -/
theorem eaEval_nil {k : ℕ} (Q : EAPoly k 0) (x : Fin k → ℝ) :
    eaEval (EAChain.nil k) Q x = MvPolynomial.eval x (eaPolyEquiv k Q) := by
  have h : (Sum.elim x fun j => Real.exp ((EAChain.nil k).ell j x)) = (x ∘ sumFinZeroEquiv k) := by
    funext v
    cases v with
    | inl i => rfl
    | inr j => exact j.elim0
  rw [eaEval, eaPolyEquiv_apply, MvPolynomial.eval_rename, h]

/-- `eaD` for the empty chain is the ordinary partial derivative. -/
theorem eaD_nil {k : ℕ} (i : Fin k) (Q : EAPoly k 0) :
    eaD (EAChain.nil k) i Q = MvPolynomial.pderiv (Sum.inl i) Q := by
  simp [eaD, EAChain.nil]

/-- Renaming commutes with the partial derivatives used in `eaD`. -/
theorem eaPolyEquiv_pderiv {k : ℕ} (i : Fin k) (Q : EAPoly k 0) :
    MvPolynomial.pderiv i (eaPolyEquiv k Q) = eaPolyEquiv k (MvPolynomial.pderiv (Sum.inl i) Q) := by
  rw [eaPolyEquiv_apply, eaPolyEquiv_apply]
  exact MvPolynomial.pderiv_rename (sumFinZeroEquiv k).injective (x := Sum.inl i) (p := Q)

/-- The Jacobian determinant of a `k`-tuple of exp-polynomials at `x`, for the nil chain. -/
def jacDetEvalEA {k : ℕ} (f : Fin k → EAPoly k 0) (x : Fin k → ℝ) : ℝ :=
  (Matrix.of fun i j => eaEval (EAChain.nil k) (eaD (EAChain.nil k) j (f i)) x).det

/-- The same, in the renamed (= ordinary polynomial) form. -/
def jacDetPoly {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det

theorem jacDetEval_eq {k : ℕ} (f : Fin k → EAPoly k 0) (x : Fin k → ℝ) :
    jacDetEvalEA f x = jacDetPoly (fun i => eaPolyEquiv k (f i)) x := by
  unfold jacDetEvalEA jacDetPoly
  apply congrArg Matrix.det
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply, eaD_nil, eaEval_nil, eaPolyEquiv_pderiv]

/-- The total degree is preserved by the elementary renaming. -/
theorem totalDegree_eaPolyEquiv {k : ℕ} (Q : EAPoly k 0) :
    (eaPolyEquiv k Q).totalDegree = Q.totalDegree :=
  MvPolynomial.totalDegree_renameEquiv (sumFinZeroEquiv k) Q

/-! ## §2. The ordinary-polynomial form of E1 -/

/-- The frozen `E1_bezout` conclusion, transported to ordinary polynomials.  This is the
statement the rest of the area proves (see `E1_bezout_of_E1Poly`). -/
def E1Poly : Prop :=
  ∀ k : ℕ, ∃ p : Polynomial ℕ, ∀ (F : Fin k → MvPolynomial (Fin k) ℝ)
    (s : Finset (Fin k → ℝ)),
    (∀ x ∈ s, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ jacDetPoly F x ≠ 0) →
    s.card ≤ p.eval (∑ i, ((F i).totalDegree + 1))

/-- The frozen statement of `E1_bezout`, as an explicit type. -/
def E1Statement : Prop :=
  ∀ k : ℕ, ∃ p : Polynomial ℕ, ∀ (f : Fin k → EAPoly k 0) (s : Finset (Fin k → ℝ)),
    (∀ x ∈ s, (∀ i, eaEval (EAChain.nil k) (f i) x = 0) ∧
      (Matrix.of fun i j => eaEval (EAChain.nil k) (eaD (EAChain.nil k) j (f i)) x).det ≠ 0) →
    s.card ≤ p.eval (∑ i, atomDeg (f i))

/-- `Polynomial ℕ`-evaluation is monotone in the argument. -/
theorem eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  refine Finset.sum_le_sum ?_
  intro n _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-- **E1** (the frozen hole) follows from its ordinary-polynomial form. -/
theorem E1Statement_of_E1Poly (h : E1Poly) : E1Statement := by
  intro k
  obtain ⟨p, hp⟩ := h k
  refine ⟨p, ?_⟩
  intro f s hs
  have hs' : ∀ x ∈ s, (∀ i, MvPolynomial.eval x (eaPolyEquiv k (f i)) = 0) ∧
      jacDetPoly (fun i => eaPolyEquiv k (f i)) x ≠ 0 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hs x hx
    refine ⟨fun i => ?_, ?_⟩
    · rw [← eaEval_nil]; exact h1 i
    · rw [← jacDetEval_eq]; exact h2
  have := hp (fun i => eaPolyEquiv k (f i)) s hs'
  refine le_trans this (eval_mono_nat p ?_)
  have hle : ∀ i : Fin k, ((eaPolyEquiv k) (f i)).totalDegree + 1 ≤ atomDeg (f i) := by
    intro i
    rw [totalDegree_eaPolyEquiv]
    unfold atomDeg
    omega
  exact Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)

end Work.WilE1
