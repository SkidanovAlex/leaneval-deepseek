import Mathlib
import Submission.Work.WilE1.Basic
import Submission.Work.WilE1.Setup
import Submission.Work.WilE1.Transfer
import Submission.Work.WilE2.Defs

set_option autoImplicit false

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

variable {n : ℕ}

/-! ## Dictionary for the empty chain

An `ESys n 0` has no chain functions: `S.a : Fin 0 → Fin n → ℝ` and `S.b : Fin 0 → ℝ`
are the unique (vacuous) functions, so `S` is the system of the frozen empty chain
`EAChain.nil n`.  Consequently `S.ev` is `eaEval (EAChain.nil n)` and `S.d` is
`eaD (EAChain.nil n)`. -/

theorem ESys.ev_eq_eaEval_nil (S : ESys n 0) (Q : EPoly n 0) (x : Fin n → ℝ) :
    S.ev Q x = eaEval (EAChain.nil n) Q x := by
  have h : (Sum.elim x fun j => S.psi j x)
      = (Sum.elim x fun j => Real.exp ((EAChain.nil n).ell j x)) := by
    funext v
    cases v with
    | inl i => rfl
    | inr j => exact j.elim0
  rw [ESys.ev, eaEval, h]

theorem ESys.d_eq_eaD_nil (S : ESys n 0) (i : Fin n) (Q : EPoly n 0) :
    S.d i Q = eaD (EAChain.nil n) i Q := by
  simp [ESys.d, eaD]

/-- For an `ESys n 0`, evaluation of the (renamed) polynomials along the system agrees with
ordinary polynomial evaluation. -/
theorem ESys.ev_eq_eval (S : ESys n 0) (Q : EPoly n 0) (x : Fin n → ℝ) :
    S.ev Q x = MvPolynomial.eval x (Work.WilE1.eaPolyEquiv n Q) := by
  rw [ESys.ev_eq_eaEval_nil, Work.WilE1.eaEval_nil]

theorem ESys_nil_dictionary {n : ℕ} (S : ESys n 0) (F : Fin n → EPoly n 0) (T : Finset (Fin n → ℝ))
    (hT : ∀ x ∈ T, S.Nondegen F x) :
    ∀ x ∈ T,
      (∀ i, MvPolynomial.eval (fun j => (x j : ℂ))
        (MvPolynomial.map (algebraMap ℝ ℂ) (Work.WilE1.eaPolyEquiv n (F i))) = 0) ∧
      Work.WilE1.jacDetEvalC (fun i => MvPolynomial.map (algebraMap ℝ ℂ) (Work.WilE1.eaPolyEquiv n (F i)))
        (fun j => (x j : ℂ)) ≠ 0 := by
  intro x hx
  obtain ⟨h1, h2⟩ := hT x hx
  -- The real evaluation statement, in renamed variables.
  have hreal1 : ∀ i, MvPolynomial.eval x (Work.WilE1.eaPolyEquiv n (F i)) = 0 := by
    intro i
    rw [← Work.WilE1.eaEval_nil, ← ESys.ev_eq_eaEval_nil]
    exact h1 i
  -- The real Jacobian determinant equals the determinant of the system's Jacobian matrix.
  have hmat : (Matrix.of fun i j => S.ev (S.d j (F i)) x)
      = Matrix.of (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j
          (Work.WilE1.eaPolyEquiv n (F i)))) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [ESys.ev_eq_eaEval_nil S (S.d j (F i)) x, ESys.d_eq_eaD_nil S j (F i),
      Work.WilE1.eaEval_nil (eaD (EAChain.nil n) j (F i)) x,
      Work.WilE1.eaD_nil j (F i), ← Work.WilE1.eaPolyEquiv_pderiv j (F i)]
  have hreal2 : Work.WilE1.jacDetEval (fun i => Work.WilE1.eaPolyEquiv n (F i)) x ≠ 0 := by
    have heq : Work.WilE1.jacDetEval (fun i => Work.WilE1.eaPolyEquiv n (F i)) x
        = (Matrix.of fun i j => S.ev (S.d j (F i)) x).det := by
      unfold Work.WilE1.jacDetEval
      rw [hmat]
    rw [heq]
    exact h2
  constructor
  · intro i
    rw [Work.WilE1.eval_map_complex, hreal1 i]
    simp
  · rw [Work.WilE1.jacDetEvalC_map_complex]
    intro h
    exact hreal2 ((FaithfulSMul.algebraMap_injective ℝ ℂ) (by simp [h]))

end Work.WilE2
