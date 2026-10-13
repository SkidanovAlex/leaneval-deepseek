/-
  Area E1 (WilE1): complexification bookkeeping.

  The counting argument is carried out over `ℂ` (so that dimensions and the Nullstellensatz are
  available).  These lemmas move a real system and a real point to `ℂ`.
-/
import Submission.Work.WilE1.Setup

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE1

/-- Evaluating a complexified real polynomial at a complexified real point. -/
theorem eval_map_complex (k : ℕ) (P : MvPolynomial (Fin k) ℝ) (x : Fin k → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) P) =
      algebraMap ℝ ℂ (MvPolynomial.eval x P) := by
  rw [MvPolynomial.eval_map]
  simpa [Function.comp_def] using
    (MvPolynomial.eval₂_comp (algebraMap ℝ ℂ) x P).symm

/-- The complexified Jacobian determinant at a complexified point. -/
theorem jacDetEvalC_map_complex (k : ℕ) (F : Fin k → MvPolynomial (Fin k) ℝ) (x : Fin k → ℝ) :
    jacDetEvalC (fun i => MvPolynomial.map (algebraMap ℝ ℂ) (F i)) (fun i => (x i : ℂ)) =
      algebraMap ℝ ℂ (jacDetEval F x) := by
  unfold jacDetEvalC jacDetEval
  have hM : (Matrix.of fun i j => MvPolynomial.eval (fun i => (x i : ℂ))
        (MvPolynomial.pderiv j (MvPolynomial.map (algebraMap ℝ ℂ) (F i))))
      = (Matrix.of fun i j =>
          MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).map (algebraMap ℝ ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, MvPolynomial.pderiv_map, eval_map_complex]
  rw [hM]
  exact (RingHom.map_det (algebraMap ℝ ℂ) _).symm

/-- Complexifying a real point is injective. -/
theorem complexifyPoint_injective (k : ℕ) :
    Function.Injective (fun x : Fin k → ℝ => fun i => (x i : ℂ)) := by
  intro x y h
  funext i
  have h' : (x i : ℂ) = (y i : ℂ) := congrFun h i
  exact_mod_cast h'

end Work.WilE1
