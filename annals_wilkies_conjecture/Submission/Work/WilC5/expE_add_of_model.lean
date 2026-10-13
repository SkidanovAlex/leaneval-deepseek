/-
  WilC5 — the exponential is additive in every model of `TE = Th(ℝ_exp)`.

  In `ℝ_exp` the exponential satisfies `exp (x + y) = exp x * exp y`.  This is a
  universally quantified `LEc`-sentence, hence it belongs to `TE = LEc.completeTheory ℝ`
  and holds in every model of `TE`.  We write the sentence down, check it on `ℝ`, and
  transfer it with `Work.WilC5.transfer`.
-/
import Mathlib
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.ReductEmb

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## The formula `exp (x + y) = exp x * exp y` -/

/-- The `LEc`-formula `exp (x + y) = exp x * exp y` in two free variables. -/
def expAddFormula : LEc.BoundedFormula Empty 2 :=
  Term.bdEqual (eExp (eAdd (v2 0) (v2 1))) (eMul (eExp (v2 0)) (eExp (v2 1)))

/-- Its realization is the additivity of `expE`, by the `LEc`-structure operations. -/
theorem expAddFormula_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    expAddFormula.Realize (emptyVar : Empty → M) xs ↔
      expE (addE (xs 0) (xs 1)) = mulE (expE (xs 0)) (expE (xs 1)) := by
  rw [expAddFormula, BoundedFormula.realize_bdEqual]
  simp only [v2, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eExp, realize_eMul]

/-- The formula holds in `ℝ`: `Real.exp_add`. -/
theorem expAdd_real : ∀ xs : Fin 2 → ℝ, expAddFormula.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [expAddFormula_realize]
  rw [addE_real, expE_real, expE_real, expE_real, mulE_real, Real.exp_add]

/-! ## Transfer to arbitrary models of `TE` -/

theorem expE_add_of_model {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) (a b : M) :
    Work.WilC5.expE (Work.WilC5.addE a b) =
      Work.WilC5.mulE (Work.WilC5.expE a) (Work.WilC5.expE b) := by
  have h := transfer hM expAddFormula expAdd_real ![a, b]
  rw [expAddFormula_realize] at h
  simpa using h

end Work.WilC5
