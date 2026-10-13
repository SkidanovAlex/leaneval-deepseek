/-
  WilC5 — the definable logarithm inverts the exponential in every model of `TE = Th(ℝ_exp)`:

      `logFun (exp x) = x`.

  The definable logarithm `logFun` (`ExpLog.lean`) is, in a model of `TE`, *the* element whose
  graph is

      `logDefSet x y  =  (0 < x ∧ exp y = x) ∨ (¬ 0 < x ∧ exp y = 1)`

  (`LogFunMap.lean`, `logFun_spec_of_model` / `logDefSet_unique_of_model`).  Hence it suffices to
  exhibit *one* `y` with `logDefSet (exp x) y`, namely `x` itself: this needs only that `exp x` is
  strictly positive, `0 < exp x`, so that the first clause applies with `exp x = exp x`.

  That `exp` is strictly positive is the `LEc`-sentence `∀ x, 0 < exp x`, true in `ℝ` (where `0 < ·`
  is the definable strict order `leE zeroE · ∧ ¬ leE · zeroE`), hence in every model of `TE` by
  `Work.WilC5.transfer` (`ReductEmb.lean`).
-/
import Mathlib
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.Bridge
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.LogFunMap
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LogFunReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LEc`-sentence `0 < exp x` -/

/-- The `LEc`-formula `0 < exp x`, i.e. `exp x` is strictly positive for the definable order
`0 < t  :=  leE zeroE t ∧ ¬ leE t zeroE`. -/
def expPosForm : LEc.BoundedFormula Empty 1 :=
  leForm eZero (eExp (v1 0)) ⊓ (leForm (eExp (v1 0)) eZero).not

theorem expPosForm_realize {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    expPosForm.Realize (emptyVar : Empty → M) xs ↔
      (leE zeroE (expE (xs 0)) ∧ ¬ leE (expE (xs 0)) zeroE) := by
  rw [expPosForm, BoundedFormula.realize_inf, BoundedFormula.realize_not, leForm_realize,
    leForm_realize]
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eZero, realize_eExp, leE]

theorem expPosForm_real : ∀ xs : Fin 1 → ℝ, expPosForm.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [expPosForm_realize]
  simp only [leE_real, expE_real, zeroE_real]
  exact ⟨le_of_lt (Real.exp_pos _), not_le.mpr (Real.exp_pos _)⟩

/-- **The exponential is strictly positive in every model of `TE`.** -/
theorem expE_pos_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M) :
    leE zeroE (expE x) ∧ ¬ leE (expE x) zeroE := by
  have h := transfer hM expPosForm expPosForm_real ![x]
  rw [expPosForm_realize] at h
  simpa using h

/-! ## 2. The logarithm of an exponential -/

theorem logFun_expE {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) (x : M) :
    Work.WilC5.logFun (Work.WilC5.expE x) = x := by
  -- `x` is a logarithm of `exp x`, since `exp x` is strictly positive.
  have hspec : Work.WilC5.logDefSet (Work.WilC5.expE x) x :=
    Or.inl ⟨Work.WilC5.expE_pos_of_model hM x, rfl⟩
  -- and `logFun (exp x)` is the unique such element.
  exact Work.WilC5.logDefSet_unique_of_model hM
    (Work.WilC5.logFun_spec_of_model hM (Work.WilC5.expE x)) hspec

end Work.WilC5
