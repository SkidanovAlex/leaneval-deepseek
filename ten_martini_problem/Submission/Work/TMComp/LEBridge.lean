import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig

/-!
# `LEBridge` — the definitional bridges C4 needs

The C4 development re-uses the (verbatim) copies of `tmC`, `iterC`, `frob`, `lyap` kept by
`Work.TMC7Core` (`Submission/Work/TMC7Core/Defs.lean`), whose cocycle library
(`Cocycle.lean`, `Trig.lean`, `Scale/*`) supplies most of the algebraic lemmas.
The two copies have identical bodies, so the bridges below are proved by `rfl` up to
`unfold`/`simp`; they are the only place where the two vocabularies meet.
-/

noncomputable section

namespace Work.TMComp

open MeasureTheory

theorem tmC_bridge (lam : ℝ) (E : ℂ) (x : ℝ) :
    Work.TMC7Core.tmC lam E x = Work.TMContract.tmC lam E x := by
  rfl

theorem frob_bridge (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Work.TMC7Core.frob A = Work.TMContract.frob A := by
  rfl

theorem iterC_bridge (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    Work.TMC7Core.iterC α lam E n x = Work.TMContract.iterC α lam E n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Work.TMC7Core.iterC, Work.TMContract.iterC, ih, tmC_bridge]

theorem lyap_bridge (α lam : ℝ) (E : ℂ) :
    Work.TMC7Core.lyap α lam E = Work.TMContract.lyap α lam E := by
  simp only [Work.TMC7Core.lyap, Work.TMContract.lyap, iterC_bridge, frob_bridge]

end Work.TMComp
