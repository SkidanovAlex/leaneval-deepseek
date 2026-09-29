import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMContract.Components

/-!
# Bridge: C7's local `P_BJ` vs the frozen `Work.TMContract.P_BJ`

`Defs.lean` is a copy of the contract vocabulary, and the frozen `TMContract/Defs.lean`
is a verbatim copy of the same text, so nearly all definitions are *definitionally*
equal.  The exceptions come from `iterC`, obtained by structural recursion: Lean compiles
it with an auxiliary `Nat.brecOn`, opaque on a variable argument, so `rfl` fails even
though the source text is identical.  This file proves the bridges (`iterC`, `frob ∘
iterC`, `lyap`) needed to transfer `P_BJ`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Bridge

/-- The two copies of the spectrum set agree. -/
theorem amoSpec_eq (α lam : ℝ) :
    Work.TMC7Core.amoSpec α lam = Work.TMContract.amoSpec α lam := rfl

/-- The two copies of the cocycle agree (they do not unfold definitionally because of
`Nat.brecOn`; the proof is by induction using the equation lemmas). -/
theorem iterC_eq (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    Work.TMC7Core.iterC α lam E n x = Work.TMContract.iterC α lam E n x := by
  induction n generalizing x with
  | zero => simp [Work.TMC7Core.iterC, Work.TMContract.iterC]
  | succ n ih =>
      simp only [Work.TMC7Core.iterC, Work.TMContract.iterC]
      rw [ih]
      rfl

theorem frob_iterC_eq (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x)
      = Work.TMContract.frob (Work.TMContract.iterC α lam E n x) := by
  rw [iterC_eq]
  rfl

/-- The two copies of the Lyapunov exponent agree. -/
theorem lyap_eq (α lam : ℝ) (E : ℂ) :
    Work.TMC7Core.lyap α lam E = Work.TMContract.lyap α lam E := by
  have h : (fun n : ℕ => (∫ x in (0 : ℝ)..1,
        Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E (n + 1) x))) / ((n : ℝ) + 1))
      = (fun n : ℕ => (∫ x in (0 : ℝ)..1,
        Real.log (Work.TMContract.frob (Work.TMContract.iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)) := by
    funext n
    simp only [frob_iterC_eq]
  rw [Work.TMC7Core.lyap, Work.TMContract.lyap, h]

/-- **C7** transferred from the local vocabulary to the frozen contract. -/
theorem P_BJ_transfer (h : Work.TMC7Core.P_BJ) : Work.TMContract.P_BJ := by
  simpa only [Work.TMC7Core.P_BJ, Work.TMContract.P_BJ, lyap_eq, amoSpec_eq] using h

end Work.TMC7Core.Bridge

end
