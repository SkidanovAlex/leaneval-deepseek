/-
# Bridge: local copies of the contract vocabulary vs the frozen `Work.TMContract`

`Defs.lean` §1–§2 are byte-identical copies of `TMPlan/Interfaces.lean` §1–§2, and the
frozen `TMContract/Defs.lean` is in turn a verbatim copy of the same text, so most of the
vocabulary is *definitionally* equal across the two copies.  The exceptions are the
definitions obtained by structural recursion (`iterC`, `pruferIter`, ...): Lean compiles
them with an auxiliary `Nat.brecOn`, which is opaque on a variable argument, so `rfl` fails
even though the source text is identical.  This file proves the bridges needed for C16
(`iterC`, `frob ∘ iterC`, `lyap`, `P_LEBasics`, `P_BJ`).
-/
import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMC16Core.Defs

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC16Core.Bridge

/-- The two copies of the cocycle agree (they do not unfold definitionally because of
`Nat.brecOn`; the proof is by induction using the equation lemmas). -/
theorem iterC_eq (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    Work.TMC16Core.iterC α lam E n x = Work.TMContract.iterC α lam E n x := by
  induction n generalizing x with
  | zero => simp [Work.TMC16Core.iterC, Work.TMContract.iterC]
  | succ n ih =>
      simp only [Work.TMC16Core.iterC, Work.TMContract.iterC]
      rw [ih]
      rfl

theorem frob_iterC_eq (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    Work.TMC16Core.frob (Work.TMC16Core.iterC α lam E n x)
      = Work.TMContract.frob (Work.TMContract.iterC α lam E n x) := by
  rw [iterC_eq]
  rfl

/-- The two copies of the Lyapunov exponent agree. -/
theorem lyap_eq (α lam : ℝ) (E : ℂ) :
    Work.TMC16Core.lyap α lam E = Work.TMContract.lyap α lam E := by
  have h : (fun n : ℕ => (∫ x in (0 : ℝ)..1,
        Real.log (Work.TMC16Core.frob (Work.TMC16Core.iterC α lam E (n + 1) x))) / ((n : ℝ) + 1))
      = (fun n : ℕ => (∫ x in (0 : ℝ)..1,
        Real.log (Work.TMContract.frob (Work.TMContract.iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)) := by
    funext n
    simp only [frob_iterC_eq]
  rw [Work.TMC16Core.lyap, Work.TMContract.lyap, h]

/-- C4 against the frozen statement. -/
theorem p_leBasics_iff : Work.TMC16Core.P_LEBasics ↔ Work.TMContract.P_LEBasics := by
  simp only [Work.TMC16Core.P_LEBasics, Work.TMContract.P_LEBasics, lyap_eq,
    frob_iterC_eq]

/-- C7 against the frozen statement. -/
theorem p_bj_iff : Work.TMC16Core.P_BJ ↔ Work.TMContract.P_BJ := by
  simp only [Work.TMC16Core.P_BJ, Work.TMContract.P_BJ, lyap_eq]
  exact Iff.rfl

/-- C7 at Diophantine frequencies against the frozen statement: the frozen Diophantine case
(`Work.TMComp.RedC7T.D_BJ_dioph_uncond`) transfers to the local vocabulary through `lyap_eq`. -/
theorem p_bj_dioph_of_frozen
    (h : ∀ (α lam b₀ : ℝ), Irrational α → 0 < b₀ → Work.TMContract.DiophBelow α b₀ →
      lam ≠ 0 → ∀ E : ℝ, E ∈ Work.TMContract.amoSpec α lam →
        Work.TMContract.lyap α lam (E : ℂ) = max 0 (Real.log |lam|)) :
    Work.TMC16Core.P_BJ_dioph := by
  intro α lam b₀ hα hb hD hlam E hE
  have h1 := h α lam b₀ hα hb hD hlam E hE
  rw [lyap_eq]
  exact h1

end Work.TMC16Core.Bridge

end
