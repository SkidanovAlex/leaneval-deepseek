import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.Defs

namespace Work.WilG1.Calc

open WilkiesDesign

/-- Iterating the projection axiom `SOMin.proj` `m` times eliminates the last `m`
coordinates of a set in `ℝ^{k+m}`, at the cost of exactly `+m` in the format.  The
degree bound `D` is untouched: `projLast` (and hence `projLastIter`) preserves `D`.

The bound `F + m` is sharp in the sense that no `mono_F` bump is needed: each of the
`m` projection steps adds exactly one to the format, and the resulting format is
never raised again. -/
theorem projLastIter_mem {S : WilkiesDesign.SOMin} (k m : ℕ) {F D : ℕ}
    {X : Set (Fin (k + m) → ℝ)} (hX : X ∈ S.Ω F D (k + m)) :
    Work.WilG0.projLastIter k m X ∈ S.Ω (F + m) D k := by
  have key : ∀ m (F D : ℕ) (X : Set (Fin (k + m) → ℝ)),
      X ∈ S.Ω F D (k + m) → Work.WilG0.projLastIter k m X ∈ S.Ω (F + m) D k := by
    intro m
    induction m with
    | zero =>
      intro F D X hX
      simpa [Work.WilG0.projLastIter] using hX
    | succ m ih =>
      intro F D X hX
      -- The last coordinate is projected out; this is one `SOMin.proj` step.
      have hX' : projLast X ∈ S.Ω (F + 1) D (k + m) := S.proj hX
      -- The remaining `m` coordinates are eliminated by the induction hypothesis.
      have hres : Work.WilG0.projLastIter k m (projLast X) ∈ S.Ω ((F + 1) + m) D k :=
        ih (F + 1) D (projLast X) hX'
      have heq : (F + 1) + m = F + (m + 1) := by omega
      change Work.WilG0.projLastIter k m (projLast X) ∈ S.Ω (F + (m + 1)) D k
      exact heq ▸ hres
  exact key m F D X hX

end Work.WilG1.Calc
