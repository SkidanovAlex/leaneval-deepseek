import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.aeI1Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

/-- The rectangle `[a,b] × [c,d]` of the statement lies in the open quadrant when
`a > 0`, `c > 0` and `d < π/2` (and is empty otherwise). -/
theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩

/-- The iterated angular derivative `∂_θ^i` of a datum smooth on the open quadrant is again
smooth on the open quadrant. -/
theorem smoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Continuity of `∂_θ^i F` on the open quadrant. -/
theorem continuousOn_uncurry_pthIter {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter i F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
  (smoothOpen_pthIter hF i).continuousOn

/-- **Continuity of `U u · BB u` on a rectangle of the open quadrant.**

Here `U u = z ∂_z u` (a first-order radial factor, bounded on the rectangle because `z` is) and
`BB u = ∂_θθ u`; on the open quadrant both are continuous, and the rectangle `[a,b] × [c,d]`
with `a > 0`, `c > 0`, `d < π/2` is contained in the open quadrant. -/
theorem UBB_continuousOn_box {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.EllipticEst.AeI1Fts.U u p.1 p.2 * Work.FTS.EllipticEst.AeI1Fts.BB u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hbox : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 :=
    box_subset_Q0 ha hc hd
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hS.pz).continuousOn
  have hBB : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_uncurry_pthIter hS 2
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * Work.Spaces.pz u p.1 p.2 * Work.Spaces.pthIter 2 u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.mul (hpz.mono hbox)).mul (hBB.mono hbox)
  simpa only [U, BB] using hmain

end Work.FTS.EllipticEst.AeI1Fts
