import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DthIter_contDiffAt
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

/-- **`D_θ^i` commutes with `D_z` on the open quadrant, for `C^∞` (not analytic) data.**

For `f` smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)` and every `i : ℕ`,

`D_θ^i (D_z f) = D_z (D_θ^i f)`  on `Q0`.

This is the `C^∞` version of `Work.Spaces.DzDthIterCommOn` (whose hypothesis
`ContDiffOn ℝ ⊤ …` is *analyticity* in this Mathlib, whereas the elliptic chapter's `SmoothOpen`
only provides `C^∞ = Work.Stability.smoothOrder`).

Route.  Induct on `i`.  The induction step is the single-operator commutation
`Work.Spaces.Dz_Dth_comm`, which needs `ContDiffAt ℝ 2 (Function.uncurry (DthIter i f)) y` at
`y ∈ Q0`; that is available because `DthIter i f` is itself `C^∞` on `Q0`
(`Work.FTS.EllipticEst.SmoothOpen.DthIter`, i.e. `ContDiffOn` of the iterates, restricted with
`ContDiffOn.of_le (2 ≤ smoothOrder)`).  The remaining steps are the local congruence of the
`θ`-derivative on an open neighbourhood, exactly as in the existing `⊤`-version: compare the two
sides pointwise at `y ∈ Q0`, using that both functions agree on the open set `Q0` around `y`. -/
theorem DthIterDzCommOpen (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) (a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter a f)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.Dz f))) Q0 := by
  induction a with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      -- `D_θ^i f` is `C^∞` on `Q0`, hence `C²` at the interior point `y ∈ Q0`.
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i f)) y :=
        ((smoothOpen_iff_forall _).mp (hf.DthIter i) 2).contDiffAt (isOpen_Q0.mem_nhds hy)
      -- Move the outer `D_z` past the outermost `D_θ` using Clairaut/Schwarz at `y`.
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz f)) y.1 y.2
      rw [hcomm]
      -- The two functions agree on the open set `Q0` (induction hypothesis), so their
      -- `θ`-derivatives agree at `y`.
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i f)) y.1 y.2
          = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz f))
              y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen isOpen_Q0 ih hy]

end Work.FTS.EllipticEst.DzAmgm
