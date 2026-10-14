import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.H2.WPQ

set_option autoImplicit false

/-! ## The interior commutation identity

`Work.Spaces.quadU = (-1,∞) × (0,π/2)` is the open quadrant of the class
`Work.FTS.LocData.SmoothQuad`, and on it `D_θ` commutes with the iterates of `D_z`.  This is
the pointwise Clairaut statement `Work.Spaces.Dz_Dth_comm`, which is available at every point
of `quadU` because `SmoothQuad` is *local* smoothness (`ContDiffOn ℝ smoothOrder`) and the two
operators are local. -/

/-- On the open quadrant `quadU`, `D_θ` commutes with every iterate of `D_z`. -/
theorem Dth_DzIter_comm_quadU {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) Work.Spaces.quadU := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      -- `D_z^b g` is `C^∞` (hence `C²`) near `y`, so Clairaut applies there.
      have hG : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter b g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg b
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) y :=
        (hG.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hy)).of_le
          (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DzIter b g) hcd
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [← hcomm]
      -- The two `z`-slices agree near `y` by the induction hypothesis, so their derivatives do.
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]



end Work.H2.WPQ
