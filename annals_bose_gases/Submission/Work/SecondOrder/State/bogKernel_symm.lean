import ChallengeDeps
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.SecondOrder.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SecondOrder.State

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The smooth cutoff `TrialState.cutBump r hr` is even: it is a function of
`‖z‖` only (`ContDiffBump.neg`). -/
lemma cutBump_even {r : ℝ} (hr : 0 < r) (z : ℝ³) :
    Work.TrialState.cutBump r hr (-z) = Work.TrialState.cutBump r hr z :=
  ContDiffBump.neg (Work.TrialState.cutData r hr) z

/-- A radial function is even: `om (-z) = om z` because `‖-z‖ = ‖z‖`. -/
lemma IsRadial.neg_eq {om : ℝ³ → ℝ} (hom : _root_.BoseGases.IsRadial om) (z : ℝ³) :
    om (-z) = om z :=
  hom (-z) z (by simp)

/-- The pair-correlation function `TrialState.pairCorr r hr om` of a radial
`om` is even: both factors `om` and `cutBump r hr` are. -/
lemma pairCorr_even {r : ℝ} (hr : 0 < r) {om : ℝ³ → ℝ}
    (hom : _root_.BoseGases.IsRadial om) (z : ℝ³) :
    Work.TrialState.pairCorr r hr om (-z) = Work.TrialState.pairCorr r hr om z := by
  simp only [Work.TrialState.pairCorr]
  rw [IsRadial.neg_eq hom z, cutBump_even hr z]

/-- The Bogoliubov pair kernel `bogKernel r hr om x y = pairCorr r hr om (x - y)`
is symmetric in `x` and `y`, since `pairCorr` of the radial scattering solution
`om` is an even function of the difference. -/
theorem bogKernel_symm (r : ℝ) (hr : 0 < r) {om : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hom : _root_.BoseGases.IsRadial om) (x y : EuclideanSpace ℝ (Fin 3)) :
    Work.SecondOrder.bogKernel r hr om x y = Work.SecondOrder.bogKernel r hr om y x := by
  have hsub : y - x = -(x - y) := (neg_sub x y).symm
  simp only [Work.SecondOrder.bogKernel, hsub]
  exact (pairCorr_even hr hom (x - y)).symm

end Work.SecondOrder.State
