import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.H2.T3Q.easyZ_abs_le_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pointwise bound of a `D_z`-slot Leibniz summand, in the interior class

This is the verbatim port of `Work.FTS.H2.Transport3Aux.Z3.TZ_abs_le` from the analytic class
`Work.Spaces.SmoothNbhd` (with `θ` in the closed quadrant `Iθ`) to the interior class
`Work.FTS.LocData.SmoothQuad` (with `θ` in the open quadrant `(0,π/2)`): the only change is
the multiplier bound `Work.Spaces.DzIter_le_WlInf` (whose hypothesis is `SmoothInt`, i.e.
smoothness of the `z`-slices at *every* `θ ∈ Iθ`) replaced by its interior counterpart
`Work.FTS.H2.WPQ.DzIter_le_WlInf` (which needs `θ ∈ (0,π/2)`).  Everything else -- the
`g`-side AM–GM lemmas `abs_dzIter_mul_Whz_le_sqrt`, `abs_mul_le_of_abs_le_sqrt` and the
nonnegativity of `WlInf`, `HkIntegrand` -- is unconditional in `g`. -/



end Work.FTS.H2.T3Q
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg.ProdOpen

open scoped Real Topology ContDiff

theorem leibniz_open_Dz :
    ∀ (j : ℕ) (f g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ * g z θ) z θ =
        ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (j - b) g z θ) := by
  intro j f g hf hg z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hfs : Work.EllipticEst.Core.SmoothZ0 (fun z' => f z' θ) := hf.curry_z hθ
  have hgs : Work.EllipticEst.Core.SmoothZ0 (fun z' => g z' θ) := hg.curry_z hθ
  have key := (Work.Spaces.DerivLike.iterate_mul Work.EllipticEst.Core.Zop_DerivLike0
    Work.EllipticEst.Core.SmoothZ0_FunClass j hfs hgs) (show z ∈ Set.Ioi (0 : ℝ) from hz)
  rw [show (fun z' => f z' θ) * (fun z' => g z' θ) = (fun z' => f z' θ * g z' θ)
    from rfl] at key
  rw [congrFun (Work.FTS.LocData.Zop_iterate_slice j (fun z' θ' => f z' θ' * g z' θ') θ) z,
    key]
  exact Finset.sum_congr rfl fun b _ => by
    rw [← congrFun (Work.FTS.LocData.Zop_iterate_slice b f θ) z,
      ← congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b) g θ) z]

end Work.FTS.OpenPkg.ProdOpen
end
