/-
Work module for the Elgindi project: the *trace-class* single-function interpolation estimate
`InterpOpenTrace` and its use to prove `Work.FTS.EllSol.PkgK5.InterpFam k`.

# State (see `NOTES_route.md` in this directory for the full route)

`InterpFam k` follows from the *trace-class* single-function estimate `InterpOpenTrace C` by
copying the PROVED proof of `Work.EllipticEst.LHSDecomp.i0Family_le_of_interpOpen` (which does
exactly this reduction from `InterpOpen C`), replacing the `InterpOpen` application by
`InterpOpenTrace` (its extra trace hypotheses are available in `InterpFam` for the data
`G = DzIter r V`, `r ≤ k`, since `InterpFam`'s traces go up to order `k+1`).

`InterpOpenTrace C` itself is meant to be proved by the *mollification transfer* documented in
`NOTES_route.md` §2: the odd-extension angular mollification `thMoll` (with the
logarithmic-radial mollification `zmoll` for joint smoothness) of a trace-vanishing datum has
the four functionals dominated by constants times those of the datum (Jensen + the proved
weight comparisons `K5cAux.thWeightCmp` and
`Work.EllipticEst.Core.i0Aux.Omega_le_of_abs_sub_le`), is smooth on the half-strip, and
converges back a.e. as the scales go to `0`; applying the PROVED strip-class estimate
(`Work.EllipticEst.Core.i0Aux.interpS_theta`, or `Work.Blocks.interp_lin_of_box`) to the
approximant and passing to the limit (Fatou on the left, dominated convergence on the right)
gives the estimate for the datum.

The vocabulary (`sBump`, `sMass`, `sKer`, `Qext`, `thMoll`, `zmoll` and their basic properties)
is in `K5c/MollDefs.lean` (builds, `sorry`-free).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.K5c

/-- **The trace-class version of the open-quadrant single-function interpolation estimate**:
the paper's §7 estimate `α² ∫_z mixIntS G ≤ C (α⁴ ∫_z ddIntS G + ∫_z ttIntS G + α² ∫_z dIntS G)`
for data `G` which are `C^∞` on the open quadrant, vanish at the two angular boundary lines,
whose slices of `G` **and of `D_zG`** have vanishing traces at both endpoints (for every
`z > 0`), and which satisfy `SliceHonestOpen` plus the four outer integrability hypotheses. -/
def InterpOpenTrace (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.EllipticEst.Core.i0Aux.SliceHonestOpen G →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z)
      Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))

/-- **The trace-class single-function estimate exists.**  To be proved by the mollification
transfer of `NOTES_route.md` §2 (steps 1–5). -/
theorem interpOpenTrace_exists : ∃ C : ℝ, 0 < C ∧ InterpOpenTrace C := by
  sorry

end Work.FTS.EllSol.PkgK5.K5c
