import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ibp_kern_first_open
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.hasDerivAt_thMoll_fold
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.intervalIntegrable_pth_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `θ`-derivative of the angular mollification of a trace-class datum.**

Writing `ρ = sKer ε` for the normalised bump and

  `Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - π)`

for the three images of the doubly odd extension (see `ThMollDefs`), the fold identity
`thMoll G ε w θ = ∫_{s ∈ Iθ} Kern ρ θ s · G w s` may be differentiated under the integral
sign and then integrated by parts on `0..π/2`; the two endpoint terms `G w 0 · ψ 0` and
`G w (π/2) · ψ (π/2)` vanish because a trace-class datum vanishes at both endpoints, and the
three reflected pieces swap sign.  This gives

  `∂_θ (thMoll G ε w) θ = ∫_{s ∈ Iθ} (ρ(θ-s) + ρ(θ+s) + ρ(θ+s-π)) · ∂_θG(w,s) ds`

on the whole closed interval `Iθ = [0, π/2]`.  Only the *interval* integrability of
`s ↦ ∂_θG(w,s)` is needed — its continuity at the endpoints is not available from `TraceClass`
(which says nothing about the datum at `θ < 0`) and is not required. -/
theorem thMoll_pth_fold (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∀ w : ℝ, 0 < w → ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pth (fun z θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z θ') w θ
        = ∫ s in Work.Spaces.Iθ,
            (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
              + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth G w s := by
  intro w hw θ hθ
  -- the two endpoint *values* of the datum, and its `C^∞`-regularity on the open quadrant
  have hsm : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  have hG0 : ∀ z : ℝ, G z 0 = 0 := hT.2.1
  have hGp : ∀ z : ℝ, G z (Real.pi / 2) = 0 := hT.2.2.1
  -- the `θ`-slice `s ↦ G w s` is differentiable on the open interval, with derivative `pth`
  have hHG : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s : ℝ => G w s) (Work.Spaces.pth G w x) x := by
    intro x hx
    have hd : DifferentiableAt ℝ (fun s : ℝ => G w s) x :=
      ((hsm.curry_θ hw).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hx)
    simpa only [Work.Spaces.pth] using hd.hasDerivAt
  -- differentiating the fold under the integral sign
  have hderiv := hasDerivAt_thMoll_fold G hT hε hε1 hw θ hθ
  -- integrating the folded kernel by parts
  have hIBP := ibp_kern_first_open (ρ := Work.FTS.EllSol.PkgK5.K5c.sKer ε)
    (ρ' := deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)) (G := fun s : ℝ => G w s)
    (H := fun s : ℝ => Work.Spaces.pth G w s) (θ := θ)
    (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.hasDerivAt_sKer ε t)
    (Work.FTS.EllSol.EllPkgAux.continuous_deriv_sKer ε)
    (slice_continuousOn G hT hw) hHG (hG0 w) (hGp w)
    (intervalIntegrable_pth_slice G hT hw)
  show deriv (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w θ') θ
      = ∫ s in Work.Spaces.Iθ,
          (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
            + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth G w s
  rw [hderiv.deriv]
  exact hIBP

end Work.FTS.EllSol.EllPkgAux.MollDom
