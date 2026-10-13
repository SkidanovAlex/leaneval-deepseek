import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.LinvI_solves
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- `Lop (Linv h) = (6 - 10 cos²θ)·Linv h - h` on `(0, π/2)`, for `h` continuous and bounded
there with vanishing `sin θ cos²θ`-moment.

This is the first-order form of `LinvI_solves`: writing `v = LinvI h` (so that
`Lzero1 (sin 2θ · v) = h`), the substitution identity
`Lzero1 (sin 2θ · v) = -sin 2θ · v'' + (6 - 10 cos²θ) · v'`
together with `v' = Linv h` gives `-sin 2θ ·(Linv h)' + (6-10cos²θ)·Linv h = h`, i.e. the
claim, since `Lop u θ = sin(2θ)·u'(θ)`. -/
theorem Linv_lop {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |h θ| ≤ M)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Lop (Work.FTS.PhiStar.Linv h) θ
        = (6 - 10 * Real.cos θ ^ 2) * Work.FTS.PhiStar.Linv h θ - h θ := by
  intro θ hθ
  -- `v := LinvI h` is twice differentiable on the interval
  have hd1 : DifferentiableOn ℝ (Work.FTS.PhiStar.LinvI h) (Set.Ioo 0 (Real.pi / 2)) := fun t ht =>
    (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd ht).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℝ (deriv (Work.FTS.PhiStar.LinvI h))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have heq : deriv (Work.FTS.PhiStar.LinvI h) =ᶠ[𝓝 t] Work.FTS.PhiStar.Linv h := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd hs).deriv
    exact (DifferentiableAt.congr_of_eventuallyEq
      (Work.FTS.PhiStar.hasDerivAt_Linv hcont hbdd ht).differentiableAt heq).differentiableWithinAt
  -- the equation `Lzero1 (sin 2θ · v) = h`
  have hsolve : Work.FTS.EllipticEst.Lzero1
      (fun θ' => Real.sin (2 * θ') * Work.FTS.PhiStar.LinvI h θ') θ = h θ := by
    simpa only [Work.Construction.s2_eq] using
      Work.FTS.PhiStar.LinvI_solves hcont hbdd hint hmom θ hθ
  -- the substitution identity
  have hsub := Work.FTS.PhiStar.Lzero1_sin2_mul (v := Work.FTS.PhiStar.LinvI h) hθ hd1 hd2
  rw [hsub] at hsolve
  -- the two derivative evaluations at `θ`
  have hD1 : deriv (Work.FTS.PhiStar.LinvI h) θ = Work.FTS.PhiStar.Linv h θ :=
    (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd hθ).deriv
  have hD2 : deriv (deriv (Work.FTS.PhiStar.LinvI h)) θ
      = deriv (Work.FTS.PhiStar.Linv h) θ := by
    have heq : deriv (Work.FTS.PhiStar.LinvI h) =ᶠ[𝓝 θ] Work.FTS.PhiStar.Linv h := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
      exact (Work.FTS.PhiStar.hasDerivAt_LinvI hcont hbdd hs).deriv
    exact heq.deriv_eq
  rw [hD2, hD1] at hsolve
  show Real.sin (2 * θ) * deriv (Work.FTS.PhiStar.Linv h) θ
    = (6 - 10 * Real.cos θ ^ 2) * Work.FTS.PhiStar.Linv h θ - h θ
  linarith [hsolve]

end Work.FTS.PhiStar.FlatWAux
