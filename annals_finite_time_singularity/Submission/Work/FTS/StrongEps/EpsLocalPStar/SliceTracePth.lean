import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTraceO
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The angular trace of a slice, in the `pth`/`mixed`/`Wt` vocabulary

`SliceTracePth` is the version of the `C¹`-slice trace lemma `SliceTraceO` (same directory) in
which the weighted angular energy is written with the plain angular derivative `∂_θ f = pth f`,
and in which the integrability hypothesis is given in the `(0,1)`-slot form used by the
`ε`-scheme, `(D_θ f · W)²` with `D_θ f = mixed 0 1 f` and `W = Wt α z ·`.

The two integrands are related by

  `(mixed 0 1 f z θ · Wt α z θ)² = (w z)² · sin(2θ)^{2-γ} · (pth f z θ)²`

(`mixed 0 1 f = D_θ f = sin(2θ)·∂_θ f` and `Wt = w·sin(2θ)^{-γ/2}`), so the slot hypothesis is,
up to the nonzero constant `(w z)²`, integrability of the weighted energy
`sin(2θ)^{2-γ} (∂_θ f)²`; this conversion is the lemma
`Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable`.  The slice `θ ↦ f z θ` is `C¹` on
`(0,π/2)` because `f` is `C^∞` on the open quadrant (`SmoothOpen.curry_θ`).  With these two
inputs the trace and its weighted Hardy rate are exactly `SliceTraceO`. -/

/-- The integrand of `SliceTraceO` for the slice `θ ↦ f z θ`, with `pth` unfolded and the two
factors exchanged; the two sides are equal pointwise. -/
private lemma pthSq_sin_eq (f : ℝ → ℝ → ℝ) (z α : ℝ) :
    (fun θ : ℝ => (deriv (fun θ' : ℝ => f z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f z θ) ^ 2 := by
  funext θ
  rw [Work.Spaces.pth]
  ring

theorem SliceTracePth {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hslot : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo 0 (π/4),
        (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the integrability of the weighted angular energy of the slice, from the slot hypothesis
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable hα0 hα1 hz hslot
  -- the same integrand in the shape consumed by `SliceTraceO`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' : ℝ => f z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    rw [pthSq_sin_eq f z α]
    exact hint
  -- the slice is `C¹` on `(0,π/2)`, being the `θ`-slice of a `C^∞` datum on the open quadrant
  have hsm : ContDiffOn ℝ 1 (fun θ : ℝ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  obtain ⟨mu, hmu, hbd⟩ := SliceTraceO (α := α) (u := fun θ : ℝ => f z θ) hα hsm hint'
  refine ⟨mu, hmu, fun θ hθ => ?_⟩
  have hInt : (∫ σ in Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => f z θ') σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun σ _ => ?_
    rw [Work.Spaces.pth]
    ring
  have h := hbd θ hθ
  rw [hInt] at h
  simpa using h

end Work.FTS.StrongEps.EpsLocalPStar
