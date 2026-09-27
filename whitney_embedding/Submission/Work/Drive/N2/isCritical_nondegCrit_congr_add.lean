import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.isCritical_iff_chartRep

namespace Work.Drive.N2

open scoped Manifold ContDiff

open scoped Manifold ContDiff in
/-- Criticality and nondegeneracy at a point depend only on the germ of the function at that point, up
to an additive constant: if `f` agrees near `x` with `g + c`, then `x` is a critical point of `f` iff
it is one of `g`, and the same for nondegeneracy. -/
theorem isCritical_nondegCrit_congr_add {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {f g : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ g)
    (x : M) (c : ℝ) (h : Filter.EventuallyEq (nhds x) f fun y => g y + c) :
    (Work.Drive.Morse.IsCritical f x ↔ Work.Drive.Morse.IsCritical g x) ∧
      (Work.Drive.Morse.NondegCrit f x ↔ Work.Drive.Morse.NondegCrit g x) := by
  have hsrc : x ∈ (extChartAt (𝓡 2) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt (𝓡 2) x).symm ((extChartAt (𝓡 2) x) x) = x :=
    (extChartAt (𝓡 2) x).left_inv hsrc
  -- the inverse of the chart at `x` is continuous there, so the germ equality pulls back
  have htend : Filter.Tendsto (extChartAt (𝓡 2) x).symm
      (nhds ((extChartAt (𝓡 2) x) x)) (nhds x) := by
    have hcont : ContinuousAt (extChartAt (𝓡 2) x).symm ((extChartAt (𝓡 2) x) x) :=
      continuousAt_extChartAt_symm x
    have h0 : Filter.Tendsto (extChartAt (𝓡 2) x).symm (nhds ((extChartAt (𝓡 2) x) x))
        (nhds ((extChartAt (𝓡 2) x).symm ((extChartAt (𝓡 2) x) x))) := hcont
    rwa [hx0] at h0
  have hFG : (fun y : EuclideanSpace ℝ (Fin 2) => f ((extChartAt (𝓡 2) x).symm y))
      =ᶠ[nhds ((extChartAt (𝓡 2) x) x)]
        fun y => g ((extChartAt (𝓡 2) x).symm y) + c :=
    htend.eventually h
  -- derivative of the chart representative: a constant shift is invisible
  have hshift : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        g ((extChartAt (𝓡 2) x).symm y) + c)
      = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => g ((extChartAt (𝓡 2) x).symm y)) := by
    funext w
    exact fderiv_add_const (𝕜 := ℝ) (f := fun y : EuclideanSpace ℝ (Fin 2) =>
      g ((extChartAt (𝓡 2) x).symm y)) (x := w) c
  have hderiv : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => f ((extChartAt (𝓡 2) x).symm y))
      =ᶠ[nhds ((extChartAt (𝓡 2) x) x)]
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => g ((extChartAt (𝓡 2) x).symm y)) := by
    have h1 := hFG.fderiv (𝕜 := ℝ)
    rwa [hshift] at h1
  -- criticality
  have hcrit : Work.Drive.Morse.IsCritical f x ↔ Work.Drive.Morse.IsCritical g x := by
    rw [isCritical_iff_chartRep f hf x x hsrc, isCritical_iff_chartRep g hg x x hsrc]
    rw [(hFG.fderiv_eq (𝕜 := ℝ)).trans (fderiv_add_const (f := fun y : EuclideanSpace ℝ (Fin 2) =>
      g ((extChartAt (𝓡 2) x).symm y)) c)]
  refine ⟨hcrit, ?_⟩
  -- nondegeneracy: both sides are `IsCritical _ x` conjoined with the injectivity of the Hessian
  rw [Work.Drive.Morse.NondegCrit, Work.Drive.Morse.NondegCrit, hcrit]
  have hHess : fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 2) x).symm)) ((extChartAt (𝓡 2) x) x)
      = fderiv ℝ (fderiv ℝ (g ∘ (extChartAt (𝓡 2) x).symm)) ((extChartAt (𝓡 2) x) x) := by
    simpa only [Function.comp_def] using hderiv.fderiv_eq (𝕜 := ℝ)
  constructor
  · rintro ⟨hc, hinj⟩
    exact ⟨hc, by rwa [← hHess]⟩
  · rintro ⟨hc, hinj⟩
    exact ⟨hc, by rwa [hHess]⟩

end Work.Drive.N2
