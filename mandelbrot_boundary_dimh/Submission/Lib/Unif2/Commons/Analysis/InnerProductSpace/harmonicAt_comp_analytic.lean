import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Harmonic.Analytic

open Complex Metric Set InnerProductSpace
open scoped Topology

namespace Commons.Analysis.InnerProductSpace

/-- Pre-composition with a complex-analytic function preserves harmonicity. -/
theorem harmonicAt_comp_analytic {u : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hu : InnerProductSpace.HarmonicAt u (f x)) :
    InnerProductSpace.HarmonicAt (fun z : ℂ => u (f z)) x := by
  -- `u` is harmonic on a whole neighbourhood of `f x`.
  have hUopen : IsOpen {x : ℂ | InnerProductSpace.HarmonicAt u x} :=
    InnerProductSpace.isOpen_setOfPred_harmonicAt u
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hUopen (f x) hu
  have hu_ball : HarmonicOnNhd u (ball (f x) ε) := by
    intro y hy
    exact hε hy
  -- Local representation `u = Re F` with `F` holomorphic on that ball.
  obtain ⟨F, hFa, hFe⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := u) (z := f x)
      (R := ε) hu_ball
  have hFaAt : AnalyticAt ℂ F (f x) := hFa (f x) (Metric.mem_ball_self hεpos)
  -- The map `z ↦ f z` is complex-analytic at `x`, hence so is `ζ ↦ F (f ζ)`.
  have hcomp : AnalyticAt ℂ (fun ζ : ℂ => F (f ζ)) x :=
    AnalyticAt.comp (f := f) (g := F) (x := x) hFaAt hf
  have hReHarm : InnerProductSpace.HarmonicAt (fun ζ : ℂ => (F (f ζ)).re) x :=
    hcomp.harmonicAt_re
  -- `u (f ζ) = (F (f ζ)).re` for all `ζ` close to `x`.
  have hcont : ContinuousAt f x := hf.continuousAt
  have hnh : ∀ᶠ ζ in 𝓝 x, f ζ ∈ ball (f x) ε :=
    hcont.preimage_mem_nhds (Metric.ball_mem_nhds (f x) hεpos)
  have hEqNhd : (fun ζ : ℂ => u (f ζ)) =ᶠ[𝓝 x] (fun ζ : ℂ => (F (f ζ)).re) := by
    filter_upwards [hnh] with ζ hζ
    exact (hFe hζ).symm
  exact (InnerProductSpace.harmonicAt_congr_nhds hEqNhd).mpr hReHarm

end Commons.Analysis.InnerProductSpace
