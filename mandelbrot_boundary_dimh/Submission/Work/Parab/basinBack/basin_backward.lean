import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Backward invariance of the uniform parabolic basin

`MandelDim.ParabolicBasin f D` is the *uniform* basin of the parabolic fixed point `0`: `z` is a
basin point if some neighbourhood `U` of `z` has all its iterates inside `D` and the iterates
`f^[n]` converge to `0` uniformly on `U`.

The companion fact `Work.Parab.basin_forward` says that the basin is forward invariant (for a
non-eventually-constant germ); this file proves the *backward* direction, which holds for any
`f` analytic at `z` and any `D` that is a neighbourhood of `z`: if `f z` is in the basin, then so
is `z`.

The neighbourhood witnessing this for `z` is `D ∩ f⁻¹' U`, where `U` is the neighbourhood of
`f z` coming from the basin hypothesis.  It is a neighbourhood of `z` because `f` is continuous
at `z`, its points lie in `D`, and their images lie in `U`, so all iterates stay in `D` and the
uniform convergence on `U` transfers to it by the identity `f^[n+1] x = f^[n] (f x)`.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab.basinBack

noncomputable section

theorem basin_backward {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ} (hzan : AnalyticAt ℂ f z)
    (hD : D ∈ nhds z) (hfz : f z ∈ MandelDim.ParabolicBasin f D) :
    z ∈ MandelDim.ParabolicBasin f D := by
  obtain ⟨U, hU, hmap, hconv⟩ := hfz
  -- `f` is continuous at `z`, so `f ⁻¹' U` is a neighbourhood of `z`
  have ht : Tendsto f (𝓝 z) (𝓝 (f z)) := hzan.continuousAt
  have hV : D ∩ f ⁻¹' U ∈ 𝓝 z := inter_mem hD (ht hU)
  refine ⟨D ∩ f ⁻¹' U, hV, ?_, ?_⟩
  · -- all iterates of a point of `D ∩ f ⁻¹' U` stay in `D`
    intro n x hx
    obtain ⟨hxD, hxU⟩ := hx
    cases n with
    | zero => exact hxD
    | succ m =>
      rw [Function.iterate_succ_apply]
      exact hmap m hxU
  · -- uniform convergence on `U` shifts to uniform convergence on `D ∩ f ⁻¹' U`
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    have hc := hconv ε hε
    rw [Filter.eventually_atTop] at hc ⊢
    obtain ⟨M, hM⟩ := hc
    refine ⟨M + 1, fun n hn x hx => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    exact hM m (by omega) (f x) hx.2

end

end Work.Parab.basinBack
