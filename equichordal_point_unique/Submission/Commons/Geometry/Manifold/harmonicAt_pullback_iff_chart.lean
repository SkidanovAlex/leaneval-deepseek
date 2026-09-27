import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Commons.Geometry.Manifold

/-- Harmonicity of a real-valued function on a complex manifold is chart-independent:
if `x` lies in the source of the preferred chart at `y`, then the pullback of `u` by
the preferred chart at `x` is harmonic at the chart image of `x` iff the pullback by
the preferred chart at `y` is harmonic at its chart image of `x`. (Chart transitions
are complex-analytic by `chart_transition_analyticOnNhd`, and precomposing a
harmonic function with an analytic map preserves harmonicity by commons
`harmonicAt_comp_analytic`.) -/
theorem harmonicAt_pullback_iff_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {x y : X}
    (hxy : x ∈ (chartAt ℂ y).source) :
    InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ↔
      InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  classical
  let a : ℂ := (chartAt ℂ x) x
  let b : ℂ := (chartAt ℂ y) x
  have hxsource : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  constructor
  · -- (->) : harmonic in the chart at x  ⇒  harmonic in the chart at y
    intro hx
    let T : ℂ → ℂ := fun z => (chartAt ℂ x) ((chartAt ℂ y).symm z)
    have hlinv : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x :=
      (chartAt ℂ y).left_inv hxy
    have hb_f : b ∈ ((chartAt ℂ y).symm.trans (chartAt ℂ x)).source := by
      dsimp [b]
      rw [mem_inter_iff, mem_preimage]
      exact ⟨(chartAt ℂ y).map_source hxy, by simp [hlinv, hxsource]⟩
    have hfA_b : AnalyticAt ℂ ((chartAt ℂ y).symm.trans (chartAt ℂ x)) b := by
      exact (Commons.Geometry.Manifold.chart_transition_analyticOnNhd (X := X) (x := y) (y := x)) b hb_f
    have hfeq : (chartAt ℂ y).symm.trans (chartAt ℂ x) =ᶠ[𝓝 b] T := by
      filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ x)).open_source.eventually_mem hb_f] with z hz
      dsimp [T]
    have hTA : AnalyticAt ℂ T b := AnalyticAt.congr hfA_b hfeq
    have hTb : T b = a := by
      dsimp [T, a, b]
      simp [hlinv]
    have hx' : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ x).symm) (T b) := by
      simpa [hTb] using hx
    have hcomp : InnerProductSpace.HarmonicAt
        (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) (T z)) b := by
      exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (f := T)
        (u := u ∘ (chartAt ℂ x).symm) (x := b) hTA hx'
    -- agreement on a neighbourhood of b
    have hAg : (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) (T z)) =ᶠ[𝓝 b]
        (fun z : ℂ => (u ∘ (chartAt ℂ y).symm) z) := by
      filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ x)).open_source.eventually_mem hb_f] with z hz
      have hz2 : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source := by
        exact hz.2
      have hlinvz : (chartAt ℂ x).symm ((chartAt ℂ x) ((chartAt ℂ y).symm z))
          = (chartAt ℂ y).symm z :=
        (chartAt ℂ x).left_inv hz2
      simp only [Function.comp_apply]
      dsimp [T]
      rw [hlinvz]
    exact (InnerProductSpace.harmonicAt_congr_nhds hAg).mp hcomp
  · -- (<-) : harmonic in the chart at y  ⇒  harmonic in the chart at x
    intro hy
    let S : ℂ → ℂ := fun z => (chartAt ℂ y) ((chartAt ℂ x).symm z)
    have hlinv : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv hxsource
    have ha_g : a ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
      dsimp [a]
      rw [mem_inter_iff, mem_preimage]
      exact ⟨(chartAt ℂ x).map_source hxsource, by simpa [hlinv] using hxy⟩
    have hgA_a : AnalyticAt ℂ ((chartAt ℂ x).symm.trans (chartAt ℂ y)) a := by
      exact (Commons.Geometry.Manifold.chart_transition_analyticOnNhd (X := X) (x := x) (y := y)) a ha_g
    have hgeq : (chartAt ℂ x).symm.trans (chartAt ℂ y) =ᶠ[𝓝 a] S := by
      filter_upwards [((chartAt ℂ x).symm.trans (chartAt ℂ y)).open_source.eventually_mem ha_g] with z hz
      dsimp [S]
    have hSA : AnalyticAt ℂ S a := AnalyticAt.congr hgA_a hgeq
    have hSa : S a = b := by
      dsimp [S, a, b]
      simp [hlinv]
    have hy' : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ y).symm) (S a) := by
      simpa [hSa] using hy
    have hcomp : InnerProductSpace.HarmonicAt
        (fun z : ℂ => (u ∘ (chartAt ℂ y).symm) (S z)) a := by
      exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (f := S)
        (u := u ∘ (chartAt ℂ y).symm) (x := a) hSA hy'
    have hAg : (fun z : ℂ => (u ∘ (chartAt ℂ y).symm) (S z)) =ᶠ[𝓝 a]
        (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) z) := by
      filter_upwards [((chartAt ℂ x).symm.trans (chartAt ℂ y)).open_source.eventually_mem ha_g] with z hz
      have hz2 : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := by
        exact hz.2
      have hlinvz : (chartAt ℂ y).symm ((chartAt ℂ y) ((chartAt ℂ x).symm z))
          = (chartAt ℂ x).symm z :=
        (chartAt ℂ y).left_inv hz2
      simp only [Function.comp_apply]
      dsimp [S]
      rw [hlinvz]
    exact (InnerProductSpace.harmonicAt_congr_nhds hAg).mp hcomp

end Commons.Geometry.Manifold

end