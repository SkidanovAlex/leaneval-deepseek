import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

namespace Commons.Analysis.Complex.ChartedSpace

open Filter Metric Set
open scoped Topology

/-- Let `X` be a (`ℂ`-)charted space and `f : X → ℂ` a function which, in the preferred chart at
every point `x`, is complex analytic at the image of `x`:
`AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)` for all `x`.
Then the set of points where `f` is locally constant is clopen.

Proof sketch.  Open is immediate.  For closedness: let `xₙ → x` with `f` locally constant at each
`xₙ`.  Put `e := chartAt ℂ x`, `h := f ∘ e.symm`, analytic at `c := e x` with radius `ρ > 0`.
The points `wₙ := e xₙ` tend to `c`, and `h` is locally constant at each `wₙ` (because `f` is
locally constant at `xₙ` and `e` is a homeomorphism near `x`).  By the identity theorem `h` is
constant on the ball `Metric.ball c ρ`, hence `h` is locally constant at `c`, hence `f` is locally
constant at `x`. -/
theorem isClopen_setOf_eventuallyConst {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {f : X → ℂ}
    (hf : ∀ x, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    IsClopen {x : X | Filter.Eventually (fun y => f y = f x) (nhds x)} := by
  constructor
  · -- closedness
    rw [← closure_subset_iff_isClosed]
    intro x hx
    -- `x` is a cluster point of the set of local-constancy points.
    let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
    have hxe : x ∈ e.source := mem_chart_source ℂ x
    obtain ⟨r, hr, hana⟩ := (hf x).exists_ball_analyticOnNhd
    -- pick `y ∈ S` close to `x`, inside the source of the chart and the ball of analyticity
    have hnhds : e.source ∩ e ⁻¹' Metric.ball (e x) r ∈ 𝓝 x :=
      Filter.inter_mem (e.open_source.mem_nhds hxe)
        ((e.continuousAt hxe).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
    obtain ⟨y, ⟨⟨hy_src, hy_ball⟩, hy_S⟩⟩ :=
      mem_closure_iff_nhds.mp hx _ hnhds
    -- `f ∘ e.symm` is locally constant at `e y`
    have hh_loc : (f ∘ e.symm) =ᶠ[𝓝 (e y)] (fun _ => (f ∘ e.symm) (e y)) := by
      have h1 : ∀ᶠ z in 𝓝 (e y), f (e.symm z) = f y :=
        (e.tendsto_symm hy_src).eventually hy_S
      filter_upwards [h1] with z hz
      simp only [Function.comp_apply]
      rw [e.left_inv hy_src]
      exact hz
    -- identity theorem on the ball of analyticity
    have heq : EqOn (f ∘ e.symm) (fun _ => (f ∘ e.symm) (e y)) (Metric.ball (e x) r) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hana analyticOnNhd_const
        (convex_ball (e x) r).isPreconnected hy_ball hh_loc
    have hc_eq : (f ∘ e.symm) (e x) = (f ∘ e.symm) (e y) := heq (Metric.mem_ball_self hr)
    have hloc : ∀ᶠ z in 𝓝 (e x), (f ∘ e.symm) z = (f ∘ e.symm) (e x) := by
      filter_upwards [Metric.ball_mem_nhds (e x) hr] with z hz
      rw [heq hz, hc_eq]
    have hloc' : ∀ᶠ z in 𝓝 (e x), f (e.symm z) = f x := by
      simpa only [Function.comp_apply, e.left_inv hxe] using hloc
    exact (e.eventually_nhds' (fun u => f u = f x) hxe).mp hloc'
  · -- openness
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨t, ht, ht_eq⟩ := hx.exists_mem
    obtain ⟨u, hu, hu_open, hxu⟩ := mem_nhds_iff.mp ht
    refine mem_of_superset (hu_open.mem_nhds hxu) fun y hy => ?_
    filter_upwards [hu_open.mem_nhds hy] with z hz
    rw [ht_eq z (hu hz), ht_eq y (hu hy)]

end Commons.Analysis.Complex.ChartedSpace