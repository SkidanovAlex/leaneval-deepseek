import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

namespace Commons.Analysis.Complex.ChartedSpace

open Filter Metric Set
open scoped Topology

/-- The set of points at which a function `f : X → ℂ` is (eventually) locally constant is open. -/
theorem isOpen_setOf_eventuallyConst_nhds {X : Type*} [TopologicalSpace X] {f : X → ℂ} :
    IsOpen {x : X | ∀ᶠ y in 𝓝 x, f y = f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨t, ht, ht_eq⟩ := hx.exists_mem
  obtain ⟨u, hu, hu_open, hxu⟩ := mem_nhds_iff.mp ht
  refine mem_of_superset (hu_open.mem_nhds hxu) fun y hy => ?_
  filter_upwards [hu_open.mem_nhds hy] with z hz
  rw [ht_eq z (hu hz), ht_eq y (hu hy)]

/-- If `f` is analytic in the preferred chart at every point of an open-looking set `U`, then the
set of points at which `f` is locally constant is closed relative to `U`: any limit point of it
which lies in `U` is again a local constancy point.

This is the (restricted) closedness half of the identity principle. -/
theorem closure_setOf_eventuallyConst_inter_subset_of_analyticAt {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {U : Set X} {f : X → ℂ}
    (hf : ∀ y ∈ U, AnalyticAt ℂ (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)) :
    closure {x : X | ∀ᶠ y in 𝓝 x, f y = f x} ∩ U ⊆ {x : X | ∀ᶠ y in 𝓝 x, f y = f x} := by
  intro y hy
  obtain ⟨hy_cl, hyU⟩ := hy
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  have hye : y ∈ e.source := mem_chart_source ℂ y
  obtain ⟨r, hr, hana⟩ := (hf y hyU).exists_ball_analyticOnNhd
  have hnhds : e.source ∩ e ⁻¹' Metric.ball (e y) r ∈ 𝓝 y :=
    Filter.inter_mem (e.open_source.mem_nhds hye)
      ((e.continuousAt hye).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  obtain ⟨z, ⟨hz_src, hz_ball⟩, hz_S⟩ := mem_closure_iff_nhds.mp hy_cl _ hnhds
  have hh_loc : (f ∘ e.symm) =ᶠ[𝓝 (e z)] (fun _ => (f ∘ e.symm) (e z)) := by
    have h1 : ∀ᶠ w in 𝓝 (e z), f (e.symm w) = f z :=
      (e.tendsto_symm hz_src).eventually hz_S
    filter_upwards [h1] with w hw
    simp only [Function.comp_apply]
    rw [e.left_inv hz_src]
    exact hw
  have heq : EqOn (f ∘ e.symm) (fun _ => (f ∘ e.symm) (e z)) (Metric.ball (e y) r) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hana analyticOnNhd_const
      (convex_ball (e y) r).isPreconnected hz_ball hh_loc
  have hc_eq : (f ∘ e.symm) (e y) = (f ∘ e.symm) (e z) := heq (Metric.mem_ball_self hr)
  have hloc : ∀ᶠ w in 𝓝 (e y), (f ∘ e.symm) w = (f ∘ e.symm) (e y) := by
    filter_upwards [Metric.ball_mem_nhds (e y) hr] with w hw
    rw [heq hw, hc_eq]
  have hloc' : ∀ᶠ w in 𝓝 (e y), f (e.symm w) = f y := by
    simpa only [Function.comp_apply, e.left_inv hye] using hloc
  exact (e.eventually_nhds' (fun u => f u = f y) hye).mp hloc'

theorem eqOn_const_of_isPreconnected_of_isLocallyConst {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {U : Set X} {f : X → ℂ}
    (hf : ∀ y ∈ U, AnalyticAt ℂ (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
    {P : Set X} (hPopen : IsOpen P) (hPconn : IsPreconnected P) (hPU : P ⊆ U) {x : X}
    (hxP : x ∈ P) (hx : Filter.Eventually (fun z => f z = f x) (nhds x)) :
    Set.EqOn f (fun _ => f x) P := by
  have hSopen : IsOpen {z : X | ∀ᶠ w in 𝓝 z, f w = f z} := isOpen_setOf_eventuallyConst_nhds
  have hclosed : closure {z : X | ∀ᶠ w in 𝓝 z, f w = f z} ∩ U ⊆
      {z : X | ∀ᶠ w in 𝓝 z, f w = f z} :=
    closure_setOf_eventuallyConst_inter_subset_of_analyticAt hf
  have hxS : x ∈ {z : X | ∀ᶠ w in 𝓝 z, f w = f z} := hx
  have hPS : P ⊆ {z : X | ∀ᶠ w in 𝓝 z, f w = f z} :=
    hPconn.subset_of_closure_inter_subset hSopen ⟨x, hxP, hxS⟩
      (fun z hz => hclosed ⟨hz.1, hPU hz.2⟩)
  intro y hy
  refine hPconn.induction₂' (fun a b => f a = f b) ?_ ?_ hy hxP
  · intro a ha
    have haS : ∀ᶠ w in 𝓝 a, f w = f a := hPS ha
    filter_upwards [(nhdsWithin_le_nhds (s := P) (a := a)) haS] with b hb
    exact ⟨hb.symm, hb⟩
  · intro a b c _ _ _ hab hbc
    exact hab.trans hbc

end Commons.Analysis.Complex.ChartedSpace