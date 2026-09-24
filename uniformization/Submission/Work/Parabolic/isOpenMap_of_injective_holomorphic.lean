import Mathlib
import Submission.Work.Parabolic.Basic

/-!
# An injective holomorphic map on a Riemann surface is open

The *open mapping theorem* in the form needed by the parabolic branch of the uniformization
theorem: if `φ : X → ℂ` is holomorphic on a complex one-manifold `X` (a Riemann surface) and is
injective, then `φ` is an open map.

The point is that local constancy of `φ` is impossible: `φ` is injective, and a chart at `x` is a
homeomorphism from an open neighbourhood of `x` onto an open subset of `ℂ`, whose source has more
than one point.  Hence, in a chart at `x`, `φ` is a holomorphic function of one complex variable
which is *not* constant near the image point, and the local open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`) applies.

The proof is done directly at the level of neighbourhood filters, using
`isOpenMap_iff_nhds_le : IsOpenMap f ↔ ∀ x, 𝓝 (f x) ≤ (𝓝 x).map f`.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace Work.Parabolic

/-- **An injective holomorphic function on a Riemann surface is an open map.**

Local form of the open mapping theorem: for each `x`, the image filter of `𝓝 x` under `φ` is finer
than `𝓝 (φ x)`.  In a chart `c` at `x` the function `φ ∘ c.symm` is analytic at `c x`; it cannot be
eventually constant there, because `c.symm` is injective on `c.target` and `φ` is injective, while
`c.target` is a nonempty open subset of `ℂ` and hence contains at least two points.  So
`AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux` gives that `φ ∘ c.symm` maps neighbourhoods
of `c x` onto neighbourhoods of `φ x`, and continuity of `c.symm` at `c x` transports this back to
`X`. -/
theorem isOpenMap_of_injective_holomorphic {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {φ : X → ℂ} (hφ : Submission.HolomorphicOnX φ Set.univ) (hinj : Function.Injective φ) :
    IsOpenMap φ := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hxt : c x ∈ c.target := c.map_source hx
  have hg : AnalyticAt ℂ (φ ∘ c.symm) (c x) := hφ x (mem_univ x)
  -- `φ ∘ c.symm` is not constant near `c x`: that would force `φ` to take the same value at two
  -- distinct points of `X`.
  have hnotconst : ¬ (∀ᶠ z in 𝓝 (c x), (φ ∘ c.symm) z = (φ ∘ c.symm) (c x)) := by
    intro hconst
    have hmem : c.target ∩ {z : ℂ | (φ ∘ c.symm) z = (φ ∘ c.symm) (c x)} ∈ 𝓝 (c x) :=
      Filter.inter_mem (c.open_target.mem_nhds hxt) hconst
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    -- a second point of the ball `ball (c x) ε`, lying on the sphere of radius `ε / 2`
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := c x) (r := ε / 2)).mpr (by positivity)
    have hymem : y ∈ Metric.ball (c x) ε := by
      rw [Metric.mem_ball]
      have h2 : dist y (c x) = ε / 2 := Metric.mem_sphere.mp hy
      rw [h2]; linarith
    have hyx : y ≠ c x := by
      intro hyx
      have h2 : dist y (c x) = ε / 2 := Metric.mem_sphere.mp hy
      rw [hyx, dist_self] at h2
      linarith
    have hty : y ∈ c.target := (hsub hymem).1
    have hgoal : (φ ∘ c.symm) y = (φ ∘ c.symm) (c x) := (hsub hymem).2
    have hx_eq : c.symm y ≠ x := by
      intro h
      have h1 : c (c.symm y) = c x := by rw [h]
      rw [c.right_inv hty] at h1
      exact hyx h1
    have hcomp1 : (φ ∘ c.symm) (c x) = φ x := by
      simp only [Function.comp_apply]
      rw [c.left_inv hx]
    have himg : φ (c.symm y) = φ x := by
      rw [Function.comp_apply] at hgoal
      rw [hgoal, hcomp1]
    exact hx_eq (hinj himg)
  rcases hg.eventually_constant_or_nhds_le_map_nhds_aux with hconst | hopen
  · exact absurd hconst hnotconst
  · -- `φ ∘ c.symm` is locally open at `c x`; compose with the continuity of `c.symm`.
    have hval : (φ ∘ c.symm) (c x) = φ x := by
      simp only [Function.comp_apply]
      rw [c.left_inv hx]
    rw [hval] at hopen
    refine le_trans hopen ?_
    rw [← Filter.map_map]
    have hcont : Filter.map (c.symm : ℂ → X) (𝓝 (c x)) ≤ 𝓝 x := by
      have h1 : Filter.map (c.symm : ℂ → X) (𝓝 (c x)) ≤ 𝓝 ((c.symm : ℂ → X) (c x)) :=
        c.continuousAt_symm hxt
      rwa [c.left_inv hx] at h1
    exact Filter.map_mono hcont

end Work.Parabolic
