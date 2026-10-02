import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology

namespace Work.GATE2.PL

/-- The canonical inverse `Function.invFunOn φ U` of an injective holomorphic function `φ` on an
open set `U ⊆ ℂ` is continuous at every point of the image `φ '' U`. -/
theorem continuousOn_invFunOn_of_injOn {U : Set ℂ} {φ : ℂ → ℂ} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : Set.InjOn φ U) :
    ContinuousOn (Function.invFunOn φ U) (φ '' U) := by
  -- φ is analytic on the open set `U`.
  have hφan : AnalyticOnNhd ℂ φ U := hφ.analyticOnNhd hU
  -- Local openness of `φ` at each point of `U`: since `φ` is injective on the open set `U`, it is
  -- not eventually constant at any `z ∈ U`, so the local open mapping theorem applies.
  have hloc : ∀ z ∈ U, 𝓝 (φ z) ≤ Filter.map φ (𝓝 z) := by
    intro z hz
    have hnc : ¬ (∀ᶠ v in 𝓝 z, φ v = φ z) := by
      intro h
      have hS : U ∩ {v : ℂ | φ v = φ z} ∈ 𝓝 z :=
        Filter.inter_mem (hU.mem_nhds hz) h
      -- any neighbourhood of `z` contains a point different from `z`.
      obtain ⟨w, hw, hwz⟩ := (nhdsWithin_neBot.mp (PerfectSpace.not_isolated z)) hS
      exact hwz (hinj hw.1 hz hw.2)
    exact (AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux (hφan z hz)).resolve_left hnc
  -- Consequently `φ` is an open map on `U`.
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (φ '' s) := by
    intro s hs hso
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hzs, rfl⟩
    exact hloc z (hs hzs) (Filter.image_mem_map (hso.mem_nhds hzs))
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hw
  -- `invFunOn φ U (φ z) = z` by injectivity of `φ` on `U`.
  have hgz : Function.invFunOn φ U (φ z) = z := by
    have hex : ∃ a ∈ U, φ a = φ z := ⟨z, hz, rfl⟩
    exact hinj (Function.invFunOn_mem hex) hz (Function.invFunOn_eq hex)
  show Filter.Tendsto (Function.invFunOn φ U) (𝓝[φ '' U] (φ z))
    (𝓝 (Function.invFunOn φ U (φ z)))
  rw [hgz]
  intro Y hY
  rw [Filter.mem_map, mem_nhdsWithin_iff_exists_mem_nhds_inter]
  obtain ⟨V, hVY, hVo, hzV⟩ := mem_nhds_iff.mp hY
  -- the open set `φ '' (V ∩ U)` is a neighbourhood of `φ z` and is mapped into `Y` by the inverse.
  have himg : φ '' (V ∩ U) ∈ 𝓝 (φ z) :=
    (hopen (V ∩ U) Set.inter_subset_right (hVo.inter hU)).mem_nhds ⟨z, ⟨hzV, hz⟩, rfl⟩
  refine ⟨φ '' (V ∩ U), himg, fun y hy => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hy.1
  change Function.invFunOn φ U (φ u) ∈ Y
  have huU : u ∈ U := hu.2
  have hthis : Function.invFunOn φ U (φ u) = u := by
    have hex : ∃ a ∈ U, φ a = φ u := ⟨u, huU, rfl⟩
    exact hinj (Function.invFunOn_mem hex) huU (Function.invFunOn_eq hex)
  rw [hthis]
  exact hVY hu.1

end Work.GATE2.PL
