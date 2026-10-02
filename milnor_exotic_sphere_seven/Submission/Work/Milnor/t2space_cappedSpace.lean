import Mathlib
import Submission.Work.Milnor.CapCompact
import Submission.Work.Glue.glued_t2space
import Submission.Work.Milnor.UnitSphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

noncomputable section

/-- The graph of the compact capping map `capFunK e` over the collar `collar (-2) = {1/2 < ν}`
is closed in `Vk (-2) × ℝ⁸`.

The point is that the only way to leave the collar is to approach the level `ν = 1/2`, where the
capping map `(ν - 1/2)⁻¹ • e(ψ p)` blows up: on the graph the product
`‖z.2‖ * (ν z.1 - 1/2)` is identically `1`, and the set where it is `≥ 1` is closed and forces
`ν z.1 - 1/2 > 0`.  Hence any limit point of the graph lies again on the graph. -/
theorem graph_closed_capFunK
    (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Sph8) :
    IsClosed {z : Vk (-2) × EuclideanSpace ℝ (Fin 8) |
      z.1 ∈ collar (-2) ∧ z.2 = capFunK e z.1} := by
  set S : Set (Vk (-2) × EuclideanSpace ℝ (Fin 8)) :=
    {z : Vk (-2) × EuclideanSpace ℝ (Fin 8) |
      z.1 ∈ collar (-2) ∧ z.2 = capFunK e z.1} with hS
  rw [← closure_subset_iff_isClosed]
  intro z hz
  -- the continuous function `F w = ‖w.2‖ * (ν w.1 - 1/2)`
  have hν : Continuous (fun w : Vk (-2) × EuclideanSpace ℝ (Fin 8) => fibreNormFun (-2) w.1) :=
    (continuous_fibreNormFun (-2)).comp continuous_fst
  have hn : Continuous (fun w : Vk (-2) × EuclideanSpace ℝ (Fin 8) => ‖w.2‖) :=
    continuous_norm.comp continuous_snd
  have hcontF : Continuous (fun w : Vk (-2) × EuclideanSpace ℝ (Fin 8) =>
      ‖w.2‖ * (fibreNormFun (-2) w.1 - 1 / 2)) :=
    hn.mul (hν.sub continuous_const)
  have hAclosed : IsClosed {w : Vk (-2) × EuclideanSpace ℝ (Fin 8) |
      1 ≤ ‖w.2‖ * (fibreNormFun (-2) w.1 - 1 / 2)} :=
    isClosed_le continuous_const hcontF
  have hSA : S ⊆ {w : Vk (-2) × EuclideanSpace ℝ (Fin 8) |
      1 ≤ ‖w.2‖ * (fibreNormFun (-2) w.1 - 1 / 2)} := by
    intro w hw
    rw [hS] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hpos : 0 < fibreNormFun (-2) w.1 - 1 / 2 := by
      have := mem_collar.mp hw1; linarith
    change 1 ≤ ‖w.2‖ * (fibreNormFun (-2) w.1 - 1 / 2)
    rw [hw2, norm_capFunK e hw1, inv_mul_cancel₀ (ne_of_gt hpos)]
  have hzA : 1 ≤ ‖z.2‖ * (fibreNormFun (-2) z.1 - 1 / 2) :=
    closure_minimal hSA hAclosed hz
  -- hence `z.1` lies in the collar
  have hzpos : 0 < fibreNormFun (-2) z.1 - 1 / 2 := by
    by_contra h
    push Not at h
    have : ‖z.2‖ * (fibreNormFun (-2) z.1 - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) h
    linarith
  have hz1mem : z.1 ∈ collar (-2) := mem_collar.mpr (by linarith)
  -- `capFunK e` is continuous at `z.1`, so `w ↦ (w.1, capFunK e w.1)` is continuous at `z`
  have hcat : ContinuousAt (capFunK e) z.1 :=
    ((continuousOn_capFunK e).continuousWithinAt hz1mem).continuousAt
      ((isOpen_collar (-2)).mem_nhds hz1mem)
  have hcont : ContinuousAt (fun w : Vk (-2) × EuclideanSpace ℝ (Fin 8) =>
      (w.1, capFunK e w.1)) z :=
    continuousAt_fst.prodMk (hcat.comp continuousAt_fst)
  have htend1 : Filter.Tendsto id (𝓝[S] z) (𝓝 z) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have htend2 : Filter.Tendsto (fun w : Vk (-2) × EuclideanSpace ℝ (Fin 8) =>
      (w.1, capFunK e w.1)) (𝓝[S] z) (𝓝 (z.1, capFunK e z.1)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (fun w : Vk (-2) × EuclideanSpace ℝ (Fin 8) => (w.1, capFunK e w.1))
      =ᶠ[𝓝[S] z] id := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hS] at hw
    exact Prod.ext rfl hw.2.symm
  have hz' : z = (z.1, capFunK e z.1) := by
    have hneBot : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
    exact tendsto_nhds_unique htend1 (Filter.Tendsto.congr' hev htend2)
  have hz2 : z.2 = capFunK e z.1 := by
    have h := congrArg Prod.snd hz'
    simpa using h
  rw [hS]
  exact ⟨hz1mem, hz2⟩

theorem t2space_cappedSpace (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) (D : Work.Milnor.CapData) (hD : Work.Milnor.IsCompactCapping e D) :
    T2Space (Work.Milnor.cappedSpace D) := by
  refine Work.Glue.glued_t2space D ?_
  have hgraph : {z : Vk (-2) × EuclideanSpace ℝ (Fin 8) |
      z.1 ∈ D.U ∧ (D.φ z.1 : EuclideanSpace ℝ (Fin 8)) = z.2}
      = {z : Vk (-2) × EuclideanSpace ℝ (Fin 8) |
          z.1 ∈ collar (-2) ∧ z.2 = capFunK e z.1} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : z.1 ∈ collar (-2) := hD.1 ▸ h1
      refine ⟨h1', ?_⟩
      have hφ := hD.2.2 ⟨z.1, h1⟩
      rw [← h2]
      exact hφ
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · exact hD.1.symm ▸ h1
      · have hφ := hD.2.2 ⟨z.1, hD.1.symm ▸ h1⟩
        rw [h2]
        exact hφ
  rw [hgraph]
  exact graph_closed_capFunK e

end

end Work.Milnor
