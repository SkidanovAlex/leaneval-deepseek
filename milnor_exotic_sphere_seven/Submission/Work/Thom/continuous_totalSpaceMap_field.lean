import Mathlib
import Submission.Work.Thom.exists_punctMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Continuity of the total-space map of a bundle morphism, over a general normed field

This generalises `Work.Thom.continuous_totalSpaceMap` (the case `𝕜 = ℝ`) to an arbitrary
`NontriviallyNormedField 𝕜`.  If the gluing data `Z₁` over `B'` is `Z₂` pulled back along a
continuous map `f : C(B', B)` — as witnessed by the base sets and the coordinate changes — then
the evident map `⟨x, v⟩ ↦ ⟨f x, v⟩` on total spaces is continuous.

The proof is local: in the trivialisation `Z.localTriv i` of the source bundle the map is the
evident map `B' × F → B × F` followed by the inverse of the trivialisation of the target bundle,
and a comparison of coordinate formulae identifies the two.
-/

namespace Work.Thom

open Bundle

noncomputable section

theorem continuous_totalSpaceMap_field {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {F : Type} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {ι : Type} (Z₁ : VectorBundleCore 𝕜 B' F ι)
    (Z₂ : VectorBundleCore 𝕜 B F ι) (f : C(B', B))
    (hbase : ∀ i, Z₁.baseSet i = f ⁻¹' Z₂.baseSet i)
    (hcoord : ∀ x i, Z₁.coordChange (Z₁.indexAt x) i x
      = Z₂.coordChange (Z₂.indexAt (f x)) i (f x)) :
    Continuous (fun p : Z₁.TotalSpace => (⟨f p.1, p.2⟩ : Z₂.TotalSpace)) := by
  -- The coordinate expression of the map, read in the trivialisation `i` of the target.
  have hkey : ∀ (i : ι) (p : Z₁.TotalSpace),
      (Z₂.localTriv i) (⟨f p.1, p.2⟩ : Z₂.TotalSpace)
        = (⟨f ((Z₁.localTriv i) p).1, ((Z₁.localTriv i) p).2⟩ : B × F) := by
    intro i p
    rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
    exact Prod.ext rfl (congrArg (fun (L : F →L[𝕜] F) => L p.2) (hcoord p.1 i).symm)
  have hφ : Continuous (fun q : B' × F => (⟨f q.1, q.2⟩ : B × F)) :=
    (f.continuous.comp continuous_fst).prodMk continuous_snd
  -- Continuity on each trivialisation source.
  have hgOn : ∀ i : ι, ContinuousOn (fun p : Z₁.TotalSpace => (⟨f p.1, p.2⟩ : Z₂.TotalSpace))
      (Z₁.localTriv i).source := by
    intro i
    have hcomp : ContinuousOn
        (fun p : Z₁.TotalSpace => (⟨f ((Z₁.localTriv i) p).1, ((Z₁.localTriv i) p).2⟩ : B × F))
        (Z₁.localTriv i).source :=
      hφ.comp_continuousOn (Z₁.localTriv i).continuousOn
    have hcomp' : ContinuousOn
        (fun p : Z₁.TotalSpace => (Z₂.localTriv i) (⟨f p.1, p.2⟩ : Z₂.TotalSpace))
        (Z₁.localTriv i).source :=
      hcomp.congr (fun p _ => hkey i p)
    have hmaps : Set.MapsTo
        (fun p : Z₁.TotalSpace => (Z₂.localTriv i) (⟨f p.1, p.2⟩ : Z₂.TotalSpace))
        (Z₁.localTriv i).source (Z₂.localTriv i).target := by
      intro p hp
      rw [Trivialization.mem_target]
      have h1 : p.1 ∈ Z₁.baseSet i := (VectorBundleCore.mem_localTriv_source Z₁ i p).mp hp
      rw [hbase i] at h1
      exact h1
    have hmsrc : Set.MapsTo
        (fun p : Z₁.TotalSpace => (⟨f p.1, p.2⟩ : Z₂.TotalSpace))
        (Z₁.localTriv i).source (Z₂.localTriv i).source := by
      intro p hp
      rw [VectorBundleCore.mem_localTriv_source]
      have h1 : p.1 ∈ Z₁.baseSet i := (VectorBundleCore.mem_localTriv_source Z₁ i p).mp hp
      rw [hbase i] at h1
      exact h1
    have hfinal := (Z₂.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp hcomp' hmaps
    exact hfinal.congr (fun p hp => (OpenPartialHomeomorph.left_inv _ (hmsrc hp)).symm)
  rw [continuous_iff_continuousAt]
  intro p
  refine (hgOn (Z₁.indexAt p.1)).continuousAt
    ((Z₁.localTriv (Z₁.indexAt p.1)).open_source.mem_nhds ?_)
  exact (VectorBundleCore.mem_localTriv_source Z₁ (Z₁.indexAt p.1) p).mpr (Z₁.mem_baseSet_at p.1)

end

end Work.Thom
