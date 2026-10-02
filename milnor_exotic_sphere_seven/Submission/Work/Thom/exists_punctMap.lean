import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The map of zero-complements induced by a bundle morphism

Given a complex vector bundle `Z` over `B` (presented by gluing data) and a continuous map
`f : C(B', B)`, the pullback bundle `bundleComap Z f` is a sub-bundle of the pullback in the naive
sense: its total space maps to the total space of `Z` by `⟨x, v⟩ ↦ ⟨f x, v⟩`, and this map sends
the complement of the zero section to the complement of the zero section.  This module records the
continuity of that total-space map (`Work.Thom.continuous_totalSpaceMap`) and deduces the existence
of the corresponding map of the punctured (zero-complement) total spaces asked for by
`Work.Thom.exists_punctMap`.

The proof of continuity is local: in the trivialisation `Z.localTriv i` of the source bundle the
map is `φ ∘ (local trivialisation)` followed by the inverse of the trivialisation of the target
bundle, where `φ` is the evident map `B' × F → B × F`; a comparison of the coordinate formulae
makes this precise.
-/

namespace Work.Thom

open Bundle

noncomputable section

variable {B B' F : Type} [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-- **The total-space map of a bundle morphism over `f`.**  If the gluing data `Z₁` over `B'` is
`Z₂` pulled back along `f` (as witnessed by the base sets and the coordinate changes), then the map
`⟨x, v⟩ ↦ ⟨f x, v⟩` on total spaces is continuous. -/
theorem continuous_totalSpaceMap (Z₁ : VectorBundleCore ℝ B' F ι) (Z₂ : VectorBundleCore ℝ B F ι)
    (f : C(B', B))
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
    exact Prod.ext rfl (congrArg (fun (L : F →L[ℝ] F) => L p.2) (hcoord p.1 i).symm)
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

theorem exists_punctMap {m : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B)) :
    ∃ F : C(↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Thom.bundleComap Z f))),
            ↥(Work.Thom.zeroComplement (Work.Thom.realification Z))),
      ∀ p : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Thom.bundleComap Z f))),
        (F p).1 = (⟨f p.1.1, p.1.2⟩ : (Work.Thom.realification Z).TotalSpace) := by
  have hbase : ∀ i : ι, (realification (bundleComap Z f)).baseSet i
      = f ⁻¹' (realification Z).baseSet i := by
    intro i
    rw [realification_baseSet, realification_baseSet, bundleComap_baseSet]
  have hcoord : ∀ (x : B') (i : ι),
      (realification (bundleComap Z f)).coordChange
          ((realification (bundleComap Z f)).indexAt x) i x
        = (realification Z).coordChange ((realification Z).indexAt (f x)) i (f x) := by
    intro x i
    ext v
    simp only [realification_coordChange, realification_indexAt,
      bundleComap_coordChange, bundleComap_indexAt]
  have hg : Continuous (fun p : (realification (bundleComap Z f)).TotalSpace =>
      (⟨f p.1, p.2⟩ : (realification Z).TotalSpace)) :=
    continuous_totalSpaceMap _ _ f hbase hcoord
  have hmem : ∀ q : ↥(zeroComplement (realification (bundleComap Z f))),
      (⟨f q.1.1, q.1.2⟩ : (realification Z).TotalSpace)
        ∈ zeroComplement (realification Z) := by
    intro q
    exact q.2
  refine ⟨⟨fun q => ⟨(⟨f q.1.1, q.1.2⟩ : (realification Z).TotalSpace), hmem q⟩, ?_⟩, ?_⟩
  · exact (hg.comp continuous_subtype_val).subtype_mk hmem
  · intro q
    rfl

end

end Work.Thom
