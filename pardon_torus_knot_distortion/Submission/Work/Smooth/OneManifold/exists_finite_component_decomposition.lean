import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic

/-!
# Finite decomposition of a compact, locally Euclidean subset of `ℝ³` into components

A compact subset `Z ⊆ ℝ³` which is locally Euclidean of dimension one (every point has a
neighbourhood in `Z` homeomorphic to `ℝ`) is the disjoint union of *finitely many* connected
components, each of which is compact, preconnected and again locally Euclidean.

The finiteness is the only non-formal input: the arc charts give an open cover of `Z` by
preconnected sets, whose connectedness makes every connected component open, and compactness
reduces that cover to a finite one; the connected components of the points of that finite cover
then exhaust all connected components.

## Main result

* `Work.Smooth.OneManifold.exists_finite_component_decomposition`
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-- **The chart neighbourhood of a point is preconnected.**

An arc chart at `x : ↥Z` provides a homeomorphism `ℝ ≃ₜ c.V` onto the chart neighbourhood; a
homeomorphic copy of `ℝ` is connected, and `c.V` is the image of `↥c.V` under the embedding
`Subtype.val`. -/
lemma isPreconnected_chartV {Z : Set R3} (hloc : IsLocallyEuclidean Z) (x : ↥Z) :
    IsPreconnected (Work.Smooth.SphereJordan.chartOf hloc x).V := by
  obtain ⟨c, hc⟩ : ∃ c : Work.Smooth.SphereJordan.ArcChart ↥Z x,
      c = Work.Smooth.SphereJordan.chartOf hloc x := ⟨_, rfl⟩
  haveI : ConnectedSpace ↥(c.V) := c.homeo.surjective.connectedSpace c.homeo.continuous
  have h2 : IsPreconnected (Set.univ : Set ↥(c.V)) := isPreconnected_univ
  have h3 : IsPreconnected ((Subtype.val : ↥(c.V) → ↥Z) '' (Set.univ : Set ↥(c.V))) :=
    (Topology.IsInducing.isPreconnected_image (f := (Subtype.val : ↥(c.V) → ↥Z))
      Topology.IsInducing.subtypeVal).mpr h2
  rw [hc] at h3
  simpa using h3

/-- **Every connected component of a locally Euclidean set is open**: the chart neighbourhood of
any of its points is a preconnected open neighbourhood of that point, hence lies in the same
connected component. -/
lemma isOpen_connectedComponent_of_isLocallyEuclidean {Z : Set R3}
    (hloc : IsLocallyEuclidean Z) (x : ↥Z) : IsOpen (connectedComponent x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  refine Filter.mem_of_superset
    ((Work.Smooth.SphereJordan.chartOf hloc y).isOpen_V.mem_nhds
      (Work.Smooth.SphereJordan.chartOf hloc y).mem_V) ?_
  intro w hw
  rw [connectedComponent_eq hy]
  exact (isPreconnected_chartV hloc y).subset_connectedComponent
    (Work.Smooth.SphereJordan.chartOf hloc y).mem_V hw

theorem exists_finite_component_decomposition {Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hcomp : IsCompact Z) (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean Z) :
    ∃ (n : ℕ) (C : Fin n → Set LeanEval.KnotTheory.PardonDistortion.R3),
      (∀ i, C i ⊆ Z) ∧ (∀ i, (C i).Nonempty) ∧ (∀ i, IsPreconnected (C i)) ∧
      (∀ i, IsCompact (C i)) ∧ (∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean (C i)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧ Z = ⋃ i, C i := by
  classical
  haveI : CompactSpace ↥Z := isCompact_iff_compactSpace.mp hcomp
  -- The arc chart neighbourhoods of the points of `Z`.
  let V : ↥Z → Set ↥Z := fun x => (Work.Smooth.SphereJordan.chartOf hloc x).V
  have hVopen : ∀ x, IsOpen (V x) :=
    fun x => (Work.Smooth.SphereJordan.chartOf hloc x).isOpen_V
  have hVmem : ∀ x, x ∈ V x :=
    fun x => (Work.Smooth.SphereJordan.chartOf hloc x).mem_V
  have hVpre : ∀ x, IsPreconnected (V x) := fun x => isPreconnected_chartV hloc x
  have hcover : (Set.univ : Set ↥Z) ⊆ ⋃ x, V x :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hVmem x⟩
  -- Compactness reduces the chart cover to a finite one.
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ V hVopen hcover
  -- The connected components of the points of that finite cover are all connected components.
  let S : Finset (Set ↥Z) := t.image (fun x => connectedComponent x)
  have hS : (↑S : Set (Set ↥Z)) = Set.range (fun x : ↥Z => connectedComponent x) := by
    apply Set.Subset.antisymm
    · intro s hs
      rw [Finset.mem_coe] at hs
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨x, rfl⟩
    · rintro s ⟨y, rfl⟩
      rw [Finset.mem_coe, Finset.mem_image]
      have hy : y ∈ ⋃ x ∈ (t : Set ↥Z), V x := ht (Set.mem_univ y)
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hxt, hyV⟩ := Set.mem_iUnion.mp hx
      have hycx : y ∈ connectedComponent x :=
        (hVpre x).subset_connectedComponent (hVmem x) hyV
      exact ⟨x, hxt, connectedComponent_eq hycx⟩
  -- Enumerate the (finitely many) connected components.
  let e : ↥S ≃ Fin S.card := Finset.equivFin S
  let D : Fin S.card → Set ↥Z := fun k => (e.symm k : ↥S).val
  have hDrange : Set.range D = (↑S : Set (Set ↥Z)) := by
    rw [show D = (Subtype.val : ↥S → Set ↥Z) ∘ e.symm from rfl, Set.range_comp,
      Set.range_eq_univ.mpr e.symm.surjective]
    exact Subtype.coe_image_univ (S : Set (Set ↥Z))
  have hDinj : Function.Injective D := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hDcomp : ∀ k, ∃ z : ↥Z, D k = connectedComponent z := by
    intro k
    have hk : D k ∈ Set.range (fun x : ↥Z => connectedComponent x) := by
      rw [← hS]
      exact (e.symm k).2
    obtain ⟨z, hz⟩ := hk
    exact ⟨z, hz.symm⟩
  have hDopen : ∀ k, IsOpen (D k) := by
    intro k
    obtain ⟨z, hz⟩ := hDcomp k
    rw [hz]
    exact isOpen_connectedComponent_of_isLocallyEuclidean hloc z
  have hDcompact : ∀ k, IsCompact (D k) := by
    intro k
    obtain ⟨z, hz⟩ := hDcomp k
    rw [hz]
    exact IsCompact.of_isClosed_subset isCompact_univ isClosed_connectedComponent
      (subset_univ _)
  refine ⟨S.card, fun k => (Subtype.val : ↥Z → R3) '' D k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k y hy
    obtain ⟨x, -, rfl⟩ := hy
    exact x.2
  · intro k
    dsimp only
    obtain ⟨z, hz⟩ := hDcomp k
    rw [hz]
    exact ⟨(z : R3), z, mem_connectedComponent, rfl⟩
  · intro k
    dsimp only
    obtain ⟨z, hz⟩ := hDcomp k
    rw [hz]
    exact (isPreconnected_connectedComponent (x := z)).image (Subtype.val : ↥Z → R3)
      continuous_subtype_val.continuousOn
  · intro k
    dsimp only
    exact (hDcompact k).image (f := (Subtype.val : ↥Z → R3)) continuous_subtype_val
  · intro k
    dsimp only
    refine IsLocallyEuclidean.of_isOpenIn ?_ ?_ hloc
    · intro y hy
      obtain ⟨x, -, rfl⟩ := hy
      exact x.2
    · show IsOpen (Subtype.val ⁻¹' ((Subtype.val : ↥Z → R3) '' D k) : Set ↥Z)
      have heq : Subtype.val ⁻¹' ((Subtype.val : ↥Z → R3) '' D k) = D k := by
        ext x
        constructor
        · rintro ⟨y, hy, hxy⟩
          rwa [Subtype.val_injective hxy] at hy
        · exact fun hx => ⟨x, hx, rfl⟩
      rw [heq]
      exact hDopen k
  · intro k k' hkk'
    dsimp only
    have hne : D k ≠ D k' := fun h => hkk' (hDinj h)
    obtain ⟨z, hz⟩ := hDcomp k
    obtain ⟨z', hz'⟩ := hDcomp k'
    have hne' : connectedComponent z ≠ connectedComponent z' := by
      rw [← hz, ← hz']; exact hne
    have hdisj : Disjoint (connectedComponent z) (connectedComponent z') :=
      connectedComponent_disjoint hne'
    rw [hz, hz']
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, hba⟩ := hy'
    have hab : b = a := Subtype.val_injective hba
    exact (Set.disjoint_left.mp hdisj) ha (hab ▸ hb)
  · rw [eq_comm]
    have hUi : (⋃ k : Fin S.card, D k) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      have hzS : connectedComponent z ∈ (↑S : Set (Set ↥Z)) := by
        rw [hS]; exact ⟨z, rfl⟩
      rw [← hDrange] at hzS
      obtain ⟨k, hk⟩ := hzS
      exact Set.mem_iUnion.mpr ⟨k, hk.symm ▸ mem_connectedComponent⟩
    rw [← Set.image_iUnion, hUi, Subtype.coe_image_univ]

end

end Work.Smooth.OneManifold
