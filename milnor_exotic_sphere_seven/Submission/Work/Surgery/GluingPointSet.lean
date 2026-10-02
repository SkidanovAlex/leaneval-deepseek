import Submission.Work.Surgery.Gluing
import Submission.Work.Surgery.BoundaryManifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Point-set properties of gluing along a boundary

`Submission/Work/Surgery/Gluing.lean` defines the glued space `M ∪_φ N` as the quotient of
`M ⊕ N` by the identification of `x ∈ ∂M` with `φ x ∈ ∂N`.  This file proves the point-set facts
about that quotient which the smooth-structure theorem (`GluingSmooth.lean`) consumes:

* `Work.Surgery.isEmbedding_ιM`, `Work.Surgery.isEmbedding_ιN` — the two inclusions are
  topological **embeddings**; their images are the two closed halves of the glued space;
* `Work.Surgery.GlueData.isOpenMap_interior_ιM`, `GlueData.isOpenMap_interior_ιN` — the inclusions
  are open maps on the *interiors*: only the interior points of a half have neighbourhoods lying in
  that half (the double of the half-line is the line, whose closed half-lines are not open).

## The one geometric input

Both statements reduce to the elementary fact about the *closed* subspace `∂X ⊆ X` of a manifold
with boundary: a subset of the boundary which is open in the boundary can be *thickened* to an open
subset of `X` with the same trace on the boundary (`Work.Surgery.exists_isOpen_inter_boundary`, which
is the definition of the subspace topology).  This makes the `φ`-compatible open subsets of `M ⊕ N`
whose images in the quotient are neighbourhoods of the seam explicit
(`GlueData.preimage_image_eq`).
-/

open scoped Manifold Topology ContDiff
open Function Set

namespace Work.Surgery

noncomputable section

variable {n : ℕ}

/-- **Thickening a relatively open subset of the boundary.**  If `s ⊆ ∂X` (a subset of the boundary
as a subspace) is open, there is an open subset `V ⊆ X` whose trace on `∂X` is exactly `s`. -/
theorem exists_isOpen_inter_boundary {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    (s : Set ((halfModel (n + 1)).boundary X)) (hs : IsOpen s) :
    ∃ V : Set X, IsOpen V ∧
      ∀ y : Set.Elem ((halfModel (n + 1)).boundary X), y.1 ∈ V ↔ y ∈ s := by
  obtain ⟨V, hV, hVs⟩ := isOpen_induced_iff.mp hs
  exact ⟨V, hV, fun y => Set.ext_iff.mp hVs y⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]

namespace GlueData

/-- **The saturated sets of the gluing relation.**  If `V ⊆ N` is open with the same trace on `∂N`
as the image under `φ` of the boundary part of an open `U ⊆ M`, then `U ⊔ V` is a *saturated* open
subset of `M ⊕ N`: its image in the glued space is an open neighbourhood of the seam. -/
theorem preimage_image_eq (D : GlueData n M N) {U : Set M} {V : Set N}
    (hUV : ∀ x : Set.Elem ((halfModel (n + 1)).boundary M), x.1 ∈ U → (D.φ x).1 ∈ V)
    (hVU : ∀ y : Set.Elem ((halfModel (n + 1)).boundary N), y.1 ∈ V →
      ∃ x : Set.Elem ((halfModel (n + 1)).boundary M), x.1 ∈ U ∧ (D.φ x).1 = y.1) :
    D.q ⁻¹' (D.q '' (Sum.inl '' U ∪ Sum.inr '' V)) = Sum.inl '' U ∪ Sum.inr '' V := by
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    rcases hb with ⟨u, huU, rfl⟩ | ⟨v, hvV, rfl⟩
    · rcases a with x | y
      · exact Or.inl ⟨x, D.ιM_injective hba ▸ huU, rfl⟩
      · obtain ⟨p, hp, hpv⟩ := D.ιM_eq_ιN_iff.mp hba
        exact Or.inr ⟨y, hpv ▸ hUV p (hp ▸ huU), rfl⟩
    · rcases a with x | y
      · obtain ⟨p, hpx, hpv⟩ := D.ιM_eq_ιN_iff.mp hba.symm
        obtain ⟨p', hp'U, hp'v⟩ := hVU ⟨(D.φ p).1, (D.φ p).2⟩ (hpv ▸ hvV)
        have hpp' : p' = p := D.φ.injective (Subtype.ext hp'v)
        exact Or.inl ⟨x, by rw [hpx]; exact hpp' ▸ hp'U, rfl⟩
      · exact Or.inr ⟨y, D.ιN_injective hba ▸ hvV, rfl⟩
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The image under `ιM` of a subset of the *interior* of `M` has the first summand as preimage:
interior points of `M` are not identified with anything. -/
theorem preimage_image_interior_ιM (D : GlueData n M N)
    (W : Set (Set.Elem ((halfModel (n + 1)).boundary M)ᶜ)) :
    D.q ⁻¹' (D.ιM '' (Subtype.val '' W)) = Sum.inl '' (Subtype.val '' W) := by
  have h := D.preimage_image_eq (U := Subtype.val '' W) (V := ∅)
    (by rintro x ⟨w, hw, hwx⟩; exact (w.2 (hwx ▸ x.2)).elim)
    (by intro y hy; exact absurd hy (Set.notMem_empty y))
  have key : D.q '' (Sum.inl '' (Subtype.val '' W)) = D.ιM '' (Subtype.val '' W) := by
    rw [GlueData.ιM, Set.image_comp]
  rw [← key]
  simpa only [Set.union_empty, Set.image_empty] using h

/-- The image under `ιN` of a subset of the *interior* of `N` has the second summand as preimage. -/
theorem preimage_image_interior_ιN (D : GlueData n M N)
    (W : Set (Set.Elem ((halfModel (n + 1)).boundary N)ᶜ)) :
    D.q ⁻¹' (D.ιN '' (Subtype.val '' W)) = Sum.inr '' (Subtype.val '' W) := by
  have h := D.preimage_image_eq (U := ∅) (V := Subtype.val '' W)
    (by intro x hx; exact absurd hx (Set.notMem_empty x))
    (by rintro y ⟨w, hw, hwy⟩; exact (w.2 (hwy ▸ y.2)).elim)
  have key : D.q '' (Sum.inr '' (Subtype.val '' W)) = D.ιN '' (Subtype.val '' W) := by
    rw [GlueData.ιN, Set.image_comp]
  rw [← key]
  simpa only [Set.empty_union, Set.image_empty] using h

/-- **The inclusion `ιM` is an open map on the interior**: it maps `M ∖ ∂M` onto an open subset of
the glued space. -/
theorem isOpenMap_interior_ιM (D : GlueData n M N)
    [IsManifold (halfModel (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] :
    IsOpenMap fun x : Set.Elem ((halfModel (n + 1)).boundary M)ᶜ => D.ιM x.1 := by
  intro W hW
  have hcompl : IsOpen (((halfModel (n + 1)).boundary M)ᶜ) :=
    (isClosed_bnd (n := n + 1) (M := M)).isOpen_compl
  have himg : (fun x : Set.Elem ((halfModel (n + 1)).boundary M)ᶜ => D.ιM x.1) '' W
      = D.ιM '' (Subtype.val '' W) :=
    Set.image_comp D.ιM (Subtype.val : Set.Elem ((halfModel (n + 1)).boundary M)ᶜ → M) W
  have hopen : IsOpen ((Sum.inl : M → M ⊕ N) ''
      ((Subtype.val : Set.Elem ((halfModel (n + 1)).boundary M)ᶜ → M) '' W)) := by
    have h1 : IsOpenMap (Subtype.val : Set.Elem ((halfModel (n + 1)).boundary M)ᶜ → M) :=
      IsOpen.isOpenMap_subtype_val hcompl
    have h2 : IsOpenMap (Sum.inl : M → M ⊕ N) :=
      (Topology.IsOpenEmbedding.inl (X := M) (Y := N)).isOpenMap
    have h3 := h2.comp h1 W hW
    rwa [Set.image_comp] at h3
  rw [isOpen_coinduced, himg]
  change IsOpen (D.q ⁻¹' (D.ιM '' (Subtype.val '' W)))
  rw [D.preimage_image_interior_ιM W]
  exact hopen

/-- The same for `ιN`. -/
theorem isOpenMap_interior_ιN (D : GlueData n M N)
    [IsManifold (halfModel (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) N] :
    IsOpenMap fun y : Set.Elem ((halfModel (n + 1)).boundary N)ᶜ => D.ιN y.1 := by
  intro W hW
  have hcompl : IsOpen (((halfModel (n + 1)).boundary N)ᶜ) :=
    (isClosed_bnd (n := n + 1) (M := N)).isOpen_compl
  have himg : (fun y : Set.Elem ((halfModel (n + 1)).boundary N)ᶜ => D.ιN y.1) '' W
      = D.ιN '' (Subtype.val '' W) :=
    Set.image_comp D.ιN (Subtype.val : Set.Elem ((halfModel (n + 1)).boundary N)ᶜ → N) W
  have hopen : IsOpen ((Sum.inr : N → M ⊕ N) ''
      ((Subtype.val : Set.Elem ((halfModel (n + 1)).boundary N)ᶜ → N) '' W)) := by
    have h1 : IsOpenMap (Subtype.val : Set.Elem ((halfModel (n + 1)).boundary N)ᶜ → N) :=
      IsOpen.isOpenMap_subtype_val hcompl
    have h2 : IsOpenMap (Sum.inr : N → M ⊕ N) :=
      (Topology.IsOpenEmbedding.inr (X := M) (Y := N)).isOpenMap
    have h3 := h2.comp h1 W hW
    rwa [Set.image_comp] at h3
  rw [isOpen_coinduced, himg]
  change IsOpen (D.q ⁻¹' (D.ιN '' (Subtype.val '' W)))
  rw [D.preimage_image_interior_ιN W]
  exact hopen

end GlueData

/-- **The inclusion of a half into its gluing along the boundary is an embedding.** -/
theorem isEmbedding_ιM (D : GlueData n M N) :
    @Topology.IsEmbedding M D.Glued _ _ D.ιM := by
  refine ⟨⟨TopologicalSpace.ext_iff.mpr fun U => ?_⟩, D.ιM_injective⟩
  rw [isOpen_induced_iff]
  constructor
  · intro hU
    obtain ⟨VN, hVN, hVNkey⟩ :=
      exists_isOpen_inter_boundary (n := n) (X := N)
        (D.φ '' ((↑) ⁻¹' U)) (D.φ.isOpenMap _ (hU.preimage continuous_subtype_val))
    have hUV : ∀ x : Set.Elem ((halfModel (n + 1)).boundary M), x.1 ∈ U → (D.φ x).1 ∈ VN := by
      intro x hx
      exact (hVNkey (D.φ x)).mpr ⟨x, hx, rfl⟩
    have hVU : ∀ y : Set.Elem ((halfModel (n + 1)).boundary N), y.1 ∈ VN →
        ∃ x : Set.Elem ((halfModel (n + 1)).boundary M), x.1 ∈ U ∧ (D.φ x).1 = y.1 := by
      intro y hy
      obtain ⟨p, hp, hpy⟩ := (hVNkey y).mp hy
      exact ⟨p, hp, congrArg Subtype.val hpy⟩
    have hWopen : IsOpen (Sum.inl '' U ∪ Sum.inr '' VN : Set (M ⊕ N)) :=
      (Topology.IsOpenEmbedding.inl.isOpenMap U hU).union
        (Topology.IsOpenEmbedding.inr.isOpenMap VN hVN)
    refine ⟨D.q '' (Sum.inl '' U ∪ Sum.inr '' VN), ?_, ?_⟩
    · rw [isOpen_coinduced]
      change IsOpen (D.q ⁻¹' (D.q '' (Sum.inl '' U ∪ Sum.inr '' VN)))
      rw [D.preimage_image_eq hUV hVU]
      exact hWopen
    · ext x
      constructor
      · rintro ⟨a, ha, hqa⟩
        rcases ha with ⟨u, huU, rfl⟩ | ⟨v, hvV, rfl⟩
        · exact D.ιM_injective hqa ▸ huU
        · obtain ⟨p, hpx, hpv⟩ := D.ιM_eq_ιN_iff.mp hqa.symm
          obtain ⟨p', hp'U, hp'v⟩ := hVU ⟨(D.φ p).1, (D.φ p).2⟩ (hpv ▸ hvV)
          have hpp' : p' = p := D.φ.injective (Subtype.ext hp'v)
          rw [hpx]
          exact hpp' ▸ hp'U
      · intro hx
        exact ⟨Sum.inl x, Or.inl ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨V, hV, hVU⟩
    rw [← hVU]
    exact hV.preimage D.continuous_ιM

/-- The same for `ιN`. -/
theorem isEmbedding_ιN (D : GlueData n M N) :
    @Topology.IsEmbedding N D.Glued _ _ D.ιN := by
  refine ⟨⟨TopologicalSpace.ext_iff.mpr fun U => ?_⟩, D.ιN_injective⟩
  rw [isOpen_induced_iff]
  constructor
  · intro hU
    obtain ⟨VM, hVM, hVMkey⟩ :=
      exists_isOpen_inter_boundary (n := n) (X := M)
        (D.φ.symm '' ((↑) ⁻¹' U)) (D.φ.symm.isOpenMap _ (hU.preimage continuous_subtype_val))
    have hUV : ∀ x : Set.Elem ((halfModel (n + 1)).boundary M), x.1 ∈ VM → (D.φ x).1 ∈ U := by
      intro x hx
      obtain ⟨q, hq, hqx⟩ := (hVMkey x).mp hx
      rw [← hqx, congrArg Subtype.val (D.φ.apply_symm_apply q)]
      exact hq
    have hVU : ∀ y : Set.Elem ((halfModel (n + 1)).boundary N), y.1 ∈ U →
        ∃ x : Set.Elem ((halfModel (n + 1)).boundary M), x.1 ∈ VM ∧ (D.φ x).1 = y.1 := by
      intro y hy
      refine ⟨D.φ.symm y, ?_, congrArg Subtype.val (D.φ.apply_symm_apply y)⟩
      exact (hVMkey (D.φ.symm y)).mpr ⟨y, hy, rfl⟩
    have hWopen : IsOpen (Sum.inl '' VM ∪ Sum.inr '' U : Set (M ⊕ N)) :=
      (Topology.IsOpenEmbedding.inl.isOpenMap VM hVM).union
        (Topology.IsOpenEmbedding.inr.isOpenMap U hU)
    refine ⟨D.q '' (Sum.inl '' VM ∪ Sum.inr '' U), ?_, ?_⟩
    · rw [isOpen_coinduced]
      change IsOpen (D.q ⁻¹' (D.q '' (Sum.inl '' VM ∪ Sum.inr '' U)))
      rw [D.preimage_image_eq hUV hVU]
      exact hWopen
    · ext y
      constructor
      · rintro ⟨a, ha, hqa⟩
        rcases ha with ⟨x, hxV, rfl⟩ | ⟨v, hvU, rfl⟩
        · obtain ⟨q, hqx, hqy⟩ := D.ιM_eq_ιN_iff.mp hqa
          rw [hqy]
          exact hUV q (hqx ▸ hxV)
        · exact D.ιN_injective hqa ▸ hvU
      · intro hy
        exact ⟨Sum.inr y, Or.inr ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨V, hV, hVU⟩
    rw [← hVU]
    exact hV.preimage D.continuous_ιN

end

end Work.Surgery
