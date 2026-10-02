import Submission.EFL.Matching
import Submission.EFL.LargeEdge
import Mathlib.Data.Set.Card

/-!
# Combining two edge-colourings with disjoint colour sets

Theorem 6.1 of the paper colours the medium edges (`𝓗_med`, Proposition 6.10)
and the large edges (`𝓗_large`, Proposition 6.9) with *disjoint* colour sets
and then reads off the combined colouring of `𝓗_med ∪ 𝓗_large`.  The same
device is used in every case analysis of §6.2/§6 of the paper.

This module supplies the glue, in a form adapted to the `classVertices` /
`classVertexCount` bookkeeping of `LargeEdge.lean`:

* `coloringUnionOfCover` — the combined colouring of a cover `𝓖₁ ∪ 𝓖₂ = 𝓗`
  (with `𝓖₁, 𝓖₂` disjoint) obtained from `φ₁ : 𝓖₁.Coloring (Fin n)` and
  `φ₂ : 𝓖₂.Coloring (Fin n)`;
* `coloringUnionOfCover_usesColourSet` — it uses `C₁ ∪ C₂` when `φ₁` uses `C₁`
  and `φ₂` uses `C₂`;
* `coloringUnionOfCover_classVertices_of_mem` /
  `..._of_notMem` — the colour classes of the combined colouring are *exactly*
  those of `φ₁` (for colours in `C₁`) and of `φ₂` (for colours outside `C₁`);
  hence the same vertex counts;
* `coloringUnionOfCover_colorClass_of_mem` — the corresponding statement for
  the edge sets themselves, which is what `SingletonClassesForHuge` needs.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The label of the edge `e` of the cover `𝓗 = 𝓖₁ ∪ 𝓖₂`: the `φ₁`-label when
`e ∈ 𝓖₁`, and the `φ₂`-label otherwise. -/
noncomputable def unionLabel {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)} (h₁ : 𝓖₁ ⊆ 𝓗) (h₂ : 𝓖₂ ⊆ 𝓗)
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂)
    (φ₁ : 𝓖₁.Coloring (Fin n)) (φ₂ : 𝓖₂.Coloring (Fin n)) (e : 𝓗) : Fin n := by
  classical
  exact if he : (e : Set (Fin n)) ∈ 𝓖₁ then φ₁.labels ⟨(e : Set (Fin n)), he⟩
    else φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩

/-- the value of `unionLabel` on the `𝓖₁`-part -/
lemma unionLabel_of_mem {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)} {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗}
    {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)} {e : 𝓗}
    (he : (e : Set (Fin n)) ∈ 𝓖₁) :
    unionLabel h₁ h₂ hcover φ₁ φ₂ e = φ₁.labels ⟨(e : Set (Fin n)), he⟩ := by
  classical
  unfold unionLabel
  exact dif_pos he

/-- the value of `unionLabel` off the `𝓖₁`-part -/
lemma unionLabel_of_notMem {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)} {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗}
    {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)} {e : 𝓗}
    (he : (e : Set (Fin n)) ∉ 𝓖₁) :
    unionLabel h₁ h₂ hcover φ₁ φ₂ e =
      φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩ := by
  classical
  unfold unionLabel
  exact dif_neg he

/-- **Combining two colourings of a cover with disjoint colour sets.**  If
`𝓖₁ ∪ 𝓖₂ = 𝓗` and `𝓖₁ ∩ 𝓖₂ = ∅` (the `Disjoint` hypothesis), the colourings
`φ₁` of `𝓖₁` and `φ₂` of `𝓖₂` whose colour sets `C₁`, `C₂` are disjoint
combine into a colouring of `𝓗`. -/
def coloringUnionOfCover {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    (h₁ : 𝓖₁ ⊆ 𝓗) (h₂ : 𝓖₂ ⊆ 𝓗)
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂)
    (hdisjG : Disjoint 𝓖₁ 𝓖₂)
    {C₁ C₂ : Finset (Fin n)} (hdisj : Disjoint C₁ C₂)
    (φ₁ : 𝓖₁.Coloring (Fin n)) (φ₂ : 𝓖₂.Coloring (Fin n))
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂) :
    𝓗.Coloring (Fin n) where
  labels := unionLabel h₁ h₂ hcover φ₁ φ₂
  isColoring e₁ e₂ hne hnon := by
    intro hcol
    by_cases h1 : (e₁ : Set (Fin n)) ∈ 𝓖₁
    · by_cases h2 : (e₂ : Set (Fin n)) ∈ 𝓖₁
      · rw [unionLabel_of_mem h1, unionLabel_of_mem h2] at hcol
        exact φ₁.isColoring ⟨_, h1⟩ ⟨_, h2⟩
          (fun hEq => hne (Subtype.ext (by simpa using congrArg Subtype.val hEq)))
          (by simpa using hnon) hcol
      · rw [unionLabel_of_mem h1, unionLabel_of_notMem h2] at hcol
        have hmem₂ : φ₁.labels ⟨(e₁ : Set (Fin n)), h1⟩ ∈ C₂ := by
          rw [hcol]; exact hφ₂ _
        exact Finset.disjoint_left.mp hdisj (hφ₁ _) hmem₂
    · by_cases h2 : (e₂ : Set (Fin n)) ∈ 𝓖₁
      · rw [unionLabel_of_notMem h1, unionLabel_of_mem h2] at hcol
        have hmem₂ : φ₁.labels ⟨(e₂ : Set (Fin n)), h2⟩ ∈ C₂ := by
          rw [← hcol]; exact hφ₂ _
        exact Finset.disjoint_left.mp hdisj (hφ₁ _) hmem₂
      · rw [unionLabel_of_notMem h1, unionLabel_of_notMem h2] at hcol
        exact φ₂.isColoring ⟨_, _⟩ ⟨_, _⟩
          (fun hEq => hne (Subtype.ext (by simpa using congrArg Subtype.val hEq)))
          (by simpa using hnon) hcol

/-- the combined colouring uses the union of the two colour sets -/
theorem coloringUnionOfCover_usesColourSet {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂) :
    (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).UsesColourSet
      (C₁ ∪ C₂) := by
  intro e
  by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
  · have hmem : (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).labels e
        = unionLabel h₁ h₂ hcover φ₁ φ₂ e := rfl
    rw [hmem, unionLabel_of_mem he]
    exact Finset.mem_union_left _ (hφ₁ _)
  · have hmem : (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).labels e
        = unionLabel h₁ h₂ hcover φ₁ φ₂ e := rfl
    rw [hmem, unionLabel_of_notMem he]
    exact Finset.mem_union_right _ (hφ₂ _)

/-- **Membership in a colour class of the combined colouring, for a colour of
the first part**: an edge of `𝓗` is coloured `c` (with `c ∈ C₁`) exactly when
it lies in `𝓖₁` and `φ₁` colours it `c`. -/
theorem mem_colorClass_coloringUnionOfCover_left {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∈ C₁) (e : 𝓗) :
    e ∈ (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c ↔
      ∃ he : (e : Set (Fin n)) ∈ 𝓖₁, (⟨(e : Set (Fin n)), he⟩ : 𝓖₁) ∈ φ₁.colorClass c := by
  have hlab : (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).labels e
      = unionLabel h₁ h₂ hcover φ₁ φ₂ e := rfl
  rw [mem_colorClass, hlab]
  constructor
  · intro hcol
    by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
    · refine ⟨he, ?_⟩
      rw [unionLabel_of_mem he] at hcol
      simpa [mem_colorClass] using hcol
    · exfalso
      rw [unionLabel_of_notMem he] at hcol
      have hmem : c ∈ C₂ := hcol ▸ hφ₂ _
      exact Finset.disjoint_left.mp hdisj hc hmem
  · rintro ⟨he, hcl⟩
    rw [unionLabel_of_mem he]
    exact hcl

/-- **Membership in a colour class of the combined colouring, for a colour
outside `C₁`**: an edge of `𝓗` is coloured `c` exactly when it lies in `𝓖₂`
and `φ₂` colours it `c`. -/
theorem mem_colorClass_coloringUnionOfCover_right {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∉ C₁) (e : 𝓗) :
    e ∈ (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c ↔
      ∃ he : (e : Set (Fin n)) ∈ 𝓖₂, (⟨(e : Set (Fin n)), he⟩ : 𝓖₂) ∈ φ₂.colorClass c := by
  have hlab : (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).labels e
      = unionLabel h₁ h₂ hcover φ₁ φ₂ e := rfl
  rw [mem_colorClass, hlab]
  constructor
  · intro hcol
    have he : (e : Set (Fin n)) ∉ 𝓖₁ := by
      intro hmem
      have hEq : φ₁.labels ⟨(e : Set (Fin n)), hmem⟩ = c := by
        rw [← unionLabel_of_mem hmem]; exact hcol
      exact hc (hEq ▸ hφ₁ _)
    have hmem₂ : (e : Set (Fin n)) ∈ 𝓖₂ :=
      (hcover (e : Set (Fin n)) e.2).resolve_left he
    refine ⟨hmem₂, ?_⟩
    rw [unionLabel_of_notMem he] at hcol
    simpa [mem_colorClass] using hcol
  · rintro ⟨he, hcl⟩
    have hnot : (e : Set (Fin n)) ∉ 𝓖₁ := fun hmem => (Set.disjoint_left.mp hdisjG) hmem he
    rw [unionLabel_of_notMem hnot]
    exact hcl

/-- The vertices incident with a colour class are the same for the combined
colouring (at a colour of `C₁`) and for `φ₁`. -/
theorem classVertices_coloringUnionOfCover_left {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∈ C₁) :
    (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).classVertices c =
      φ₁.classVertices c := by
  ext v
  rw [mem_classVertices, mem_classVertices]
  constructor
  · rintro ⟨e, hcl, hv⟩
    obtain ⟨he, hcl₁⟩ := (mem_colorClass_coloringUnionOfCover_left hφ₁ hφ₂ hc e).mp hcl
    exact ⟨⟨(e : Set (Fin n)), he⟩, hcl₁, hv⟩
  · rintro ⟨e, hcl, hv⟩
    exact ⟨⟨(e : Set (Fin n)), h₁ e.2⟩,
      (mem_colorClass_coloringUnionOfCover_left hφ₁ hφ₂ hc _).mpr ⟨e.2, hcl⟩, hv⟩

/-- The vertices incident with a colour class are the same for the combined
colouring (at a colour outside `C₁`) and for `φ₂`. -/
theorem classVertices_coloringUnionOfCover_right {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∉ C₁) :
    (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).classVertices c =
      φ₂.classVertices c := by
  ext v
  rw [mem_classVertices, mem_classVertices]
  constructor
  · rintro ⟨e, hcl, hv⟩
    obtain ⟨he, hcl₂⟩ := (mem_colorClass_coloringUnionOfCover_right hφ₁ hφ₂ hc e).mp hcl
    exact ⟨⟨(e : Set (Fin n)), he⟩, hcl₂, hv⟩
  · rintro ⟨e, hcl, hv⟩
    exact ⟨⟨(e : Set (Fin n)), h₂ e.2⟩,
      (mem_colorClass_coloringUnionOfCover_right hφ₁ hφ₂ hc _).mpr ⟨e.2, hcl⟩, hv⟩

/-- The colour classes of the combined colouring, at colours of `C₁`, are the
images of the colour classes of `φ₁`. -/
theorem colorClass_coloringUnionOfCover_left {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∈ C₁) {e₀ : 𝓖₁}
    (hcl : φ₁.colorClass c = {e₀}) :
    (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c =
      {⟨(e₀ : Set (Fin n)), h₁ e₀.2⟩} := by
  ext e
  rw [mem_colorClass_coloringUnionOfCover_left hφ₁ hφ₂ hc e, hcl, Set.mem_singleton_iff]
  constructor
  · rintro ⟨he, hEq⟩
    have hv : ((⟨(e : Set (Fin n)), he⟩ : 𝓖₁) : Set (Fin n)) = (e₀ : Set (Fin n)) := by
      simpa using congrArg (fun x : 𝓖₁ => (x : Set (Fin n))) hEq
    exact Subtype.ext hv
  · rintro rfl
    exact ⟨e₀.2, rfl⟩

end

end ErdosFaberLovaszConjecture
