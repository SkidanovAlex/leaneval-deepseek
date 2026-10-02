import Submission.EFL.ColourUnion
import Submission.EFL.AlphaBoundedColouring
import Submission.EFL.LargeEdgeCase1

/-!
# Relabelling colourings and combining colourings with a cross-condition

Two tools used in the Case-2 analysis of Theorem 6.1.

* `Hypergraph.Coloring.map`: relabel a colouring along an injective map of
  colour hosts; `exists_coloring_usesColourSet` packages the special case of
  moving a colouring into a *prescribed* colour set `D` (of at least the
  original number of colours), preserving `AlphaBounded`.
* `coloringUnionCross`: two colourings of a disjoint cover combine into a
  proper colouring whenever the *cross-condition* holds (no colour is used by
  both parts on intersecting edges).  Unlike `coloringUnionOfCover` the colour
  sets need not be disjoint; the price is that a colour class of the combined
  colouring is the union of a class of `φ₁` and a class of `φ₂`.

Also `classVertexCount_union_le` (the covered-vertex count of a combined class
is at most the sum of the parts') and `classVertexCount_le_of_alphaBounded`
(a class of a `γ`-bounded colouring whose edges all have size `≤ M` covers at
most `max (γn) M` vertices) — the two facts behind property (iii) of the
non-extremal alternative in Case 2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- Relabel the colours of a colouring along an injective map. -/
def Hypergraph.Coloring.map {𝓖 : Hypergraph (Fin n)} {α β : Type*} (φ : 𝓖.Coloring α)
    (f : α → β) (hf : Function.Injective f) : 𝓖.Coloring β where
  labels := fun e => f (φ.labels e)
  isColoring := fun e₁ e₂ hne hnon h => φ.isColoring e₁ e₂ hne hnon (hf h)

/-- The colour classes of a relabelled colouring at a colour in the range. -/
theorem Coloring.colorClass_map {𝓖 : Hypergraph (Fin n)} {α β : Type*}
    (φ : 𝓖.Coloring α) (f : α → β) (hf : Function.Injective f) (a : α) :
    (φ.map f hf).colorClass (f a) = φ.colorClass a := by
  ext e
  simp only [Hypergraph.Coloring.colorClass, Set.mem_setOf_eq, Hypergraph.Coloring.map]
  exact hf.eq_iff

/-- Relabelling preserves `α`-boundedness. -/
theorem Coloring.alphaBounded_map {𝓖 : Hypergraph (Fin n)} {α β : Type*} {γ : ℝ}
    (φ : 𝓖.Coloring α) (f : α → β) (hf : Function.Injective f) (hφ : φ.AlphaBounded γ) :
    (φ.map f hf).AlphaBounded γ := by
  intro c
  by_cases hc : ∃ a, f a = c
  · obtain ⟨a, rfl⟩ := hc
    rw [Coloring.colorClass_map]
    exact hφ a
  · left
    have hempty : (φ.map f hf).colorClass c = ∅ := by
      ext e
      constructor
      · intro h
        exact absurd ⟨φ.labels e, h⟩ hc
      · intro h
        exact absurd h (Set.notMem_empty e)
    rw [hempty, Set.ncard_empty]
    norm_num

/-- **Move a colouring into a prescribed colour set.**  A colouring with `m`
colours can be relabelled so that it uses only the colours of a given set `D`
with `m ≤ |D|`, preserving `α`-boundedness. -/
theorem exists_coloring_usesColourSet {𝓖 : Hypergraph (Fin n)} {m : ℕ} {γ : ℝ}
    (D : Finset (Fin n)) (hm : m ≤ D.card) (φ : 𝓖.Coloring (Fin m)) (hφ : φ.AlphaBounded γ) :
    ∃ ψ : 𝓖.Coloring (Fin n), ψ.UsesColourSet D ∧ ψ.AlphaBounded γ := by
  classical
  obtain ⟨t, htD, htcard⟩ := Finset.exists_subset_card_eq hm
  let σ : Fin m ≃ ↥t := (Finset.equivFinOfCardEq htcard).symm
  let f : Fin m → Fin n := fun a => ((σ a : ↥t) : Fin n)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (σ a : ↥t) = (σ b : ↥t) := Subtype.ext hab
    exact σ.injective h1
  refine ⟨φ.map f hf, fun e => ?_, Coloring.alphaBounded_map φ f hf hφ⟩
  exact htD (σ (φ.labels e)).2

/-! ## Combining colourings with a cross-condition -/

/-- The combined labelling of a disjoint cover: the `φ₁`-label on `𝓖₁`, the
`φ₂`-label off it. -/
def unionLabelCross {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)} (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂)
    (φ₁ : 𝓖₁.Coloring (Fin n)) (φ₂ : 𝓖₂.Coloring (Fin n)) (e : 𝓗) : Fin n := by
  classical
  exact if he : (e : Set (Fin n)) ∈ 𝓖₁ then φ₁.labels ⟨(e : Set (Fin n)), he⟩
    else φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩

/-- **Combining two colourings of a cover with a cross-condition.**  If `φ₁`
and `φ₂` colour a disjoint cover and never agree on intersecting edges across
the two parts, they combine into a proper colouring of the whole. -/
def coloringUnionCross {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    (h₁ : 𝓖₁ ⊆ 𝓗) (h₂ : 𝓖₂ ⊆ 𝓗)
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂) (hdisjG : Disjoint 𝓖₁ 𝓖₂)
    (φ₁ : 𝓖₁.Coloring (Fin n)) (φ₂ : 𝓖₂.Coloring (Fin n))
    (hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂) :
    𝓗.Coloring (Fin n) where
  labels := unionLabelCross hcover φ₁ φ₂
  isColoring := by
    intro e₁ e₂ hne hnon hcol
    by_cases h1 : (e₁ : Set (Fin n)) ∈ 𝓖₁
    · by_cases h2 : (e₂ : Set (Fin n)) ∈ 𝓖₁
      · have hcol1 : φ₁.labels ⟨(e₁ : Set (Fin n)), h1⟩ = φ₁.labels ⟨(e₂ : Set (Fin n)), h2⟩ := by
          simpa only [unionLabelCross, dif_pos h1, dif_pos h2] using hcol
        exact φ₁.isColoring ⟨_, h1⟩ ⟨_, h2⟩
          (fun hEq => hne (Subtype.ext (by simpa using congrArg Subtype.val hEq)))
          (by simpa using hnon) hcol1
      · have hcol1 : φ₁.labels ⟨(e₁ : Set (Fin n)), h1⟩ =
            φ₂.labels ⟨(e₂ : Set (Fin n)), (hcover (e₂ : Set (Fin n)) e₂.2).resolve_left h2⟩ := by
          simpa only [unionLabelCross, dif_pos h1, dif_neg h2] using hcol
        exact hcross ⟨(e₁ : Set (Fin n)), h1⟩
          ⟨(e₂ : Set (Fin n)), (hcover (e₂ : Set (Fin n)) e₂.2).resolve_left h2⟩
          (by simpa using hnon) hcol1
    · by_cases h2 : (e₂ : Set (Fin n)) ∈ 𝓖₁
      · have hcol1 : φ₂.labels ⟨(e₁ : Set (Fin n)), (hcover (e₁ : Set (Fin n)) e₁.2).resolve_left h1⟩ =
            φ₁.labels ⟨(e₂ : Set (Fin n)), h2⟩ := by
          simpa only [unionLabelCross, dif_neg h1, dif_pos h2] using hcol
        exact hcross ⟨(e₂ : Set (Fin n)), h2⟩
          ⟨(e₁ : Set (Fin n)), (hcover (e₁ : Set (Fin n)) e₁.2).resolve_left h1⟩
          (by simpa [Set.inter_comm] using hnon) hcol1.symm
      · have hcol1 : φ₂.labels ⟨(e₁ : Set (Fin n)), (hcover (e₁ : Set (Fin n)) e₁.2).resolve_left h1⟩ =
            φ₂.labels ⟨(e₂ : Set (Fin n)), (hcover (e₂ : Set (Fin n)) e₂.2).resolve_left h2⟩ := by
          simpa only [unionLabelCross, dif_neg h1, dif_neg h2] using hcol
        exact φ₂.isColoring ⟨_, _⟩ ⟨_, _⟩
          (fun hEq => hne (Subtype.ext (by simpa using congrArg Subtype.val hEq)))
          (by simpa using hnon) hcol1

/-- The combined colouring uses the union of the two colour sets. -/
theorem coloringUnionCross_usesColourSet {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    {hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂}
    {C₁ C₂ : Finset (Fin n)} (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂) :
    (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).UsesColourSet (C₁ ∪ C₂) := by
  intro e
  by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
  · have : (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).labels e =
        φ₁.labels ⟨(e : Set (Fin n)), he⟩ := by
      simp only [coloringUnionCross, unionLabelCross, dif_pos he]
    rw [this]
    exact Finset.mem_union_left _ (hφ₁ _)
  · have : (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).labels e =
        φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩ := by
      simp only [coloringUnionCross, unionLabelCross, dif_neg he]
    rw [this]
    exact Finset.mem_union_right _ (hφ₂ _)

/-- The vertices covered by a colour class of the combined colouring are the
union of the vertices covered by the corresponding classes of the two
colourings. -/
theorem classVertices_coloringUnionCross {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    {hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂}
    (c : Fin n) :
    (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).classVertices c =
      φ₁.classVertices c ∪ φ₂.classVertices c := by
  ext v
  constructor
  · rintro ⟨e, hcl, hv⟩
    by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
    · left
      refine ⟨⟨(e : Set (Fin n)), he⟩, ?_, hv⟩
      simpa only [coloringUnionCross, unionLabelCross, dif_pos he, mem_colorClass] using hcl
    · right
      refine ⟨⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩, ?_, hv⟩
      simpa only [coloringUnionCross, unionLabelCross, dif_neg he, mem_colorClass] using hcl
  · rintro (⟨e, hcl, hv⟩ | ⟨e, hcl, hv⟩)
    · refine ⟨⟨(e : Set (Fin n)), h₁ e.2⟩, ?_, hv⟩
      simp only [coloringUnionCross, unionLabelCross, dif_pos e.2, mem_colorClass]
      exact hcl
    · refine ⟨⟨(e : Set (Fin n)), h₂ e.2⟩, ?_, hv⟩
      simp only [coloringUnionCross, unionLabelCross, dif_neg (fun hc => (Set.disjoint_left.mp hdisjG) hc e.2),
        mem_colorClass]
      exact hcl

/-- The covered-vertex count of a combined colour class is at most the sum of
the covered-vertex counts of the two parts. -/
theorem classVertexCount_coloringUnionCross_le {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    {hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂}
    (c : Fin n) :
    (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).classVertexCount c ≤
      φ₁.classVertexCount c + φ₂.classVertexCount c := by
  rw [Hypergraph.Coloring.classVertexCount, classVertices_coloringUnionCross,
    Hypergraph.Coloring.classVertexCount, Hypergraph.Coloring.classVertexCount]
  exact Set.ncard_union_le _ _

/-- **Covered vertices of a class of a bounded colouring.**  If `φ` is
`γ`-bounded and every edge of the class of `c` has size at most `M`, then the
class covers at most `max (γn) M` vertices. -/
theorem classVertexCount_le_of_alphaBounded {𝓖 : Hypergraph (Fin n)} {γ M : ℝ}
    (φ : 𝓖.Coloring (Fin n)) (hφ : φ.AlphaBounded γ) (hγ : 0 ≤ γ * (n : ℝ)) {c : Fin n}
    (hM : ∀ e : 𝓖, e ∈ φ.colorClass c → (edgeSize (e : Set (Fin n)) : ℝ) ≤ M) :
    (φ.classVertexCount c : ℝ) ≤ max (γ * (n : ℝ)) M := by
  rcases (AlphaBounded_iff_classVertexCount γ φ).mp hφ c with h1 | h2
  · -- the class is a singleton (or empty), so it covers at most `M` vertices
    have hfin : (φ.colorClass c).Finite := Set.toFinite _
    rcases eq_empty_or_singleton_of_ncard_le_one hfin h1 with hem | ⟨e₀, hs⟩
    · have hz : φ.classVertexCount c = 0 := by
        rw [classVertexCount_eq_of_classVertices_eq φ
          (classVertices_eq_empty_of_colorClass_eq_empty φ hem)]
        simp
      rw [hz, Nat.cast_zero]
      exact le_trans hγ (le_max_left _ _)
    · have hcv : (φ.classVertexCount c : ℝ) = (edgeSize (e₀ : Set (Fin n)) : ℝ) := by
        rw [classVertexCount_eq_edgeSize_of_singleton φ hs]
      rw [hcv]
      exact le_trans (hM e₀ (hs ▸ Set.mem_singleton _)) (le_max_right _ _)
  · exact le_trans h2 (le_max_left _ _)

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **The assembly of the non-extremal alternative, from the properties of the
large-edge colouring.**  This is the version of
`largeEdge_nonExtremal_of_colourings` (Case 1) that works with the *weaker*
input produced by Case 2 of Theorem 6.1: instead of `β/5`-boundedness of the
large-edge colouring we only require that colours assigned to huge edges are
singletons and that all other colours cover at most `βn` vertices, except
(possibly) colours carrying a huge edge. -/
theorem largeEdge_nonExtremal_of_largeColouring {n r₁ r₀ : ℕ} {σ γ₁ β : ℝ}
    {𝓗 : Hypergraph (Fin n)}
    (hn : 0 < n) (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)))
    (hβ : 0 < β) (hγ₁σ : γ₁ ≤ σ / 2)
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    {C_large Cmed : Finset (Fin n)} (hdisjCL : Disjoint C_large Cmed)
    (hbudgetL : (C_large.card : ℝ) + (Cmed.card : ℝ) ≤ (1 - σ) * (n : ℝ))
    {φL : (𝓗.largeEdges r₀).Coloring (Fin n)} (hφL : φL.UsesColourSet C_large)
    (hsingL : ∀ c : Fin n, (∃ e : 𝓗.largeEdges r₀, e ∈ φL.colorClass c ∧
        β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)) →
      ∃ e₀ : 𝓗.largeEdges r₀, φL.colorClass c = {e₀})
    (hsmallL : ∀ c : Fin n, c ∉ Cmed →
      (¬ ∃ e : 𝓗.largeEdges r₀, e ∈ φL.colorClass c ∧
        β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)) →
      (φL.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} (hφmed : φmed.UsesColourSet Cmed)
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  have hsubL : 𝓗.largeEdges r₀ ⊆ 𝓗 := largeEdges_subset 𝓗 r₀
  have hsubM : 𝓗.medEdges r₁ r₀ ⊆ 𝓗 := medEdges_subset 𝓗 r₁ r₀
  have hcover : ∀ e ∈ 𝓗, e ∈ 𝓗.largeEdges r₀ ∨ e ∈ 𝓗.medEdges r₁ r₀ :=
    cover_large_med_edges hsize
  have hdisjG : Disjoint (𝓗.largeEdges r₀) (𝓗.medEdges r₁ r₀) :=
    disjoint_large_med_edges 𝓗 r₁ r₀
  let φ : 𝓗.Coloring (Fin n) :=
    coloringUnionOfCover hsubL hsubM hcover hdisjG hdisjCL φL φmed hφL hφmed
  have hφdef : φ = coloringUnionOfCover hsubL hsubM hcover hdisjG hdisjCL φL φmed hφL hφmed := rfl
  have hφlabel : ∀ e : 𝓗, φ.labels e = unionLabel hsubL hsubM hcover φL φmed e := by
    intro e; rw [hφdef]; rfl
  have hcvL : ∀ c : Fin n, c ∈ C_large → φ.classVertices c = φL.classVertices c := by
    intro c hc; rw [hφdef]
    exact classVertices_coloringUnionOfCover_left hφL hφmed hc
  have hcvM : ∀ c : Fin n, c ∉ C_large → φ.classVertices c = φmed.classVertices c := by
    intro c hc; rw [hφdef]
    exact classVertices_coloringUnionOfCover_right hφL hφmed hc
  have hmemL : ∀ {c : Fin n} (hc : c ∈ C_large) (e : 𝓗.largeEdges r₀),
      e ∈ φL.colorClass c →
      (⟨(e : Set (Fin n)), hsubL e.2⟩ : 𝓗) ∈ φ.colorClass c := by
    intro c hc e he
    refine (mem_colorClass_coloringUnionOfCover_left hφL hφmed hc _).mpr ⟨e.2, he⟩
  -- (i) huge colour classes are singletons
  have hsing : φ.SingletonClassesForHuge β := by
    intro c hc
    obtain ⟨e, hcli, hbig⟩ := hc
    have heL : (e : Set (Fin n)) ∈ 𝓗.largeEdges r₀ := by
      rw [mem_largeEdges]
      refine ⟨e.2, ?_⟩
      exact_mod_cast (lt_of_lt_of_le hβn hbig :
        (r₀ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    have hlab : φ.labels e = φL.labels ⟨(e : Set (Fin n)), heL⟩ := by
      rw [hφlabel, unionLabel_of_mem heL]
    have hmemLc : (⟨(e : Set (Fin n)), heL⟩ : 𝓗.largeEdges r₀) ∈ φL.colorClass c := by
      rw [mem_colorClass]; exact hlab.symm.trans hcli
    have hcL : c ∈ C_large := by
      have hEq : φL.labels ⟨(e : Set (Fin n)), heL⟩ = c := hlab.symm.trans hcli
      rw [← hEq]; exact hφL _
    obtain ⟨e₀, hs⟩ := hsingL c ⟨⟨(e : Set (Fin n)), heL⟩, hmemLc, hbig⟩
    refine ⟨⟨(e₀ : Set (Fin n)), hsubL e₀.2⟩, ?_⟩
    rw [hφdef]
    exact colorClass_coloringUnionOfCover_left hφL hφmed hcL hs
  -- (ii) the medium colours cover few vertices
  have hclassMed : ∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ) := by
    intro c hc
    have hcL : c ∉ C_large := fun h => Finset.disjoint_left.mp hdisjCL h hc
    have h2 : (φ.classVertexCount c : ℝ) = (φmed.classVertexCount c : ℝ) := by
      rw [classVertexCount_eq_of_classVertices_eq φ (hcvM c hcL)]; rfl
    rw [h2]; exact hmedb c
  -- (iii) all other colour classes cover at most `βn` vertices
  have hclassOther : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ) := by
    intro c hcM hnot
    by_cases hcL : c ∈ C_large
    · have hnotL : ¬ ∃ e : 𝓗.largeEdges r₀, e ∈ φL.colorClass c ∧
          β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by
        rintro ⟨e, he, hb⟩
        exact hnot ⟨⟨(e : Set (Fin n)), hsubL e.2⟩, hmemL hcL e he, hb⟩
      have h1 : (φL.classVertexCount c : ℝ) ≤ β * (n : ℝ) := hsmallL c hcM hnotL
      rw [classVertexCount_eq_of_classVertices_eq φ (hcvL c hcL)]
      exact_mod_cast h1
    · have hz : φ.classVertexCount c = 0 := by
        rw [classVertexCount_eq_of_classVertices_eq φ
          (by rw [hcvM c hcL, classVertices_eq_empty_of_notMem_usesColourSet hφmed hcM])]
        simp
      rw [hz, Nat.cast_zero]
      have : (0 : ℝ) ≤ β * (n : ℝ) := by positivity
      linarith
  have huses : φ.UsesColourSet (C_large ∪ Cmed) := by
    have h := coloringUnionOfCover_usesColourSet (h₁ := hsubL) (h₂ := hsubM)
      (hcover := hcover) (hdisjG := hdisjG) (hdisj := hdisjCL) hφL hφmed
    rwa [← hφdef] at h
  have hcardUnion : ((C_large ∪ Cmed).card : ℝ) ≤ (1 - σ) * (n : ℝ) := by
    rw [Finset.card_union_of_disjoint hdisjCL]
    exact_mod_cast hbudgetL
  refine ⟨φ, C_large ∪ Cmed, Cmed, huses, hcardUnion, Finset.subset_union_right, hCmed,
    ?_, hclassMed, hsing, hclassOther⟩
  intro e he
  have heM : (e : Set (Fin n)) ∈ 𝓗.medEdges r₁ r₀ :=
    (edgeMedium_iff_mem_medEdges e.2).mp he
  have heNotL : (e : Set (Fin n)) ∉ 𝓗.largeEdges r₀ :=
    fun h => (Set.disjoint_left.mp hdisjG) h heM
  have hlab : φ.labels e = φmed.labels ⟨(e : Set (Fin n)), heM⟩ := by
    rw [hφlabel, unionLabel_of_notMem heNotL]
  rw [hlab]
  exact hφmed _

end

end ErdosFaberLovaszConjecture
