import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AuxDefs

/-!
# The degrees of the auxiliary hypergraph `𝓗_aux` (equation `eqn:degree_aux`)

This module proves `Work.Deep.Nibble.aux_degree`: every vertex of the auxiliary
hypergraph `𝓗_aux` of the proof of `lem:pseudorandom_matching` has degree
`(1 ± 2β)D`.

The auxiliary hypergraph has two kinds of vertices, and the two cases are
handled separately.

* An `e*`-vertex (`auxVInl f hf`, for an edge `f ∈ 𝓖`) lies in exactly the
  edges `{f} ∪ {v^i : v ∈ f}` indexed by the `i` with `f ∩ ι '' V(M i) = ∅`.
  There are `D - |{i : f ∩ ι '' V(M i) ≠ ∅}|` of these, and the second term is
  at most `βD` by `hunif`.
* A `w^i`-vertex (`auxVInr i w hw`) lies in exactly the edges indexed by the
  edges `f ∈ 𝓖` with `w ∈ f` and `f ∩ ι '' V(M i) = ∅`.  The number of edges of
  `𝓖` through `w` is `(1 ± β)D` by `hdeglo`/`hdeghi`, and the number of those
  meeting `ι '' V(M i)` is at most `|V(M i)| ≤ βD` because `𝓖` is linear and
  `w ∉ ι '' V(M i)` (`ncard_edgesThrough_meet_le`).

The two key sub-lemmas are `auxEdge_inj_right` (the `e*`-vertex of an edge
determines the index `i`, using `r ≥ 1` so that `f ≠ ∅`) and
`auxEdge_inj_left` (the index determines the edge `f`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

noncomputable section

variable {n M D : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
  {Mfam : Fin D → Set (Set (Fin n))}

/-- For nonempty `f`, the vertices `auxVInr i v ·` distinguish the edges
`auxEdge f i` from one another. -/
theorem auxEdge_inj_right {f : Set (Fin M)} (hfne : f.Nonempty) {i₁ i₂ : Fin D}
    (h₁ : f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i₁) = ∅)
    (h₂ : f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i₂) = ∅)
    (h : auxEdge n M D 𝓖 ι Mfam f i₁ = auxEdge n M D 𝓖 ι Mfam f i₂) : i₁ = i₂ := by
  by_contra hne
  obtain ⟨v, hv⟩ := hfne
  have hv₂ : v ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i₂) := by
    intro hmem
    have hmem' : v ∈ f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i₂) := ⟨hv, hmem⟩
    rw [h₂] at hmem'; exact hmem'
  have hmem : auxVInr n M D 𝓖 ι Mfam i₂ v hv₂ ∈ auxEdge n M D 𝓖 ι Mfam f i₂ := by
    rw [auxVInr_mem_auxEdge]; exact ⟨rfl, hv⟩
  have hnot : auxVInr n M D 𝓖 ι Mfam i₂ v hv₂ ∉ auxEdge n M D 𝓖 ι Mfam f i₁ := by
    rw [auxVInr_mem_auxEdge]
    rintro ⟨hii, -⟩
    exact hne hii.symm
  rw [← h] at hmem
  exact hnot hmem

/-- `Set.InjOn` form of `auxEdge_inj_right`. -/
theorem auxEdge_injOn_right {f : Set (Fin M)} (hfne : f.Nonempty) :
    Set.InjOn (fun i : Fin D => auxEdge n M D 𝓖 ι Mfam f i)
      {i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅} :=
  fun _ h₁ _ h₂ h => auxEdge_inj_right hfne h₁ h₂ h

/-- For a fixed `i`, the edge `auxEdge · i` determines the edge `f ∈ 𝓖`. -/
theorem auxEdge_inj_left {i : Fin D} {f₁ f₂ : Set (Fin M)}
    (h₁ : f₁ ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅)
    (h₂ : f₂ ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅)
    (h : auxEdge n M D 𝓖 ι Mfam f₁ i = auxEdge n M D 𝓖 ι Mfam f₂ i) : f₁ = f₂ := by
  by_contra hne
  have hdiff : (∃ v, v ∈ f₁ ∧ v ∉ f₂) ∨ (∃ v, v ∈ f₂ ∧ v ∉ f₁) := by
    by_cases hsub : f₁ ⊆ f₂
    · right
      by_contra hcon
      exact hne (Set.Subset.antisymm hsub fun v hv => by
        by_contra hv'
        exact hcon ⟨v, hv, hv'⟩)
    · exact Or.inl (Set.not_subset.mp hsub)
  rcases hdiff with ⟨v, hv₁, hv₂⟩ | ⟨v, hv₂, hv₁⟩
  · have hvv : v ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) := by
      intro hmem
      have hmem' : v ∈ f₁ ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) := ⟨hv₁, hmem⟩
      rw [h₁] at hmem'; exact hmem'
    have hmem : auxVInr n M D 𝓖 ι Mfam i v hvv ∈ auxEdge n M D 𝓖 ι Mfam f₁ i := by
      rw [auxVInr_mem_auxEdge]; exact ⟨rfl, hv₁⟩
    have hnot : auxVInr n M D 𝓖 ι Mfam i v hvv ∉ auxEdge n M D 𝓖 ι Mfam f₂ i := by
      rw [auxVInr_mem_auxEdge]; rintro ⟨-, hv'⟩; exact hv₂ hv'
    rw [h] at hmem
    exact hnot hmem
  · have hvv : v ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) := by
      intro hmem
      have hmem' : v ∈ f₂ ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) := ⟨hv₂, hmem⟩
      rw [h₂] at hmem'; exact hmem'
    have hmem : auxVInr n M D 𝓖 ι Mfam i v hvv ∈ auxEdge n M D 𝓖 ι Mfam f₂ i := by
      rw [auxVInr_mem_auxEdge]; exact ⟨rfl, hv₂⟩
    have hnot : auxVInr n M D 𝓖 ι Mfam i v hvv ∉ auxEdge n M D 𝓖 ι Mfam f₁ i := by
      rw [auxVInr_mem_auxEdge]; rintro ⟨-, hv'⟩; exact hv₁ hv'
    rw [← h] at hmem
    exact hnot hmem

/-- `Set.InjOn` form of `auxEdge_inj_left`. -/
theorem auxEdge_injOn_left (i : Fin D) :
    Set.InjOn (fun f : Set (Fin M) => auxEdge n M D 𝓖 ι Mfam f i)
      {f : Set (Fin M) | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅} :=
  fun _ h₁ _ h₂ h => auxEdge_inj_left h₁ h₂ h

/-- The edges of `𝓗_aux` through the `e*`-vertex `auxVInl f hf` are exactly the
edges `auxEdge f i` with `f ∩ ι '' V(M i) = ∅`. -/
theorem mem_auxHypergraph_auxVInl {f : Set (Fin M)} (hf : f ∈ 𝓖)
    (A : Set (AuxVertex n M D 𝓖 ι Mfam)) :
    (A ∈ auxHypergraph n M D 𝓖 ι Mfam ∧ auxVInl n M D 𝓖 ι Mfam f hf ∈ A) ↔
      ∃ i : Fin D, f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅ ∧
        A = auxEdge n M D 𝓖 ι Mfam f i := by
  constructor
  · rintro ⟨hA, hyA⟩
    obtain ⟨f', hf', i, hd, hAeq⟩ := mem_auxHypergraph.mp hA
    rw [hAeq] at hyA
    have hff' : f = f' := (auxVInl_mem_auxEdge (f := f') (f' := f) hf i).mp hyA
    refine ⟨i, ?_, ?_⟩
    · rw [hff']; exact hd
    · rw [hff']; exact hAeq
  · rintro ⟨i, hd, rfl⟩
    exact ⟨⟨f, hf, i, hd, rfl⟩, by simp⟩

/-- The edges of `𝓗_aux` through the `w^i`-vertex `auxVInr i w hw` are exactly
the edges `auxEdge f i` with `f ∈ 𝓖`, `w ∈ f` and `f ∩ ι '' V(M i) = ∅`. -/
theorem mem_auxHypergraph_auxVInr {i : Fin D} {w : Fin M}
    (hw : w ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i))
    (A : Set (AuxVertex n M D 𝓖 ι Mfam)) :
    (A ∈ auxHypergraph n M D 𝓖 ι Mfam ∧ auxVInr n M D 𝓖 ι Mfam i w hw ∈ A) ↔
      ∃ f : Set (Fin M), f ∈ 𝓖 ∧ w ∈ f ∧
        f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅ ∧
          A = auxEdge n M D 𝓖 ι Mfam f i := by
  constructor
  · rintro ⟨hA, hyA⟩
    obtain ⟨f', hf', i', hd, hAeq⟩ := mem_auxHypergraph.mp hA
    rw [hAeq] at hyA
    have hspec := (auxVInr_mem_auxEdge (hw := hw) (f := f') (i := i') (i' := i) (w := w)).mp hyA
    refine ⟨f', hf', hspec.2, ?_, ?_⟩
    · rw [hspec.1]; exact hd
    · rw [hspec.1]; exact hAeq
  · rintro ⟨f, hf, hwf, hd, rfl⟩
    exact ⟨⟨f, hf, i, hd, rfl⟩, by rw [auxVInr_mem_auxEdge]; exact ⟨rfl, hwf⟩⟩

/-- Linearity of `𝓖` and `w ∉ ι '' V(M i)` bound the number of edges of `𝓖`
through `w` meeting `ι '' V(M i)` by `|V(M i)|`: each such edge contains `w` and
some other vertex of `ι '' V(M i)`, and each such vertex determines at most one
edge. -/
theorem ncard_edgesThrough_meet_le {i : Fin D} {w : Fin M} (hlin : 𝓖.IsLinear)
    (hw : w ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)) :
    ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
        (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard
      ≤ (ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).ncard := by
  have hnat : Nat.card {f : Set (Fin M) // f ∈ 𝓖 ∧ w ∈ f ∧
        (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}
      ≤ Nat.card (↥(ι '' ErdosFaberLovaszConjecture.famVert (Mfam i))) := by
    refine Nat.card_le_card_of_injective
      (fun f => (⟨Classical.choose f.2.2.2, (Classical.choose_spec f.2.2.2).2⟩ :
        ↥(ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)))) ?_
    intro f₁ f₂ heq
    have hc₁ := Classical.choose_spec f₁.2.2.2
    have hc₂ := Classical.choose_spec f₂.2.2.2
    have hu : Classical.choose f₁.2.2.2 = Classical.choose f₂.2.2.2 := congrArg Subtype.val heq
    by_contra hne
    have hne' : f₁.val ≠ f₂.val := fun he => hne (Subtype.ext he)
    have hsub := hlin f₁.2.1 f₂.2.1 hne'
    have hw12 : w ∈ f₁.val ∩ f₂.val := ⟨f₁.2.2.1, f₂.2.2.1⟩
    have hu12 : Classical.choose f₁.2.2.2 ∈ f₁.val ∩ f₂.val := ⟨hc₁.1, by rw [hu]; exact hc₂.1⟩
    have hwu : w = Classical.choose f₁.2.2.2 := hsub hw12 hu12
    exact hw (by rw [hwu]; exact hc₁.2)
  exact hnat

/-- Every vertex of the auxiliary hypergraph `𝓗_aux` has degree `(1 ± 2β)D`
(equation `eqn:degree_aux` of the paper), assuming the bounds on the degrees of
`𝓖`, the sizes `|V(M i)| ≤ βD` and the interaction `eqn:unif_intersect`. -/
theorem aux_degree {n M D r : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    {ι : Fin n ↪ Fin M} {Mfam : Fin D → Set (Set (Fin n))} {β : ℝ}
    (hr : 1 ≤ r) (huni : ∀ f ∈ 𝓖, f.ncard = r) (hlin : 𝓖.IsLinear)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2)
    (hMsize : ∀ i, ((ErdosFaberLovaszConjecture.famVert (Mfam i)).ncard : ℝ) ≤ β * D)
    (hdeglo : ∀ w : Fin M,
      (1 - β) * D ≤ (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ))
    (hdeghi : ∀ w : Fin M,
      (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ) ≤ (1 + β) * D)
    (hunif : ∀ f ∈ 𝓖,
      (({i : Fin D | (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℝ) ≤ β * D)
    (y : Work.Deep.Nibble.AuxVertex n M D 𝓖 ι Mfam) :
    |((Work.Deep.Nibble.degreeAt (Work.Deep.Nibble.auxHypergraph n M D 𝓖 ι Mfam) y : ℝ)) - (D : ℝ)| ≤
      2 * β * (D : ℝ) := by
  have _hβ1 := hβ1
  classical
  obtain ⟨yval, hyval⟩ := y
  rcases yval with f | ⟨i, w⟩
  · -- the vertex is `e*` for the edge `f ∈ 𝓖`
    change f ∈ 𝓖 at hyval
    change |((degreeAt (auxHypergraph n M D 𝓖 ι Mfam) (auxVInl n M D 𝓖 ι Mfam f hyval) : ℝ)) -
      (D : ℝ)| ≤ 2 * β * (D : ℝ)
    have hfne : f.Nonempty := by
      rw [← Set.ncard_pos, huni f hyval]
      omega
    have hS : ({A : Set (AuxVertex n M D 𝓖 ι Mfam) |
          A ∈ auxHypergraph n M D 𝓖 ι Mfam ∧ auxVInl n M D 𝓖 ι Mfam f hyval ∈ A})
        = (fun i : Fin D => auxEdge n M D 𝓖 ι Mfam f i) ''
            {i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅} := by
      ext A
      constructor
      · intro hA
        obtain ⟨i, hi, hAeq⟩ := (mem_auxHypergraph_auxVInl hyval A).mp hA
        exact ⟨i, hi, hAeq.symm⟩
      · rintro ⟨i, hi, rfl⟩
        exact (mem_auxHypergraph_auxVInl hyval (auxEdge n M D 𝓖 ι Mfam f i)).mpr ⟨i, hi, rfl⟩
    have hcardA : degreeAt (auxHypergraph n M D 𝓖 ι Mfam) (auxVInl n M D 𝓖 ι Mfam f hyval)
        = ({i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard := by
      rw [show degreeAt (auxHypergraph n M D 𝓖 ι Mfam) (auxVInl n M D 𝓖 ι Mfam f hyval) =
        ({A : Set (AuxVertex n M D 𝓖 ι Mfam) |
          A ∈ auxHypergraph n M D 𝓖 ι Mfam ∧ auxVInl n M D 𝓖 ι Mfam f hyval ∈ A}).ncard from rfl]
      rw [hS, Set.InjOn.ncard_image (auxEdge_injOn_right (𝓖 := 𝓖) (ι := ι) (Mfam := Mfam) hfne)]
    have hdisjA : Disjoint {i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}
        {i : Fin D | (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty} := by
      rw [Set.disjoint_left]
      intro j hp hq
      exact hq.ne_empty hp
    have hunionA : ({i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅} ∪
        {i : Fin D | (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty})
        = Set.univ := by
      ext j
      constructor
      · intro _
        exact Set.mem_univ j
      · intro _
        rw [Set.mem_union]
        by_cases h : (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam j)).Nonempty
        · exact Or.inr h
        · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)
    have hsumA : ({i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard +
        ({i : Fin D | (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard
        = D := by
      rw [← Set.ncard_union_eq hdisjA, hunionA, Set.ncard_univ, Nat.card_fin]
    have hQb : (({i : Fin D | (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℝ)
        ≤ β * (D : ℝ) := hunif f hyval
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have hβD : (0 : ℝ) ≤ β * (D : ℝ) := mul_nonneg hβ0.le hD0
    have hcastA : ((({i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ) +
        ((({i : Fin D | (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℕ) : ℝ)
        = (D : ℝ) := by
      rw [← Nat.cast_add, hsumA]
    have hupperA : ((({i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ)
        ≤ (D : ℝ) := by linarith
    have hlowerA : (D : ℝ) - β * (D : ℝ) ≤
        ((({i : Fin D | f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ) := by
      linarith
    rw [hcardA, abs_le]
    exact ⟨by linarith [hlowerA, hβD], by linarith [hupperA, hβD]⟩
  · -- the vertex is `w^i`
    change w ∉ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) at hyval
    change |((degreeAt (auxHypergraph n M D 𝓖 ι Mfam) (auxVInr n M D 𝓖 ι Mfam i w hyval) : ℝ)) -
      (D : ℝ)| ≤ 2 * β * (D : ℝ)
    have hT : ({A : Set (AuxVertex n M D 𝓖 ι Mfam) |
          A ∈ auxHypergraph n M D 𝓖 ι Mfam ∧ auxVInr n M D 𝓖 ι Mfam i w hyval ∈ A})
        = (fun f : Set (Fin M) => auxEdge n M D 𝓖 ι Mfam f i) ''
            {f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
              f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅} := by
      ext A
      constructor
      · intro hA
        obtain ⟨f, hf, hwf, hd, hAeq⟩ := (mem_auxHypergraph_auxVInr hyval A).mp hA
        exact ⟨f, ⟨hf, hwf, hd⟩, hAeq.symm⟩
      · rintro ⟨f, ⟨hf, hwf, hd⟩, rfl⟩
        exact (mem_auxHypergraph_auxVInr hyval (auxEdge n M D 𝓖 ι Mfam f i)).mpr
          ⟨f, hf, hwf, hd, rfl⟩
    have hcardB : degreeAt (auxHypergraph n M D 𝓖 ι Mfam) (auxVInr n M D 𝓖 ι Mfam i w hyval)
        = ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard := by
      rw [show degreeAt (auxHypergraph n M D 𝓖 ι Mfam) (auxVInr n M D 𝓖 ι Mfam i w hyval) =
        ({A : Set (AuxVertex n M D 𝓖 ι Mfam) |
          A ∈ auxHypergraph n M D 𝓖 ι Mfam ∧ auxVInr n M D 𝓖 ι Mfam i w hyval ∈ A}).ncard from rfl]
      rw [hT]
      exact Set.InjOn.ncard_image
        ((auxEdge_injOn_left (𝓖 := 𝓖) (ι := ι) (Mfam := Mfam) i).mono (fun f hf => hf.2.2))
    have hle1 : ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
          f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard
        ≤ ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w := by
      have h1 : ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard
          ≤ ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f}).ncard :=
        Set.ncard_le_ncard (fun f hf => ⟨hf.1, hf.2.1⟩)
      rwa [show ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f}).ncard =
        ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w from rfl] at h1
    have hbad : (({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
          (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℝ)
        ≤ β * (D : ℝ) := by
      have h1 : ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard
          ≤ (ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).ncard :=
        ncard_edgesThrough_meet_le hlin hyval
      have h2 : ((ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).ncard : ℝ) ≤ β * (D : ℝ) := by
        rw [Set.ncard_image_of_injective (ErdosFaberLovaszConjecture.famVert (Mfam i)) ι.injective]
        exact hMsize i
      have h1' : (({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℝ)
          ≤ ((ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).ncard : ℝ) := by
        exact_mod_cast h1
      linarith
    have hdecomp : ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w
        = ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
              f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard
          + ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
              (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard := by
      have hunion : ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅} ∪
          {f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty})
          = {f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f} := by
        ext f
        rw [Set.mem_union]
        constructor
        · rintro (h | h) <;> exact ⟨h.1, h.2.1⟩
        · intro h
          by_cases hc : (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty
          · exact Or.inr ⟨h.1, h.2, hc⟩
          · exact Or.inl ⟨h.1, h.2, Set.not_nonempty_iff_eq_empty.mp hc⟩
      have hdisj : Disjoint ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅})
          ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}) := by
        rw [Set.disjoint_left]
        intro f hp hq
        exact hq.2.2.ne_empty hp.2.2
      rw [show ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w =
        ({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f}).ncard from rfl]
      rw [← Set.ncard_union_eq hdisj, hunion]
    have hdeg_hi : (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ) ≤ (1 + β) * (D : ℝ) :=
      hdeghi w
    have hdeg_lo : (1 - β) * (D : ℝ) ≤ (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ) :=
      hdeglo w
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have hβD : (0 : ℝ) ≤ β * (D : ℝ) := mul_nonneg hβ0.le hD0
    have hcastB : (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ)
        = ((({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
              f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ)
          + ((({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
              (f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℕ) : ℝ) := by
      rw [← Nat.cast_add, hdecomp]
    have hupperB : ((({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
          f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ)
        ≤ (1 + β) * (D : ℝ) := by
      have h1 : ((({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
            f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ)
          ≤ (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ) := by
        exact_mod_cast hle1
      linarith
    have hlowerB : (1 - β) * (D : ℝ) - β * (D : ℝ) ≤
        ((({f : Set (Fin M) | f ∈ 𝓖 ∧ w ∈ f ∧
          f ∩ ι '' ErdosFaberLovaszConjecture.famVert (Mfam i) = ∅}).ncard : ℕ) : ℝ) := by
      linarith
    rw [hcardB, abs_le]
    exact ⟨by linarith [hlowerB, hβD], by linarith [hupperB, hβD]⟩

end

end Work.Deep.Nibble
