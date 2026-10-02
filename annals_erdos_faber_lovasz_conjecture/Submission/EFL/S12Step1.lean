import Submission.EFL.S12Step9Pack
import Submission.EFL.LargeEdgeThm

/-!
# §12, Step 1: from Theorem 6.7 to the Types A/B

The paper's proof of Theorem 1.1 begins by applying Theorem 6.7
(`large-edge-thm`) to the medium and large edges of `𝓗`, obtaining a colouring
`φ` of `𝓗_med ∪ 𝓗_large`.  The alternatives (6.7:a) and (6.7:b) are recorded in
the cone as `LargeEdgeNonExtremal`/`LargeEdgeExtremal` (colourings of *all* of
`𝓗`), while §12 works with the restriction to `𝓗_med ∪ 𝓗_large = medLarge 𝓗 r₁`
and the predicates `IsTypeA`/`IsTypeB`.

This module supplies the (elementary) passage between the two formulations:
restricting a colouring of `𝓗` to a subfamily, together with the behaviour of
`classVertexCount`, `AssignedToHuge` and `SingletonClassesForHuge` under
restriction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Restriction of a colouring to a subfamily -/

theorem Hypergraph.Coloring.restrict_labels {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} (e : 𝓖) :
    (φ.restrict hsub).labels e = φ.labels ⟨(e : Set (Fin n)), hsub e.2⟩ := rfl

theorem UsesColourSet_restrict {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} {C : Finset (Fin n)} (h : φ.UsesColourSet C) :
    (φ.restrict hsub).UsesColourSet C := by
  intro e
  exact h _

theorem classVertices_restrict_subset {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} (c : Fin n) :
    (φ.restrict hsub).classVertices c ⊆ φ.classVertices c := by
  rintro v ⟨e, he, hve⟩
  rw [mem_colorClass, Hypergraph.Coloring.restrict_labels] at he
  exact ⟨⟨(e : Set (Fin n)), hsub e.2⟩, by rw [mem_colorClass]; exact he, hve⟩

theorem classVertexCount_restrict_le {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} (c : Fin n) :
    (φ.restrict hsub).classVertexCount c ≤ φ.classVertexCount c :=
  Set.ncard_le_ncard (classVertices_restrict_subset hsub c) (Set.toFinite _)

theorem AssignedToHuge_restrict {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} {β : ℝ} {c : Fin n}
    (h : (φ.restrict hsub).AssignedToHuge β c) : φ.AssignedToHuge β c := by
  obtain ⟨e, he, hsz⟩ := h
  rw [mem_colorClass, Hypergraph.Coloring.restrict_labels] at he
  exact ⟨⟨(e : Set (Fin n)), hsub e.2⟩, by rw [mem_colorClass]; exact he, hsz⟩

/-- Conversely, if every edge of `𝓗` of size at least `βn/4` lies in `𝓖`,
restriction preserves "the colour `c` is assigned to a huge edge". -/
theorem AssignedToHuge_of_restrict {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} {β : ℝ}
    (hhuge : ∀ e ∈ 𝓗, β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ) → e ∈ 𝓖)
    {c : Fin n} (h : φ.AssignedToHuge β c) :
    (φ.restrict hsub).AssignedToHuge β c := by
  obtain ⟨e, he, hsz⟩ := h
  have hmem : (e : Set (Fin n)) ∈ 𝓖 := hhuge _ e.2 hsz
  refine ⟨⟨(e : Set (Fin n)), hmem⟩, ?_, hsz⟩
  rw [mem_colorClass, Hypergraph.Coloring.restrict_labels,
    show (⟨(e : Set (Fin n)), hsub hmem⟩ : 𝓗) = e from Subtype.ext rfl]
  rw [← mem_colorClass]; exact he

/-- The colour class of a restriction, when the colour class of `φ` is a
singleton edge lying in the subfamily. -/
theorem colorClass_restrict_eq {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} {c : Fin n} {e₀ : 𝓗}
    (he₀ : φ.colorClass c = {e₀}) (hmem : (e₀ : Set (Fin n)) ∈ 𝓖) :
    (φ.restrict hsub).colorClass c = {⟨(e₀ : Set (Fin n)), hmem⟩} := by
  ext e
  rw [Set.mem_singleton_iff, mem_colorClass, Hypergraph.Coloring.restrict_labels]
  constructor
  · intro h
    have h2 : (⟨(e : Set (Fin n)), hsub e.2⟩ : 𝓗) ∈ φ.colorClass c := by
      rw [mem_colorClass]; exact h
    rw [he₀] at h2
    exact Subtype.ext (congrArg (fun x : 𝓗 => (x : Set (Fin n))) (by simpa using h2))
  · intro h
    subst h
    have h1 : e₀ ∈ φ.colorClass c := by rw [he₀]; exact rfl
    rw [mem_colorClass] at h1
    show φ.labels ⟨(e₀ : Set (Fin n)), hsub hmem⟩ = c
    rwa [show (⟨(e₀ : Set (Fin n)), hsub hmem⟩ : 𝓗) = e₀ from Subtype.ext rfl]

/-- If every edge of `𝓗` of size at least `βn/4` lies in `𝓖`, then restriction
preserves the property "colour classes with a huge edge are singletons". -/
theorem SingletonClassesForHuge_restrict {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    {φ : 𝓗.Coloring (Fin n)} {β : ℝ}
    (hhuge : ∀ e ∈ 𝓗, β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ) → e ∈ 𝓖)
    (h : φ.SingletonClassesForHuge β) : (φ.restrict hsub).SingletonClassesForHuge β := by
  intro c hc
  obtain ⟨e₁, he₁, hsz₁⟩ := hc
  obtain ⟨e₀, he₀⟩ := h c (AssignedToHuge_restrict hsub ⟨e₁, he₁, hsz₁⟩)
  have h2 : (⟨(e₁ : Set (Fin n)), hsub e₁.2⟩ : 𝓗) ∈ φ.colorClass c := by
    rw [mem_colorClass, ← Hypergraph.Coloring.restrict_labels]; exact he₁
  rw [he₀] at h2
  have heq : (⟨(e₁ : Set (Fin n)), hsub e₁.2⟩ : 𝓗) = e₀ := by simpa using h2
  have hsz₀ : β * (n : ℝ) / 4 ≤ (edgeSize (e₀ : Set (Fin n)) : ℝ) := by
    rw [← heq]; exact hsz₁
  exact ⟨⟨(e₀ : Set (Fin n)), hhuge _ e₀.2 hsz₀⟩,
    colorClass_restrict_eq hsub he₀ (hhuge _ e₀.2 hsz₀)⟩


/-! ## From `LargeEdgeNonExtremal`/`LargeEdgeExtremal` to `IsTypeA`/`IsTypeB` -/

/-- The non-extremal alternative (6.7:a) of Theorem 6.7 is the Type A
hypothesis of §12 for the restriction of the colouring to `𝓗_med ∪ 𝓗_large`. -/
theorem isTypeA_exists_of_nonExtremal {n : ℕ} {𝓗 : Hypergraph (Fin n)}
    {r₁ r₀ σ γ₁ β : ℝ} (hr₁β : r₁ < β * (n : ℝ) / 4)
    (h : LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ 𝓗) :
    ∃ φ : (medLarge 𝓗 r₁).Coloring (Fin n), IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ := by
  obtain ⟨φ, C₁, Cmed, huses, hcard, hCmedsub, hCmedcard, hmed, hCmedvert, hsing,
    hvert⟩ := h
  let φ' : (medLarge 𝓗 r₁).Coloring (Fin n) := φ.restrict (medLarge_subset 𝓗 r₁)
  have hlab : ∀ e : ↥(medLarge 𝓗 r₁), φ'.labels e =
      φ.labels ⟨(e : Set (Fin n)), medLarge_subset 𝓗 r₁ e.2⟩ := fun e => rfl
  have hcvc : ∀ c : Fin n, φ'.classVertexCount c ≤ φ.classVertexCount c :=
    fun c => classVertexCount_restrict_le (medLarge_subset 𝓗 r₁) c
  have hass : ∀ {c : Fin n}, φ'.AssignedToHuge β c → φ.AssignedToHuge β c :=
    fun hc => AssignedToHuge_restrict (medLarge_subset 𝓗 r₁) hc
  have hhuge : ∀ e ∈ 𝓗, β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ) → e ∈ medLarge 𝓗 r₁ := by
    intro e he hs
    exact ⟨he, lt_of_lt_of_le hr₁β hs⟩
  refine ⟨φ', C₁, Cmed, UsesColourSet_restrict (medLarge_subset 𝓗 r₁) huses, hcard,
    hCmedsub, hCmedcard, ?_, ?_, ?_, ?_⟩
  · intro e hmed'
    rw [hlab e]
    exact hmed ⟨(e : Set (Fin n)), medLarge_subset 𝓗 r₁ e.2⟩ hmed'
  · intro c hc
    exact le_trans (Nat.cast_le.mpr (hcvc c)) (hCmedvert c hc)
  · exact SingletonClassesForHuge_restrict (medLarge_subset 𝓗 r₁) hhuge hsing
  · intro c hc hnot
    refine le_trans (Nat.cast_le.mpr (hcvc c)) (hvert c hc ?_)
    intro hcontra
    exact hnot (AssignedToHuge_of_restrict (medLarge_subset 𝓗 r₁) hhuge hcontra)

/-- The extremal alternative (6.7:b) of Theorem 6.7 is the Type B hypothesis of
§12 for the restriction of the colouring to `𝓗_med ∪ 𝓗_large`. -/
theorem isTypeB_exists_of_extremal {n : ℕ} {𝓗 : Hypergraph (Fin n)}
    {r₁ r₀ δ γ₂ γ₁ β : ℝ} (hr₁β : r₁ < β * (n : ℝ) / 4)
    (h : LargeEdgeExtremal n δ γ₂ γ₁ β r₁ r₀ 𝓗) :
    ∃ φ : (medLarge 𝓗 r₁).Coloring (Fin n), IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ := by
  obtain ⟨hW, φ, Cmed, hCmedcard, hmed, hCmedvert, hassigned, hvert⟩ := h
  let φ' : (medLarge 𝓗 r₁).Coloring (Fin n) := φ.restrict (medLarge_subset 𝓗 r₁)
  have hlab : ∀ e : ↥(medLarge 𝓗 r₁), φ'.labels e =
      φ.labels ⟨(e : Set (Fin n)), medLarge_subset 𝓗 r₁ e.2⟩ := fun e => rfl
  have hcvc : ∀ c : Fin n, φ'.classVertexCount c ≤ φ.classVertexCount c :=
    fun c => classVertexCount_restrict_le (medLarge_subset 𝓗 r₁) c
  have hass : ∀ {c : Fin n}, φ'.AssignedToHuge β c → φ.AssignedToHuge β c :=
    fun hc => AssignedToHuge_restrict (medLarge_subset 𝓗 r₁) hc
  have hhuge : ∀ e ∈ 𝓗, β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ) → e ∈ medLarge 𝓗 r₁ := by
    intro e he hs
    exact ⟨he, lt_of_lt_of_le hr₁β hs⟩
  have hbody : ∃ Cmed : Finset (Fin n),
      (Cmed.card : ℝ) ≤ γ₂ * (n : ℝ) ∧
      (∀ e : ↥(medLarge 𝓗 r₁), edgeMedium r₁ r₀ (e : Set (Fin n)) →
        φ'.labels e ∈ Cmed) ∧
      (∀ c ∈ Cmed, (φ'.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) ∧
      (∀ c : Fin n, φ'.AssignedToHuge β c → (φ'.classVertexCount c : ℝ) ≤ δ * (n : ℝ)) ∧
      (∀ c : Fin n, c ∉ Cmed → ¬ φ'.AssignedToHuge β c →
        (φ'.classVertexCount c : ℝ) ≤ β * (n : ℝ)) := by
    refine ⟨Cmed, hCmedcard, ?_, ?_, ?_, ?_⟩
    · intro e hmed'
      rw [hlab e]
      exact hmed ⟨(e : Set (Fin n)), medLarge_subset 𝓗 r₁ e.2⟩ hmed'
    · intro c hc
      exact le_trans (Nat.cast_le.mpr (hcvc c)) (hCmedvert c hc)
    · intro c hc
      exact le_trans (Nat.cast_le.mpr (hcvc c)) (hassigned c (hass (c := c) hc))
    · intro c hc hnot
      refine le_trans (Nat.cast_le.mpr (hcvc c)) (hvert c hc ?_)
      intro hcontra
      exact hnot (AssignedToHuge_of_restrict (medLarge_subset 𝓗 r₁) hhuge hcontra)
  exact ⟨φ', hW, hbody⟩

end

end ErdosFaberLovaszConjecture
