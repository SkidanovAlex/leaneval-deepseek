import Submission.EFL.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Combining edge-colourings of a partition

The paper's proofs (Theorem 1.3, Theorem 6.1) colour the pieces of a
partition of the edge set of a hypergraph separately — with *distinct* sets
of colours — and combine the colourings.  This module provides the
combinatorial glue: if `𝓖₁, 𝓖₂ (⊆ 𝓗)` cover `𝓗`, and `𝓖₁` is colourable with
`a` colours and `𝓖₂` with `b` colours, then `𝓗` is colourable with `a + b`
colours; the labels of `𝓖₁` are placed in `{0, …, a-1}` and those of `𝓖₂` in
`{a, …, a+b-1}`.

The three-part version `Colorable.union3` (the shape of the paper's
`𝓗 = 𝓗₁ ∪ 𝓗₂ ∪ 𝓗₃` decomposition) is derived.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

variable {V : Type*}

/-- **Combining two colourings on a partition.**  If `𝓖₁ ⊆ 𝓗`, `𝓖₂ ⊆ 𝓗` cover
the edges of `𝓗`, then colourings of `𝓖₁` with `a` colours and of `𝓖₂` with
`b` colours combine into a colouring of `𝓗` with `a + b` colours. -/
theorem Hypergraph.Colorable.union {𝓖₁ 𝓖₂ 𝓗 : Hypergraph V}
    (h₁ : 𝓖₁ ⊆ 𝓗) (h₂ : 𝓖₂ ⊆ 𝓗)
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂)
    {a b : ℕ} (ha : 𝓖₁.Colorable a) (hb : 𝓖₂.Colorable b) :
    𝓗.Colorable (a + b) := by
  classical
  obtain ⟨φ₁⟩ := ha
  obtain ⟨φ₂⟩ := hb
  let lab : 𝓗 → Fin (a + b) := fun e =>
    if he : (e : Set V) ∈ 𝓖₁ then Fin.castAdd b (φ₁.labels ⟨(e : Set V), he⟩)
    else Fin.natAdd a (φ₂.labels ⟨(e : Set V), (hcover (e : Set V) e.2).resolve_left he⟩)
  refine ⟨lab, ?_⟩
  intro e f hef hne
  show lab e ≠ lab f
  have hcast : ∀ (x : Fin a), ((Fin.castAdd b x : Fin (a + b)) : ℕ) = (x : ℕ) :=
    fun x => Fin.val_castAdd b x
  have hnat : ∀ (y : Fin b), ((Fin.natAdd a y : Fin (a + b)) : ℕ) = a + (y : ℕ) :=
    fun y => Fin.val_natAdd a y
  by_cases he : (e : Set V) ∈ 𝓖₁
  · by_cases hf : (f : Set V) ∈ 𝓖₁
    · intro hlab
      simp only [lab, dif_pos he, dif_pos hf] at hlab
      have hxy : φ₁.labels ⟨(e : Set V), he⟩ = φ₁.labels ⟨(f : Set V), hf⟩ :=
        Fin.castAdd_injective a b hlab
      exact φ₁.isColoring ⟨(e : Set V), he⟩ ⟨(f : Set V), hf⟩
        (fun hc => hef (Subtype.ext (by simpa using congrArg Subtype.val hc)))
        (by simpa using hne) hxy
    · intro hlab
      simp only [lab, dif_pos he, dif_neg hf] at hlab
      have hv := congrArg Fin.val hlab
      rw [hcast (φ₁.labels ⟨(e : Set V), he⟩), hnat (φ₂.labels _)] at hv
      have := (φ₁.labels ⟨(e : Set V), he⟩).isLt
      omega
  · by_cases hf : (f : Set V) ∈ 𝓖₁
    · intro hlab
      simp only [lab, dif_neg he, dif_pos hf] at hlab
      have hv := congrArg Fin.val hlab
      rw [hcast (φ₁.labels ⟨(f : Set V), hf⟩), hnat (φ₂.labels _)] at hv
      have := (φ₁.labels ⟨(f : Set V), hf⟩).isLt
      omega
    · intro hlab
      simp only [lab, dif_neg he, dif_neg hf] at hlab
      have hxy : φ₂.labels ⟨(e : Set V), (hcover (e : Set V) e.2).resolve_left he⟩
          = φ₂.labels ⟨(f : Set V), (hcover (f : Set V) f.2).resolve_left hf⟩ := by
        apply Fin.natAdd_injective b a
        exact hlab
      exact φ₂.isColoring ⟨(e : Set V), (hcover (e : Set V) e.2).resolve_left he⟩ _
        (fun hc => hef (Subtype.ext (by simpa using congrArg Subtype.val hc)))
        (by simpa using hne) hxy

/-- **Combining three colourings on a partition.**  If `𝓖₁, 𝓖₂, 𝓖₃ ⊆ 𝓗` cover
`𝓗`, then colourings with `a`, `b`, `c` colours combine into one with
`a + b + c` colours. -/
theorem Hypergraph.Colorable.union3 {𝓖₁ 𝓖₂ 𝓖₃ 𝓗 : Hypergraph V}
    (h₁ : 𝓖₁ ⊆ 𝓗) (h₂ : 𝓖₂ ⊆ 𝓗) (h₃ : 𝓖₃ ⊆ 𝓗)
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂ ∨ e ∈ 𝓖₃)
    {a b c : ℕ} (ha : 𝓖₁.Colorable a) (hb : 𝓖₂.Colorable b) (hc : 𝓖₃.Colorable c) :
    𝓗.Colorable (a + b + c) := by
  classical
  have hsub : (𝓖₂ ∪ 𝓖₃ : Hypergraph V) ⊆ 𝓗 := by
    intro e he
    rcases he with he | he
    · exact h₂ he
    · exact h₃ he
  have hbc : (𝓖₂ ∪ 𝓖₃ : Hypergraph V).Colorable (b + c) :=
    Hypergraph.Colorable.union (𝓖₁ := 𝓖₂) (𝓖₂ := 𝓖₃) (𝓗 := 𝓖₂ ∪ 𝓖₃)
      (a := b) (b := c)
      (by intro e he; exact Or.inl he) (by intro e he; exact Or.inr he)
      (by intro e he; exact he) hb hc
  refine Hypergraph.Colorable.mono (Nat.add_assoc a b c).ge ?_
  exact Hypergraph.Colorable.union (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂ ∪ 𝓖₃) (𝓗 := 𝓗)
    (a := a) (b := b + c) h₁ hsub
    (fun e he => by
      rcases hcover e he with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) ha hbc

end ErdosFaberLovaszConjecture
