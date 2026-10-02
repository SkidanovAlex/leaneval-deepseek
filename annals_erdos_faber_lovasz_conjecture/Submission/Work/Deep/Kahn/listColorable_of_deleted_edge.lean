import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

theorem listColorable_of_deleted_edge {n : ℕ} {α : Type*}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (e₀ : 𝓗) (L : 𝓗 → Finset α)
    (hcount : Nat.card {f : 𝓗 // f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ (e₀ : Set (Fin n))).Nonempty}
      < (L e₀).card)
    (χ : (ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {(e₀ : Set (Fin n))}).Coloring α)
    (hχ : ∀ f : ErdosFaberLovaszConjecture.Hypergraph.edgeDiff 𝓗 {(e₀ : Set (Fin n))},
      χ.labels f ∈ L ⟨(f : Set (Fin n)), f.2.1⟩) :
    ErdosFaberLovaszConjecture.Hypergraph.ListColorable L := by
  classical
  -- the edges of `𝓗` other than `e₀` that meet `e₀`
  let D := {f : 𝓗 // f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ (e₀ : Set (Fin n))).Nonempty}
  -- the colour that `χ` gives to an edge `f ≠ e₀` of `𝓗`
  let chi : (f : 𝓗) → f ≠ e₀ → α := fun f hf =>
    χ.labels ⟨(f : Set (Fin n)), f.2, fun hmem => hf (Subtype.ext hmem)⟩
  -- the colours used by `χ` on those edges
  let g : D → α := fun d => chi d.1 d.2.1
  haveI : Fintype D := Fintype.ofFinite D
  let F : Finset α := (Finset.univ : Finset D).image g
  have hcountD : Nat.card D < (L e₀).card := hcount
  have hFcard : F.card < (L e₀).card := by
    have hle : F.card ≤ Nat.card D := by
      have h := Finset.card_image_le (s := (Finset.univ : Finset D)) (f := g)
      rw [Nat.card_eq_fintype_card]
      simpa using h
    omega
  -- there is a colour of `L e₀` that is used on none of those edges
  obtain ⟨c₀, hc₀L, hc₀F⟩ : ∃ c : α, c ∈ L e₀ ∧ c ∉ F := by
    by_contra hcon
    have hcon' : ∀ c : α, c ∈ L e₀ → c ∈ F := by
      intro c hc
      by_contra hcF
      exact hcon ⟨c, hc, hcF⟩
    have hle : (L e₀).card ≤ F.card := Finset.card_le_card hcon'
    omega
  -- the colouring of `𝓗`: `e₀` gets `c₀`, every other edge keeps its colour
  refine ⟨⟨fun e => if h : e = e₀ then c₀ else chi e h, ?_⟩, ?_⟩
  · intro e₁ e₂ he hnon
    by_cases h₁ : e₁ = e₀
    · -- `e₁ = e₀`, the other edge is coloured by `χ`
      have h₂ : e₂ ≠ e₀ := fun h => he (h₁.trans h.symm)
      simp only [dif_pos h₁, dif_neg h₂]
      intro hcon
      have hnon' : ((e₂ : Set (Fin n)) ∩ (e₀ : Set (Fin n))).Nonempty := by
        have h1 : ((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty := hnon
        rw [h₁] at h1
        rw [Set.inter_comm]
        exact h1
      exact hc₀F (Finset.mem_image.mpr ⟨⟨e₂, h₂, hnon'⟩, Finset.mem_univ _, hcon.symm⟩)
    · by_cases h₂ : e₂ = e₀
      · -- symmetric case
        simp only [dif_neg h₁, dif_pos h₂]
        intro hcon
        have hnon' : ((e₁ : Set (Fin n)) ∩ (e₀ : Set (Fin n))).Nonempty := by
          have h1 : ((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty := hnon
          rwa [h₂] at h1
        exact hc₀F (Finset.mem_image.mpr ⟨⟨e₁, h₁, hnon'⟩, Finset.mem_univ _, hcon⟩)
      · -- both edges are coloured by `χ`
        simp only [dif_neg h₁, dif_neg h₂]
        let A : ↥(Hypergraph.edgeDiff 𝓗 {(e₀ : Set (Fin n))}) :=
          ⟨(e₁ : Set (Fin n)), e₁.2, fun hmem => h₁ (Subtype.ext hmem)⟩
        let B : ↥(Hypergraph.edgeDiff 𝓗 {(e₀ : Set (Fin n))}) :=
          ⟨(e₂ : Set (Fin n)), e₂.2, fun hmem => h₂ (Subtype.ext hmem)⟩
        have hne' : A ≠ B := by
          intro heq
          have hval : (A : Set (Fin n)) = (B : Set (Fin n)) := congrArg Subtype.val heq
          exact he (Subtype.ext hval)
        have hnon' : ((A : Set (Fin n)) ∩ (B : Set (Fin n))).Nonempty := hnon
        exact χ.isColoring A B hne' hnon'
  · intro e
    change (if h : e = e₀ then c₀ else chi e h) ∈ L e
    by_cases h : e = e₀
    · rw [dif_pos h, h]
      exact hc₀L
    · rw [dif_neg h]
      exact hχ ⟨(e : Set (Fin n)), e.2, fun hmem => h (Subtype.ext hmem)⟩

end Work.Deep.Kahn
