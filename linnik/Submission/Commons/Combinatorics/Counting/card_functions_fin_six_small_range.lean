import Mathlib

namespace Commons.Combinatorics.Counting

/-- Every function `B : Fin 6 → Fin H` whose image has at most `3` elements factors as
`f ∘ g` with `f : Fin 3 → Fin H` and `g : Fin 6 → Fin 3` (the image of `B` is enumerated by
an injective map `Fin (#image) → Fin H` which is padded to `Fin 3 → Fin H`). -/
private lemma exists_comp_eq_of_image_card_le_three (H : ℕ) (B : Fin 6 → Fin H)
    (hB : (Finset.univ.image B).card ≤ 3) :
    ∃ (f : Fin 3 → Fin H) (g : Fin 6 → Fin 3), (fun i => f (g i)) = B := by
  classical
  set S : Finset (Fin H) := Finset.univ.image B with hSdef
  have hS : S.card ≤ 3 := hB
  set e : Fin S.card ↪o Fin H := S.orderEmbOfFin rfl with hedef
  have hrange : Set.range (e : Fin S.card → Fin H) = (S : Set (Fin H)) := by
    rw [hedef]; exact Finset.range_orderEmbOfFin S rfl
  have key1 : ∀ i : Fin 6, ∃ k : Fin S.card, e k = B i := by
    intro i
    have hmem : B i ∈ S := by
      rw [hSdef]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have : B i ∈ Set.range (e : Fin S.card → Fin H) := by rw [hrange]; exact hmem
    exact Set.mem_range.mp this
  refine ⟨fun j => if h : (j : ℕ) < S.card then e ⟨j, h⟩ else B 0,
    fun i => ⟨(Classical.choose (key1 i)).val,
      lt_of_lt_of_le (Classical.choose (key1 i)).isLt hS⟩, ?_⟩
  funext i
  have hch : e (Classical.choose (key1 i)) = B i := Classical.choose_spec (key1 i)
  have hlt : ((⟨(Classical.choose (key1 i)).val,
      lt_of_lt_of_le (Classical.choose (key1 i)).isLt hS⟩ : Fin 3) : ℕ) < S.card :=
    (Classical.choose (key1 i)).isLt
  beta_reduce
  rw [dif_pos hlt]
  rw [hch]

/-- **Counting `Fin 6`-tuples taking at most three values.**

The number of functions `v : Fin 6 → Fin H` whose range has at most `3` elements is at most
`3^6 * H^3`.

Reason: such a `v` factors as `v = a ∘ ρ` with `ρ : Fin 6 → Fin 3` and `a : Fin 3 → Fin H`
(pick `a` to enumerate the range of `v`, padded arbitrarily), and the map
`v ↦ (a, ρ)` is injective because `(a, ρ)` determines `v = a ∘ ρ`.  Hence the count is at most
`#(Fin 6 → Fin 3) * #(Fin 3 → Fin H) = 3^6 * H^3`. -/
lemma card_functions_fin_six_small_range (H : ℕ) :
    ((Finset.univ : Finset (Fin 6 → Fin H)).filter
        (fun v => (Finset.univ.image v).card ≤ 3)).card ≤ 3 ^ 6 * H ^ 3 := by
  classical
  -- Counting via the surjection `(a, ρ) ↦ a ∘ ρ` from `(Fin 3 → Fin H) × (Fin 6 → Fin 3)`.
  set A : Finset (Fin 6 → Fin H) :=
    Finset.univ.filter (fun v : Fin 6 → Fin H => (Finset.univ.image v).card ≤ 3) with hA
  let φ : (Fin 3 → Fin H) × (Fin 6 → Fin 3) → (Fin 6 → Fin H) := fun p => p.1 ∘ p.2
  have hsub : A ⊆ Finset.univ.image φ := by
    intro B hB
    rw [hA, Finset.mem_filter] at hB
    obtain ⟨-, hB⟩ := hB
    obtain ⟨f, g, hfg⟩ := exists_comp_eq_of_image_card_le_three H B hB
    refine Finset.mem_image.mpr ⟨(f, g), Finset.mem_univ _, ?_⟩
    show φ (f, g) = B
    simp only [φ]
    exact hfg
  calc A.card ≤ (Finset.univ.image φ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin 3 → Fin H) × (Fin 6 → Fin 3))).card :=
        Finset.card_image_le
    _ = Fintype.card ((Fin 3 → Fin H) × (Fin 6 → Fin 3)) := Finset.card_univ
    _ = H ^ 3 * 3 ^ 6 := by simp [Fintype.card_prod, Fintype.card_fin]
    _ = 3 ^ 6 * H ^ 3 := by ring

end Commons.Combinatorics.Counting
