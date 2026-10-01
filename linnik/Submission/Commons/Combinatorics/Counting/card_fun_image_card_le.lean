import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators

open Finset

namespace Commons.Combinatorics.Counting

/-- Every function `B : Fin n → Fin H` whose image has at most `r` elements factors as
`f ∘ g` with `f : Fin r → Fin H` and `g : Fin n → Fin r` (the image of `B` is enumerated by
an injective map `Fin (#image) → Fin H` which is padded to `Fin r → Fin H`). -/
private lemma exists_comp_eq_of_image_card_le (n H r : ℕ) (hH : 1 ≤ H) (B : Fin n → Fin H)
    (hB : (Finset.univ.image B).card ≤ r) :
    ∃ (f : Fin r → Fin H) (g : Fin n → Fin r), (fun i => f (g i)) = B := by
  classical
  set S : Finset (Fin H) := Finset.univ.image B with hSdef
  have hS : S.card ≤ r := hB
  set e : Fin S.card ↪o Fin H := S.orderEmbOfFin rfl with hedef
  have hrange : Set.range (e : Fin S.card → Fin H) = (S : Set (Fin H)) := by
    rw [hedef]; exact Finset.range_orderEmbOfFin S rfl
  have key1 : ∀ i : Fin n, ∃ k : Fin S.card, e k = B i := by
    intro i
    have hmem : B i ∈ S := by
      rw [hSdef]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have : B i ∈ Set.range (e : Fin S.card → Fin H) := by rw [hrange]; exact hmem
    exact Set.mem_range.mp this
  refine ⟨fun j => if h : (j : ℕ) < S.card then e ⟨j, h⟩ else ⟨0, hH⟩,
    fun i => ⟨(Classical.choose (key1 i)).val,
      lt_of_lt_of_le (Classical.choose (key1 i)).isLt hS⟩, ?_⟩
  funext i
  have hch : e (Classical.choose (key1 i)) = B i := Classical.choose_spec (key1 i)
  have hlt : ((⟨(Classical.choose (key1 i)).val,
      lt_of_lt_of_le (Classical.choose (key1 i)).isLt hS⟩ : Fin r) : ℕ) < S.card :=
    (Classical.choose (key1 i)).isLt
  beta_reduce
  rw [dif_pos hlt]
  rw [hch]

/-- The number of functions `B : Fin n → Fin H` whose image has at most `r` elements is at most
`(r + 1) * H ^ r * r ^ n`. -/
theorem card_fun_image_card_le (n H r : ℕ) (hH : 1 ≤ H) :
    (Finset.univ.filter (fun B : Fin n → Fin H => (Finset.univ.image B).card ≤ r)).card
      ≤ (r + 1) * H ^ r * r ^ n := by
  classical
  set A : Finset (Fin n → Fin H) :=
    Finset.univ.filter (fun B : Fin n → Fin H => (Finset.univ.image B).card ≤ r) with hA
  -- Counting via the surjection `(f, g) ↦ f ∘ g` from `(Fin r → Fin H) × (Fin n → Fin r)`.
  let φ : (Fin r → Fin H) × (Fin n → Fin r) → (Fin n → Fin H) := fun p => p.1 ∘ p.2
  have hsub : A ⊆ Finset.univ.image φ := by
    intro B hB
    rw [hA, Finset.mem_filter] at hB
    obtain ⟨-, hB⟩ := hB
    obtain ⟨f, g, hfg⟩ := exists_comp_eq_of_image_card_le n H r hH B hB
    refine Finset.mem_image.mpr ⟨(f, g), Finset.mem_univ _, ?_⟩
    show φ (f, g) = B
    simp only [φ]
    exact hfg
  calc A.card ≤ (Finset.univ.image φ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin r → Fin H) × (Fin n → Fin r))).card :=
        Finset.card_image_le
    _ = Fintype.card ((Fin r → Fin H) × (Fin n → Fin r)) := Finset.card_univ
    _ = H ^ r * r ^ n := by simp [Fintype.card_prod, Fintype.card_fin]
    _ ≤ (r + 1) * H ^ r * r ^ n := by
        rw [Nat.mul_assoc]
        exact Nat.le_mul_of_pos_left _ (Nat.succ_pos r)

end Commons.Combinatorics.Counting