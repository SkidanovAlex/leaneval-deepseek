import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Density

namespace Commons.Combinatorics.Matching

open Finset

lemma card_interedges_eq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (r : α → β → Prop) [DecidableRel r] (s : Finset α) (t : Finset β) :
    (Rel.interedges r s t).card = ∑ a ∈ s, (t.filter (r a)).card := by
  classical
  rw [Rel.interedges_eq_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.card_map]
  · intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_map] at hp hq
    obtain ⟨y, hy, hpy⟩ := hp
    obtain ⟨z, hz, hqz⟩ := hq
    exact hab ((congrArg Prod.fst hpy).trans (congrArg Prod.fst hqz).symm)

theorem upper_regular_exists_injective {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (Rd : A → B → Prop) [DecidableRel Rd] {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : ξ ≤ ρ)
    (hdeg : ∀ a : A, 2 * ρ * (Fintype.card A : ℝ) ≤ ((Finset.univ.filter (fun b => Rd a b)).card : ℝ))
    (hcard : ξ * ((Fintype.card A + Fintype.card B : ℕ) : ℝ) ≤ ρ * (Fintype.card A : ℝ))
    (hreg : ∀ (S : Finset A) (T : Finset B),
        ξ * ((Fintype.card A + Fintype.card B : ℕ) : ℝ) ≤ (S.card : ℝ) →
        ξ * ((Fintype.card A + Fintype.card B : ℕ) : ℝ) ≤ (T.card : ℝ) →
        (((S.product T).filter (fun p => Rd p.1 p.2)).card : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ)) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a : A, Rd a (f a) := by
  classical
  let nb : A → Finset B := fun a => Finset.univ.filter (fun b => Rd a b)
  let L : ℝ := ξ * ((Fintype.card A + Fintype.card B : ℕ) : ℝ)
  have hAnonneg : (0:ℝ) ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hcard' : L ≤ ρ * (Fintype.card A : ℝ) := hcard
  have hreg' : ∀ (S : Finset A) (T : Finset B), L ≤ (S.card : ℝ) → L ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => Rd p.1 p.2)).card : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) := hreg
  have hall : ∀ S : Finset A, S.card ≤ (S.biUnion nb).card := by
    intro S
    by_cases hS : S = ∅
    · subst hS; simp
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    set T : Finset B := S.biUnion nb with hT
    have hsub : ∀ a ∈ S, nb a ⊆ T := by
      intro a ha
      rw [hT]
      exact Finset.subset_biUnion_of_mem nb ha
    have hdegl : ∀ a ∈ S, (2:ℝ) * ρ * (Fintype.card A : ℝ) ≤ ((nb a).card : ℝ) := by
      intro a ha; exact hdeg a
    have hfilt : ∀ a ∈ S, T.filter (fun b => Rd a b) = nb a := by
      intro a ha
      ext b
      simp only [Finset.mem_filter, nb, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hsub a ha (Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩), h⟩⟩
    have hcount : (Rel.interedges Rd S T).card = ∑ a ∈ S, (nb a).card := by
      rw [card_interedges_eq_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hfilt a ha]
    have hconst : ∑ a ∈ S, (2:ℝ) * ρ * (Fintype.card A : ℝ) = (S.card : ℝ) * (2 * ρ * (Fintype.card A : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have he_lower : (S.card : ℝ) * (2 * ρ * (Fintype.card A : ℝ)) ≤ ((Rel.interedges Rd S T).card : ℝ) := by
      rw [hcount, Nat.cast_sum, ← hconst]
      exact Finset.sum_le_sum (fun a ha => hdegl a ha)
    have hT_lb : (2:ℝ) * ρ * (Fintype.card A : ℝ) ≤ (T.card : ℝ) := by
      obtain ⟨a, ha⟩ := hSne
      calc (2:ℝ) * ρ * (Fintype.card A : ℝ) ≤ ((nb a).card : ℝ) := hdeg a
        _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card (hsub a ha)
    by_cases hcase : L ≤ (S.card : ℝ)
    · have hTtr : L ≤ (T.card : ℝ) := by
        have h2 : L ≤ ρ * (Fintype.card A : ℝ) := hcard'
        have h3 : ρ * (Fintype.card A : ℝ) ≤ (2:ℝ) * ρ * (Fintype.card A : ℝ) := by
          nlinarith [hρ, hAnonneg]
        linarith
      have hregapp : (((S.product T).filter (fun p => Rd p.1 p.2)).card : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) :=
        hreg' S T hcase hTtr
      have he_upper : ((Rel.interedges Rd S T).card : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) := by
        simpa [Rel.interedges] using hregapp
      have hs_pos : 0 < (S.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hSne
      have h1 : (2:ℝ) * ρ * (Fintype.card A : ℝ) ≤ (ρ + ξ) * (T.card : ℝ) := by
        have h := he_lower.trans he_upper
        have h' : (S.card : ℝ) * (2 * ρ * (Fintype.card A : ℝ)) ≤ (S.card : ℝ) * ((ρ + ξ) * (T.card : ℝ)) := by
          nlinarith [h]
        exact le_of_mul_le_mul_left h' hs_pos
      have h2 : (Fintype.card A : ℝ) ≤ (T.card : ℝ) := by
        have hpos : 0 < ρ + ξ := by linarith
        have h3 : (ρ + ξ) * (Fintype.card A : ℝ) ≤ (2:ℝ) * ρ * (Fintype.card A : ℝ) := by
          nlinarith [hξρ, hAnonneg]
        have h4 : (ρ + ξ) * (Fintype.card A : ℝ) ≤ (ρ + ξ) * (T.card : ℝ) := le_trans h3 h1
        exact le_of_mul_le_mul_left h4 hpos
      have h5 : (S.card : ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast Finset.card_le_univ S
      exact_mod_cast le_trans h5 h2
    · have hlt : (S.card : ℝ) < L := lt_of_not_ge hcase
      have hST : (S.card : ℝ) < (T.card : ℝ) := by
        have h2 : L ≤ ρ * (Fintype.card A : ℝ) := hcard'
        have h3 : ρ * (Fintype.card A : ℝ) ≤ (2:ℝ) * ρ * (Fintype.card A : ℝ) := by
          nlinarith [hρ, hAnonneg]
        linarith
      exact_mod_cast le_of_lt hST
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (t := nb)).mp hall
  exact ⟨f, hfinj, fun a => by simpa [nb] using hfmem a⟩

end Commons.Combinatorics.Matching