import Mathlib
import Submission.SunBasic
import Submission.SunExtras

/-!
# 1-uniform sunflower facts
-/
open Finset

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- two distinct members of a 1-uniform family are disjoint. -/
lemma disjoint_of_one_uniform_ne {F : Finset (Finset α)}
    (huni : ∀ A ∈ F, A.card = 1) {A B : Finset α} (hA : A ∈ F) (hB : B ∈ F) (hAB : A ≠ B) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hcardA : A.card = 1 := huni A hA
  have hcardB : B.card = 1 := huni B hB
  rcases Finset.card_eq_one.mp hcardA with ⟨a, rfl⟩
  rcases Finset.card_eq_one.mp hcardB with ⟨b, rfl⟩
  simp at hxA hxB
  have ha : a = b := hxA.symm.trans hxB
  exact hAB (by simp [ha])

/-- A 1-uniform family with at least p members contains a p-sunflower. -/
lemma one_uniform_has_sunflower {F : Finset (Finset α)} {p : ℕ} (hp : 2 ≤ p)
    (huni : ∀ A ∈ F, A.card = 1) (hcard : p ≤ F.card) :
    HasSunflower F p := by
  rcases Finset.exists_subset_card_eq hcard with ⟨S, hSsub, hScard⟩
  refine ⟨S, hSsub, ?_⟩
  exact IsSunflower_of_pairwise_disjoint hp hScard
    (by
      intro A hA B hB hAB
      exact disjoint_of_one_uniform_ne huni (hSsub hA) (hSsub hB) hAB)

/-- A 1-uniform sunflower-free family has at most p-1 members. -/
lemma one_uniform_sunfree_card {F : Finset (Finset α)} {p : ℕ} (hp : 2 ≤ p)
    (huni : ∀ A ∈ F, A.card = 1) (hfree : SunflowerFree F p) :
    F.card ≤ p - 1 := by
  by_contra h
  have hpcard : p ≤ F.card := by omega
  exact hfree (one_uniform_has_sunflower hp huni hpcard)

/-- subfamilies of sunflower-free families are sunflower-free. -/
lemma sunfree_of_subset {F G : Finset (Finset α)} {p : ℕ} (hGF : G ⊆ F)
    (hfree : SunflowerFree F p) : SunflowerFree G p := by
  intro hG
  exact hfree (HasSunflower.mono hGF hG)

end Submission.Sun
