import Mathlib

/-!
# Basic sunflower lemmas over finite sets

We develop the combinatorial core over `Finset (Finset α)` families.
-/
open Finset
open scoped BigOperators

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- The intersection of all members of a finite family of sets
(garbage `∅` if the family is empty). -/
noncomputable def interAll (S : Finset (Finset α)) : Finset α :=
  if h : S.Nonempty then S.inf' h id else ∅

lemma interAll_eq_inf' (S : Finset (Finset α)) (h : S.Nonempty) : interAll S = S.inf' h id := by
  simp [interAll, h]

lemma mem_interAll {S : Finset (Finset α)} (hS : S.Nonempty) {x : α} :
    x ∈ interAll S ↔ ∀ A, A ∈ S → x ∈ A := by
  rw [interAll_eq_inf' S hS]
  simp [Finset.mem_inf']

lemma interAll_subset {S : Finset (Finset α)} {A : Finset α} (hA : A ∈ S) : interAll S ⊆ A := by
  have hS : S.Nonempty := ⟨A, hA⟩
  intro x hx
  exact (mem_interAll hS).1 hx A hA

/-- A finite `r`-sunflower: `r` distinct sets whose pairwise intersections equal
the intersection of all of them. Mirrors `Set.IsSunflower`. -/
def IsSunflower (S : Finset (Finset α)) (r : ℕ) : Prop :=
  S.card = r ∧ ∀ A, A ∈ S → ∀ B, B ∈ S → A ≠ B → A ∩ B = interAll S

lemma IsSunflower.nonempty {S : Finset (Finset α)} {r : ℕ} (hS : IsSunflower S r) (hr : 0 < r) :
    S.Nonempty := by
  have hc : 0 < S.card := by simpa [hS.1] using hr
  exact Finset.card_pos.mp hc

/-- `r ≥ 2` pairwise disjoint members form an `r`-sunflower. -/
lemma IsSunflower_of_pairwise_disjoint {S : Finset (Finset α)} {r : ℕ} (hr : 2 ≤ r)
    (hS : S.card = r) (hdisj : ∀ A, A ∈ S → ∀ B, B ∈ S → A ≠ B → Disjoint A B) :
    IsSunflower S r := by
  refine ⟨hS, ?_⟩
  intro A hA B hB hAB
  have hnon : S.Nonempty := Finset.card_pos.mp (by rw [hS]; omega)
  have hx : interAll S = ∅ := by
    apply Finset.ext; intro x
    constructor
    · intro hx'
      have hxA : x ∈ A := (mem_interAll hnon).1 hx' A hA
      have hxB : x ∈ B := (mem_interAll hnon).1 hx' B hB
      have hxAB : x ∈ A ∩ B := by simp [hxA, hxB]
      have hempty : x ∈ (∅ : Finset α) := by simpa using (hdisj A hA B hB hAB).le_bot hxAB
      exact (by simpa using hempty)
    · intro hx'; simp at hx'
  rw [hx]
  exact (disjoint_iff_inter_eq_empty.mp (hdisj A hA B hB hAB))



/-- A family containing an `r`-sunflower, expressed with subset. -/
def HasSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ S : Finset (Finset α), S ⊆ F ∧ IsSunflower S r

/-- sunflower-free -/
def SunflowerFree (F : Finset (Finset α)) (r : ℕ) : Prop := ¬ HasSunflower F r

/-- Subfamilies of sunflower-free families are sunflower-free. -/
lemma SunflowerFree.of_subset {F G : Finset (Finset α)} {r : ℕ} (hGF : G ⊆ F)
    (hfree : SunflowerFree F r) : SunflowerFree G r := by
  intro h
  rcases h with ⟨S, hSF, hSun⟩
  exact hfree ⟨S, subset_trans hSF hGF, hSun⟩

end Submission.Sun
