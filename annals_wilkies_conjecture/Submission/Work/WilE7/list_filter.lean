import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.star_deg_zero

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
## Bookkeeping for lists of `*`-pieces

Three elementary facts used when a covering list of `*`-pieces is pruned:

* pieces whose `*`-degree vanishes are trivial (empty or the whole cube), and can
  therefore be thrown away from a covering list; and after discarding all the pieces
  with vanishing degree, the remaining list is no longer than the total degree of the
  original list (used to keep the degree bookkeeping additive);
* the length of a flattened family of lists is at most the sum of the lengths;
* a point lies in the flattening of a family iff it lies in one of its members.
-/

/-- Counting helper: keeping only the entries at which `g` does not vanish, the resulting
list is no longer than the total `g`-mass of the original list. -/
lemma length_filter_ne_zero_le_sum {α : Type*} (g : α → ℕ) (L : List α) :
    (L.filter (fun P => g P ≠ 0)).length ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases h : g a = 0
    · rw [List.filter_cons_of_neg (p := fun P => decide (g P ≠ 0)) (a := a) (l := L)
        (by simp [h])]
      omega
    · rw [List.filter_cons_of_pos (p := fun P => decide (g P ≠ 0)) (a := a) (l := L)
        (by simp [h])]
      have h1 : 1 ≤ g a := Nat.one_le_iff_ne_zero.mpr h
      simp only [List.length_cons]
      omega

theorem list_filter :
    (∀ {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)),
        (∀ P ∈ L, P ∉ L.filter (fun P => P.X.deg ≠ 0) →
            P.set = ∅ ∨ P.set = WilkiesDesign.E.cubeC n) ∧
        (L.filter (fun P => P.X.deg ≠ 0)).length ≤ (L.map fun P => P.X.deg).sum) ∧
    (∀ {α : Type} {k : ℕ} (L : Fin k → List α),
        (List.flatten (List.ofFn L)).length ≤ ∑ i, (L i).length) ∧
    (∀ {α : Type} {k : ℕ} (L : Fin k → List α) (a : α),
        a ∈ List.flatten (List.ofFn L) ↔ ∃ i, a ∈ L i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n L
    refine ⟨?_, ?_⟩
    · -- a piece of the list that survives no filtering has vanishing degree,
      -- hence is trivial by `star_deg_zero`
      intro P hPL hnot
      have hdeg : P.X.deg = 0 := by
        by_contra h
        exact hnot (List.mem_filter.mpr ⟨hPL, by simpa using h⟩)
      exact star_deg_zero.1 P hdeg
    · -- the surviving pieces all have degree `≥ 1`, so the count is bounded by the mass
      simpa using length_filter_ne_zero_le_sum (fun P => P.X.deg) L
  · intro α k L
    simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    exact le_refl _
  · intro α k L a
    simp only [List.mem_flatten, List.mem_ofFn]
    constructor
    · rintro ⟨l, ⟨i, rfl⟩, ha⟩
      exact ⟨i, ha⟩
    · rintro ⟨i, ha⟩
      exact ⟨L i, ⟨i, rfl⟩, ha⟩

end Work.WilE7
