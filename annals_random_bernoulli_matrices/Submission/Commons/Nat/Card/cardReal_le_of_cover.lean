import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Nat.Card

open scoped Classical BigOperators

lemma cardReal_le_of_cover {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β)
    (P : α → Prop) (Q : β → α → Prop) (B : ℝ)
    (hcover : ∀ x ∈ s, P x → ∃ y ∈ t, Q y x)
    (hbound : ∀ y ∈ t, ((s.filter (fun x : α => Q y x)).card : ℝ) ≤ B) :
    ((s.filter (fun x : α => P x)).card : ℝ) ≤ (t.card : ℝ) * B := by
  classical
  -- S: the elements of `s` satisfying `P`;  F y: the elements of `s` related to `y` by `Q`.
  let S : Finset α := s.filter (fun x : α => P x)
  let F : β → Finset α := fun y => s.filter (fun x : α => Q y x)
  -- Every element of S lies in F y for some y ∈ t (by hcover), hence S ⊆ t.biUnion F.
  have hsub : S ⊆ t.biUnion F := by
    intro x hxS
    have hxs : x ∈ s := (Finset.mem_filter.mp (by simpa [S] using hxS)).1
    have hPx : P x := (Finset.mem_filter.mp (by simpa [S] using hxS)).2
    rcases hcover x hxs hPx with ⟨y, hyt, hQxy⟩
    exact Finset.mem_biUnion.mpr ⟨y, hyt, by simp [F, hQxy, hxs]⟩
  -- Counting: S.card ≤ (t.biUnion F).card ≤ ∑ y ∈ t, (F y).card, all as naturals.
  have hnat : S.card ≤ ∑ y ∈ t, (F y).card := by
    exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  -- Pass to reals.
  have hreal : (S.card : ℝ) ≤ ∑ y ∈ t, ((F y).card : ℝ) := by
    exact_mod_cast hnat
  -- Bound the sum termwise by B.
  have hsum : (∑ y ∈ t, ((F y).card : ℝ)) ≤ (t.card : ℝ) * B := by
    calc
      (∑ y ∈ t, ((F y).card : ℝ)) ≤ ∑ y ∈ t, B := Finset.sum_le_sum (by intro y hyt; exact hbound y hyt)
      _ = (t.card : ℝ) * B := by
        simp [Finset.sum_const, nsmul_eq_mul]
  exact le_trans hreal hsum

end Commons.Nat.Card