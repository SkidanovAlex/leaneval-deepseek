import Mathlib
import Submission.Work.LT.lr_Mpar_defs

/-! `dispCount` splits as the sum of the `ℓ¹`-masses of the label-class indicators `sA`, `sB`.

`dispCount A B W` counts the disputed A-edges (indices `Fin 2 × G × Fin Δ`) and the disputed
B-edges, while `∑ i, l1 (sA A W i)` counts the disputed A-edges grouped by their *label* `i`.  The
two are the same by the elementary counting identity `key_disp`: for any predicate `P a b c`, the
cardinality of `{(a,b,c) | P a b c}` equals the sum over `c` of the cardinalities of the fibres. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

/-- Counting identity: the number of triples satisfying `P` equals the sum over `c` of the number
of pairs `(a,b)` with `P a b c` written as a sum of `0/1` indicators. -/
lemma key_disp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α → β → γ → Prop) :
    (∑ c : γ, ∑ a : α, ∑ b : β, (if P a b c then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun p : α × β × γ => P p.1 p.2.1 p.2.2)).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

theorem lr_Mpar_disp_decomp {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    (dispCount A B W : ℝ) = (∑ i : Fin Δ, l1 (sA A W i)) + (∑ j : Fin Δ, l1 (sB B W j)) := by
  rw [dispCount]
  push_cast
  rw [← key_disp (disputeA A W), ← key_disp (disputeB B W)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [l1, Fintype.sum_prod_type]
    simp only [sA]
  · apply Finset.sum_congr rfl
    intro j _
    rw [l1, Fintype.sum_prod_type]
    simp only [sB]

end Work.LT
