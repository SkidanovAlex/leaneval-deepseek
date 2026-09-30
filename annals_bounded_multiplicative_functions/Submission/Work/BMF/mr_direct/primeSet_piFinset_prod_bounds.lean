import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

/-- Every tuple of primes drawn from the dyadic prime set `primeSet P` has a product that is
`≥ 1`, at least `⌈P⌉₊ ^ k` and at most `⌊2 * P⌋₊ ^ k`. -/
theorem primeSet_piFinset_prod_bounds (P : ℝ) (k : ℕ) {f : Fin k → ℕ}
    (hf : f ∈ Fintype.piFinset (fun _ : Fin k => Work.BMF.mr_direct.primePoly.primeSet P)) :
    1 ≤ ∏ j, f j ∧ ⌈P⌉₊ ^ k ≤ ∏ j, f j ∧ ∏ j, f j ≤ ⌊2 * P⌋₊ ^ k := by
  have hmem : ∀ j, f j ∈ Work.BMF.mr_direct.primePoly.primeSet P :=
    fun j => (Fintype.mem_piFinset.mp hf) j
  have hprime : ∀ j, Nat.Prime (f j) := by
    intro j; exact (Finset.mem_filter.mp (hmem j)).2
  have hlo : ∀ j, ⌈P⌉₊ ≤ f j := by
    intro j; exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem j)).1).1
  have hhi : ∀ j, f j ≤ ⌊2 * P⌋₊ := by
    intro j; exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem j)).1).2
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.one_le_prod (fun j _ => (hprime j).one_le)
  · calc ⌈P⌉₊ ^ k = ∏ _j : Fin k, ⌈P⌉₊ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin k, f j := Finset.prod_le_prod (fun j _ => hlo j)
  · calc ∏ j : Fin k, f j ≤ ∏ _j : Fin k, ⌊2 * P⌋₊ :=
          Finset.prod_le_prod (fun j _ => hhi j)
      _ = ⌊2 * P⌋₊ ^ k := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Work.BMF.mr_direct
