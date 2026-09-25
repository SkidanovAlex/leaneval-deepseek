import Mathlib
import Submission.Work.RHContract.A.regionII.caC1_cert_defs

/-!
# Two facts about the certified prime table `ThetaBracket.CU`

`ThetaBracket.CU` is the certified table of all primes `≤ 100003`, stored as a list of
pairs `(p, b)` with `b` an integer upper bound for `10^9 · log p`.  Here we record the two
structural facts needed by the region II certificate:

* the list of first coordinates `CU.map Prod.fst` is strictly increasing
  (`List.Pairwise (· < ·)`), so the table has no repetitions and is sorted;
* every prime `p` with `2 ≤ p ≤ 100000` occurs as a first coordinate of `CU`.

Both are extracted from the already-verified chain properties `CU_lt`, `CU_gap` and
`CU_head` of `theta_bracket_finite_range` (the completeness argument
`prime_mem_of_gap` fills the gaps between consecutive table entries).
-/

namespace Work.RHContract.A.regionII

open Commons.NumberTheory.Chebyshev
open Commons.NumberTheory.Chebyshev.ThetaBracket

/-- A list of naturals whose consecutive entries (read through `zip tail`) are strictly
increasing is strictly increasing throughout. -/
lemma pairwise_lt_of_zip_lt_aux : ∀ (l : List ℕ),
    (∀ pr ∈ l.zip l.tail, pr.1 < pr.2) → l.Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    cases t with
    | nil => simp
    | cons b s =>
      rw [List.pairwise_cons]
      refine ⟨head_lt_of_zip_lt_aux a (b :: s) h, ?_⟩
      exact ih (fun pr hp => h pr (zip_subset_cons a (b :: s) hp))

theorem caC1_cert_CU_facts :
    (Commons.NumberTheory.Chebyshev.ThetaBracket.CU.map Prod.fst).Pairwise (· < ·) ∧
      (∀ p : ℕ, 2 ≤ p → p ≤ 100000 → Nat.Prime p →
        p ∈ Commons.NumberTheory.Chebyshev.ThetaBracket.CU.map Prod.fst) := by
  constructor
  · exact pairwise_lt_of_zip_lt_aux (CU.map Prod.fst) CU_lt
  · intro p hp2 hpN hpp
    have hhead2 : (CU.map Prod.fst).head? = some 2 := by rw [List.head?_map, CU_head]; rfl
    refine prime_mem_of_gap (CU.map Prod.fst) CU_lt CU_gap hhead2 p ?_ ?_ hpp
    · exact hpp.two_le
    · exact ⟨100003,
        by rw [List.mem_map]; exact ⟨sentCU, List.mem_append_right _ (by simp), by simp [sentCU]⟩,
        by omega⟩

end Work.RHContract.A.regionII
