import Mathlib
import Submission.Work.MainP.p52helpers

namespace Work.MainP

/-! ## `S = ∏ sᵢ ≤ T = ∏ tᵢ` for `ResParams`

`HvdH.ResParams p α ss ts` says in particular that `ss` and `ts` both have length `D` and that
`ssᵢ < tsᵢ` for every `i < D` (in fact `2 ≤ ssᵢ`).  Hence each factor of `ss.prod` is at most the
corresponding factor of `ts.prod`, and products of equally long lists compare pointwise.

This is the easy half of the size window of Lemma 4.12 / Prop 5.2; the companion bound
`T < 2S` needs the numerical window and is proved in `Work.MainP.prodWindow`. -/

/-- Two natural-number lists of the same length whose entries compare pointwise (read off with
`getD`) have comparable products. -/
lemma prod_le_prod_of_getD {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 ≤ l₂.getD i 0) : l₁.prod ≤ l₂.prod := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp
    | cons b l₂' => simp at hlen
  | cons a l₁' ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b l₂' =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [List.prod_cons, List.prod_cons]
      refine Nat.mul_le_mul ?_ (ih hlen ?_)
      · simpa using h 0 (by simp)
      · intro i hi
        have hlt : i + 1 < (a :: l₁').length := by simp [hi]
        simpa using h (i + 1) hlt

theorem ss_prod_le_ts_prod {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) :
    ss.prod ≤ ts.prod := by
  obtain ⟨hsslen, htslen, -, -, -, h⟩ := hRes
  refine prod_le_prod_of_getD (by omega) fun i hi => ?_
  exact le_of_lt (h i (by omega)).2.1

end Work.MainP
