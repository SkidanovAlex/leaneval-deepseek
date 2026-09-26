import Mathlib
import Submission.Work.SG.ApplyBDefs

/-!
# `Work.SG.applyB_range`

`Data.applyB B y` is `∑ᵢ Bᵢ *ᵥ (blocks y)ᵢ`, a right fold over `List.zipWith Data.M3.mulV B
(Data.blocks y)`, while `appV k F y` is the corresponding `Finset`-sum over `List.range k`.
This file proves that the two agree when the matrix list is `(List.range k).map F` and `k` does
not exceed the number of blocks of `y` (so that `zipWith` is not truncated).

The proof splits into two elementary ingredients, both proved here:

* `applyB_range_zipWith_sum` : for `l₁.length ≤ l₂.length` a `List.sum` of a `List.zipWith` is
  the `Finset.sum` over `List.range l₁.length` of the pointwise values (the `getD` defaults are
  irrelevant because every index occurring is in range);
* `applyB_range_foldr_toFun` : the `c`-th coordinate of a fold of `Data.V3.add` is the sum of the
  `c`-th coordinates;

and then `applyB_range_blocks_gen`, the statement for an arbitrary matrix list `B` whose length is
at most the number of blocks.
-/

namespace Work.SG

/-! ## Two elementary `List` facts -/

/-- A `List.zipWith` evaluated with `List.sum` equals the corresponding `Finset.sum` over the
range of the (shorter) first list, read with `getD`. -/
theorem applyB_range_zipWith_sum {α β : Type*} (f : α → β → ℤ) (d₁ : α) (d₂ : β)
    (l₁ : List α) (l₂ : List β) (h : l₁.length ≤ l₂.length) :
    (List.zipWith f l₁ l₂).sum
      = ∑ i ∈ Finset.range l₁.length, f (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      rw [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
        List.getD_cons_zero, List.getD_cons_zero]
      simp only [List.getD_cons_succ]
      rw [ih l₂ (by simpa using h)]
      ring

/-- The `c`-th coordinate of a right fold of `Data.V3.add` is the sum of the coordinates. -/
theorem applyB_range_foldr_toFun (l : List Data.V3) (c : Fin 3) :
    (l.foldr Data.V3.add Data.V3.zero).toFun c = (l.map (fun v => v.toFun c)).sum := by
  induction l with
  | nil => simp [toFun_zero]
  | cons a l ih =>
    rw [List.foldr_cons, toFun_add, Pi.add_apply, ih, List.map_cons, List.sum_cons]

/-! ## `applyB` as a `Finset` sum -/

/-- `Data.applyB` of a matrix list `B` whose length does not exceed the number of blocks of `y` is
the `Finset`-sum of `mvf` over `List.range B.length`. -/
theorem applyB_range_blocks_gen (B : List Data.M3) (y : List ℤ)
    (hB : B.length ≤ (Data.blocks y).length) :
    (Data.applyB B y).toFun
      = ∑ g ∈ Finset.range B.length,
          mvf (B.getD g Data.M3.zero) ((Data.blocks y).getD g Data.V3.zero).toFun := by
  funext c
  rw [Finset.sum_apply, Data.applyB, applyB_range_foldr_toFun, List.map_zipWith]
  rw [applyB_range_zipWith_sum (fun A v => (Data.M3.mulV A v).toFun c) Data.M3.zero
    Data.V3.zero B (Data.blocks y) hB]
  exact Finset.sum_congr rfl fun g _ => by rw [mvf_eq_mulV]

theorem applyB_range (k : ℕ) (F : ℕ → Work.SG.Data.M3) (y : List ℤ)
    (hk : k ≤ (Work.SG.Data.blocks y).length) :
    (Work.SG.Data.applyB ((List.range k).map F) y).toFun = Work.SG.appV k F y := by
  have hB : ((List.range k).map F).length ≤ (Data.blocks y).length := by
    rw [List.length_map, List.length_range]; exact hk
  rw [applyB_range_blocks_gen ((List.range k).map F) y hB, appV, List.length_map,
    List.length_range]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : g < k := Finset.mem_range.mp hg
  have hgl : g < ((List.range k).map F).length := by
    rw [List.length_map, List.length_range]; exact hg'
  rw [List.getD_eq_getElem _ _ hgl, List.getElem_map,
    List.getElem_range (by rw [List.length_range]; exact hg')]

end Work.SG
