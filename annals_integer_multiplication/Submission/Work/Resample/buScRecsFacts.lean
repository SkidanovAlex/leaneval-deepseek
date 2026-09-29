import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample

namespace Work.Resample
open HvdH

/-! ## list-level helpers

`buScRecs` is the `zipWith` of two lists of length `s`, namely `buScKeys s t` (of length `s`) and
`d.map cfxVal` (of length `d.length = s`). The two basic facts about `getD` on `List.ofFn` and on
`List.zipWith` turn it into the `ofFn` normal form `buScRecs'`. -/

/-- `getD` of `List.ofFn` at an index inside the range. -/
theorem buSc_getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h]
  rfl

/-- `zipWith` of two lists of the same length `n` is the `ofFn` of the pointwise `getD`. -/
theorem buSc_zipWith_eq_ofFn {α β γ : Type} (f : α → β → γ) {n : ℕ} (a : List α) (b : List β)
    (ha : a.length = n) (hb : b.length = n) (da : α) (db : β) :
    List.zipWith f a b = List.ofFn (fun i : Fin n => f (a.getD (i:ℕ) da) (b.getD (i:ℕ) db)) := by
  apply List.ext_getElem
  · rw [List.length_zipWith, ha, hb, Nat.min_self, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_eq_getD da, List.getElem_eq_getD db]

/-- `buScRecs` in `ofFn` normal form. -/
theorem buScRecs_eq_ofFn (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    buScRecs s t d = List.ofFn (fun i : Fin s =>
      Val.cons (Val.int (((egKeyS s t (i:ℕ) : ℕ) : ℤ))) (cfxVal (d.getD (i:ℕ) (0,0)))) := by
  rw [buScRecs, buScKeys, List.zipWith_map_left]
  rw [buSc_zipWith_eq_ofFn (f := fun k v => Val.cons (Val.int k) v) (n := s) (da := (0:ℤ))
      (db := cfxVal (0,0)) (ha := List.length_ofFn) (hb := by simp [hd])]
  rw [List.ofFn_inj]
  funext i
  rw [buSc_getD_ofFn _ (0:ℤ) (i:ℕ) i.isLt, List.getD_map]

/-- List-level normal form of the record list of the scaling stage. -/
theorem buScRecsFacts (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    buScRecs s t d = buScRecs' s t d ∧
    (∀ i < s, (buScRecs s t d).getD i Val.nil =
      Val.cons (Val.int (((egKeyS s t i : ℕ) : ℤ))) (cfxVal (d.getD i (0, 0)))) ∧
    (buScRecs s t d).map pairKey = List.ofFn (fun i : Fin s => ((egKeyS s t (i : ℕ) : ℕ) : ℤ)) ∧
    (buScRecs s t d).length = s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [buScRecs_eq_ofFn s t d hd]; rfl
  · intro i hi
    rw [buScRecs_eq_ofFn s t d hd, buSc_getD_ofFn _ Val.nil i hi]
  · rw [buScRecs_eq_ofFn s t d hd, List.map_ofFn, List.ofFn_inj]
    funext i
    rfl
  · rw [buScRecs, List.length_zipWith, buScKeys_length, List.length_map, hd, Nat.min_self]

end Work.Resample

open HvdH

/-- List-level normal form of the record list of the scaling stage.

(Documented name of the lemma above, which the file template placed in the duplicated namespace
`Work.Resample.Work.Resample`.) -/
theorem buScRecsFacts (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    buScRecs s t d = buScRecs' s t d ∧
    (∀ i < s, (buScRecs s t d).getD i Val.nil =
      Val.cons (Val.int (((egKeyS s t i : ℕ) : ℤ))) (cfxVal (d.getD i (0, 0)))) ∧
    (buScRecs s t d).map pairKey = List.ofFn (fun i : Fin s => ((egKeyS s t (i : ℕ) : ℕ) : ℤ)) ∧
    (buScRecs s t d).length = s :=
  Work.Resample.Work.Resample.buScRecsFacts s t d hd

end Work.Resample
