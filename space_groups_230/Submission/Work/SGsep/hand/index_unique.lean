import Mathlib
import Submission.Work.SGsep.hand.HandDefs2
import Submission.Work.SGsep.table_facts

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-- A list without duplicates assigns to each of its elements exactly one index, read
through `List.getD` (the default value is never used, since the index is `< length`). -/
private theorem existsUnique_getD {α : Type*} {l : List α} (hnd : l.Nodup) {d a : α}
    (ha : a ∈ l) : ∃! i : Nat, i < l.length ∧ l.getD i d = a := by
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  refine ⟨i, ⟨hi, ?_⟩, ?_⟩
  · rw [List.getD_eq_getElem l d hi, hia]
  · intro j hj
    have hj' : l[j] = a := by rw [← List.getD_eq_getElem l d hj.1, hj.2]
    exact (List.Nodup.getElem_inj_iff hnd).mp (by rw [hj', hia])

/-- Every element of the point group of representative `k` occurs at exactly one table index. -/
theorem index_unique {k : Fin 230} {A : IMat} (hA : A ∈ arithRep (sgArith k)) :
    ∃! i : Nat, i < (repArith k.val).n ∧ Ah k i = A := by
  -- Write `A` as `e.toIMat` for an entry `e` of the stored element list.
  have hmem := hA
  rw [Work.SG.arithRep_eq_data (sgArith k), Set.mem_ofPred_eq] at hmem
  obtain ⟨e, he, hAe⟩ := hmem
  -- The stored table is duplicate-free and has length `n`.
  have hspec := of_decide_eq_true (List.all_eq_true.mp arithData_elems_nodup_len (sgArith k).val
    ((List.mem_range).mpr (sgArith k).isLt))
  obtain ⟨hnd0, hlen0⟩ := hspec
  rw [← repArith_eq_data_getD k] at hnd0 hlen0 he
  obtain ⟨i, hi, huniq⟩ := existsUnique_getD hnd0 he
  refine ⟨i, ⟨?_, ?_⟩, ?_⟩
  · rw [← hlen0]; exact hi.1
  · have hA3 : A3 k i = e := hi.2
    show (A3 k i).toIMat = A
    rw [hA3, hAe]
  · intro j hj
    have hj' : (repArith k.val).elems.getD j M3.one = e := by
      have : (A3 k j).toIMat = e.toIMat := by
        show Ah k j = e.toIMat
        rw [hj.2, hAe]
      exact M3.toIMat_injective this
    exact huniq j ⟨by rw [hlen0]; exact hj.1, hj'⟩

end Work.SGsep.hand
