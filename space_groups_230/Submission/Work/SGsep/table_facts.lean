import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

set_option maxRecDepth 100000

/-- The class index stored for the `k`-th representative is a valid index into the 73
arithmetic classes (a finite kernel check over the 230-entry data table). -/
theorem repClass_lt (k : Fin 230) : Data.repClass k.val < 73 := by
  have h : (List.range 230).all (fun k => decide (Data.repClass k < 73)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h k.val (List.mem_range.mpr k.isLt))

/-- The element table stored for `Data.repArith k.val` is the table of `sgArith k` (the stored
class index is already `< 73`, so the `% 73` in `sgArith` is the identity). -/
theorem repArith_eq_data_getD (k : Fin 230) :
    Data.repArith k.val = Data.arithData.getD (sgArith k).val default := by
  have hlt := repClass_lt k
  unfold Data.repArith
  congr 1
  show Data.repClass k.val = (sgArith k).val
  show Data.repClass k.val = Data.repClass k.val % 73
  exact (Nat.mod_eq_of_lt hlt).symm

/-- Every element list of `Data.arithData` has no duplicates and length `n`.  (This is the
cardinality/duplicate-free part of `Data.arithData_chk`, extracted as a standalone kernel
check so that the big `chk` conjunction need not be destructured.) -/
theorem arithData_elems_nodup_len :
    (List.range 73).all (fun j => decide ((Data.arithData.getD j default).elems.Nodup ∧
      (Data.arithData.getD j default).elems.length = (Data.arithData.getD j default).n)) = true := by
  decide

/-- The cardinality of `Tk k` is the length `n` of the stored table. -/
theorem card_Tk (k : Fin 230) : (Tk k).card = (Data.repArith k.val).n := by
  have hlt := repClass_lt k
  obtain ⟨hnodup, hlen⟩ :=
    of_decide_eq_true (List.all_eq_true.mp arithData_elems_nodup_len (Data.repClass k.val)
      (List.mem_range.mpr hlt))
  simp only [Tk, Data.repArith]
  rw [List.toFinset_card_of_nodup (List.Nodup.map Data.M3.toIMat_injective hnodup),
    List.length_map]
  exact hlen

/-- The element set of `Tk k` is exactly `arithRep (sgArith k)`. -/
theorem mem_Tk_iff (k : Fin 230) : ∀ A : IMat, A ∈ Tk k ↔ A ∈ arithRep (sgArith k) := by
  intro A
  have h2 := repArith_eq_data_getD k
  simp only [Tk, Data.repArith] at h2 ⊢
  rw [List.mem_toFinset, List.mem_map]
  rw [arithRep_eq_data (sgArith k), Set.mem_ofPred_eq, ← h2]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, h.symm⟩

/-- Table facts for representative `k`: the stored class index is a valid index, the table of
`Data.repArith` is the one of `sgArith k`, it has `n` elements, and its element set is
`arithRep (sgArith k)`.  Use `Data.arithRep_eq_data` (in the imports) and a finite `decide`
check over `Data.sgDataList` for the index bound (`Data.repClass k.val < 73`); for the
cardinality use `Data.arithData_chk` (`elems.Nodup`) and `Data.M3.toIMat_injective`. -/
theorem table_facts (k : Fin 230) :
    Data.repClass k.val < 73 ∧
    Data.repArith k.val = Data.arithData.getD (sgArith k).val default ∧
    (Tk k).card = (Data.repArith k.val).n ∧
    (∀ A : IMat, A ∈ Tk k ↔ A ∈ arithRep (sgArith k)) :=
  ⟨repClass_lt k, repArith_eq_data_getD k, card_Tk k, mem_Tk_iff k⟩

end Work.SGsep
