import Mathlib
import Submission.Work.SGsep.symChk_defs
import Submission.Work.SGsep.table_facts
import Submission.Work.SG.arithRep_eq_data

namespace Work.SGsep

/-- Facts about the class table of representative `k`: it is nonempty, and every generator
`A_g` of the table occurs in `elems` at index `genIdx g` (that index being `< n`), and its matrix
lies in `arithRep (sgArith k)`.
Recipe: `Work.SG.Data.arithData_chk` (kernel `decide`) gives
`Work.SG.Data.ArithData.chk j (arithData.getD j default)` at `j = (sgArith k).val` (which is
`< 73` by construction); rewrite `Data.repArith k.val` to
`Data.arithData.getD (sgArith k).val default` with `Work.SGsep.repArith_eq_data_getD`; unfold
`Work.SG.Data.ArithData.chk` with `List.all_eq_true`, `Bool.and_eq_true`, `beq_iff_eq`; the
conjuncts `elems.length = D.n` and `elems.head? = some M3.one` give `0 < D.n`; the `genIdx`
conjunct gives the index statements; membership in `Work.SG.arithRep (Work.SG.sgArith k)`
follows from `Work.SG.arithRep_eq_data` (with `List.getElem_mem`, `List.getD_eq_getElem`). -/
theorem symChk_data (k : Fin 230) :
    0 < (Work.SG.Data.repArith k.val).n ∧
    (∀ g, g < (Work.SG.Data.repArith k.val).gens.length →
      (((Work.SG.Data.repArith k.val).gens.getD g Work.SG.Data.M3.one).toIMat ∈
          Work.SG.arithRep (Work.SG.sgArith k) ∧
       (Work.SG.Data.repArith k.val).genIdx.getD g 0 < (Work.SG.Data.repArith k.val).n ∧
       (Work.SG.Data.repArith k.val).elems.getD
           ((Work.SG.Data.repArith k.val).genIdx.getD g 0) Work.SG.Data.M3.one =
         (Work.SG.Data.repArith k.val).gens.getD g Work.SG.Data.M3.one)) := by
  -- The kernel check for the arithmetic class of `k`.
  have hchk : (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).chk
      (Work.SG.sgArith k).val = true :=
    List.all_eq_true.mp Work.SG.Data.arithData_chk (Work.SG.sgArith k).val
      (List.mem_range.mpr (Work.SG.sgArith k).isLt)
  -- Unfold the checker and turn its `Bool` conjuncts into `Prop`s.
  simp only [Work.SG.Data.ArithData.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hlen⟩, hhead⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hgen⟩, -⟩ := hchk
  -- Replace `Data.repArith k.val` by the class table of `sgArith k` (definitionally equal).
  rw [repArith_eq_data_getD k]
  refine ⟨?_, ?_⟩
  · -- Nonemptiness from `elems.length = n` and `elems.head? = some 1`.
    rcases List.head?_eq_some_iff.mp hhead with ⟨t, ht⟩
    rw [← hlen, ht]
    simp
  · intro g hg
    refine ⟨?_, (hgen g hg).1, (hgen g hg).2⟩
    -- Membership in `arithRep (sgArith k)` via the element-table description.
    rw [Work.SG.arithRep_eq_data (Work.SG.sgArith k), Set.mem_ofPred_eq]
    have hi : (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).genIdx.getD g 0
        < (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).elems.length := by
      rw [hlen]; exact (hgen g hg).1
    refine ⟨(Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).elems[
        (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).genIdx.getD g 0]'hi,
      List.getElem_mem hi, ?_⟩
    have h2 : (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).elems[
        (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).genIdx.getD g 0]'hi
        = (Work.SG.Data.arithData.getD (Work.SG.sgArith k).val default).gens.getD g
            Work.SG.Data.M3.one := by
      rw [← List.getD_eq_getElem _ Work.SG.Data.M3.one hi]
      exact (hgen g hg).2
    rw [h2]

end Work.SGsep
