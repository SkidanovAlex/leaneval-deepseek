import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.table_facts

namespace Work.SGsep

set_option maxRecDepth 100000

/-- Kernel check over the 73 arithmetic-class tables: every stored element has nonzero `ord`. -/
theorem arithData_ord_ne :
    (List.range 73).all (fun j =>
      (List.range (Work.SG.Data.arithData.getD j default).n).all (fun i =>
        decide (((Work.SG.Data.arithData.getD j default).elems.getD i
          Work.SG.Data.M3.one).ord ≠ 0))) = true := by
  decide +kernel

/-- Every element stored in an arithmetic class table `Data.arithData` has finite order `≤ 12`
in the sense of `Data.M3.ord` (so `Data.M3.ord` is the honest order of the matrix, and
`Data.normOf A = N_A`, see `Work.SGsep.PSep.ord_eq_mOrd`).  Kernel-checked finite statement over
the generated table `Data.arithData`: reduce to
`(List.range 73).all (fun j => (List.range (Data.arithData.getD j default).n).all (fun i => decide (((Data.arithData.getD j default).elems.getD i Data.M3.one).ord ≠ 0))) = true`
by `decide +kernel`, then use `Work.SGsep.arithData_elems_nodup_len` (in
`Submission/Work/SGsep/table_facts.lean`, giving `elems.length = n`) and
`Work.SGsep.repClass_lt` (`Data.repClass k.val < 73`). -/
theorem repArith_ord_ne (k : Fin 230) (i : ℕ) (hi : i < (Work.SG.Data.repArith k.val).n) :
    ((Work.SG.Data.repArith k.val).elems.getD i Work.SG.Data.M3.one).ord ≠ 0 := by
  have hlt : Work.SG.Data.repClass k.val < 73 := Work.SGsep.repClass_lt k
  have hnm : i < (Work.SG.Data.arithData.getD (Work.SG.Data.repClass k.val) default).n := hi
  have h₁ : (List.range (Work.SG.Data.arithData.getD (Work.SG.Data.repClass k.val) default).n).all
      (fun i => decide (((Work.SG.Data.arithData.getD (Work.SG.Data.repClass k.val) default).elems.getD
        i Work.SG.Data.M3.one).ord ≠ 0)) = true :=
    List.all_eq_true.mp arithData_ord_ne (Work.SG.Data.repClass k.val)
      (List.mem_range.mpr hlt)
  have h₂ := List.all_eq_true.mp h₁ i (List.mem_range.mpr hnm)
  exact of_decide_eq_true h₂

end Work.SGsep
