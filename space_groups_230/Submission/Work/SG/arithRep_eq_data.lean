import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.Data.ArithCheck
import Submission.Work.SG.arithDefs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md and Submission/Work/SG/Data/DATA.md first (orchestrator design + certificate data). Shared defs: Submission/Work/SG/Defs.lean (namespace Work.SG); data modules Submission/Work/SG/Data/* — do NOT edit any of them. Certificate checks use kernel decide only (no native_decide). Siblings run in parallel.
-/

namespace Work.SG

/-- Bridge: the flat row-major encoding `Data.M3.toList`, read back as a matrix by `imatOfList`,
is the matrix `Data.M3.toIMat`. -/
theorem imatOfList_toList (A : Data.M3) : imatOfList (Data.M3.toList A) = A.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Two kernel checks comparing the two element tables

`arithData[j].elems` (the BFS table of `Data.ArithTab`, used by the whole `Sub`-table pipeline)
and `ELcodes[j]` (the element list of `arithDefs`, already certified to have image `arithRep j`)
list the same finite set of matrices, in two different encodings. Both inclusions are finite
checks on flat integer data. -/

/-- Every element of the BFS table is one of the `dec9`-decoded codes of `ELcodes`. -/
theorem arithData_chk_to_EL : (List.range 73).all (fun j =>
    (Data.arithData.getD j default).elems.all (fun e =>
      (ELcodes.getD j []).any (fun c => decide (Data.M3.toList e = dec9 c)))) = true := by
  decide

/-- Conversely, every code of `ELcodes` decodes to an element of the BFS table. -/
theorem EL_chk_to_arithData : (List.range 73).all (fun j =>
    (ELcodes.getD j []).all (fun c =>
      (Data.arithData.getD j default).elems.any (fun e => decide (Data.M3.toList e = dec9 c)))) = true := by
  decide

/-- Unpacked form of `arithData_chk_to_EL`. -/
theorem arithData_to_EL (j : Fin 73) :
    ∀ e ∈ (Data.arithData.getD j.val default).elems,
      ∃ c ∈ ELcodes.getD j.val [], Data.M3.toList e = dec9 c := by
  intro e he
  have h := List.all_eq_true.mp arithData_chk_to_EL j.val (List.mem_range.mpr j.isLt)
  obtain ⟨c, hc, hc'⟩ := List.any_eq_true.mp (List.all_eq_true.mp h e he)
  exact ⟨c, hc, decide_eq_true_eq.mp hc'⟩

/-- Unpacked form of `EL_chk_to_arithData`. -/
theorem EL_to_arithData (j : Fin 73) :
    ∀ c ∈ ELcodes.getD j.val [], ∃ e ∈ (Data.arithData.getD j.val default).elems,
      Data.M3.toList e = dec9 c := by
  intro c hc
  have h := List.all_eq_true.mp EL_chk_to_arithData j.val (List.mem_range.mpr j.isLt)
  obtain ⟨e, he, he'⟩ := List.any_eq_true.mp (List.all_eq_true.mp h c hc)
  exact ⟨e, he, decide_eq_true_eq.mp he'⟩

/-- The class-`j` arithmetic representative is exactly the element table `arithData[j]`
(bridge from the `sgClose` definition to the kernel-checked table). -/
theorem arithRep_eq_data (j : Fin 73) :
    arithRep j = {A | ∃ e ∈ (Data.arithData.getD j default).elems, A = e.toIMat} := by
  ext A
  rw [mem_arithRep j A, mem_finSet_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c0, hc0, hc0'⟩ := List.mem_map.mp hc
    obtain ⟨e, he, he'⟩ := EL_to_arithData j c0 hc0
    exact ⟨e, he, by rw [← imatOfList_toList e, he', hc0']⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨c, hc, hc'⟩ := arithData_to_EL j e he
    exact ⟨dec9 c, List.mem_map.mpr ⟨c, hc, rfl⟩, by rw [← imatOfList_toList e, hc']⟩

end Work.SG
