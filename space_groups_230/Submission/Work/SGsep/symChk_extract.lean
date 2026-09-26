import Mathlib
import Submission.Work.SGsep.symChk_defs
import Submission.Work.SGsep.sym_prep

namespace Work.SGsep

/-- Elementary `zipWith` extraction: if `(List.zipWith f L M).all id = true` and `j` is an index
of both lists, then the corresponding entry is `true`. -/
theorem zipWith_all_getElem {α β : Type*} {f : α → β → Bool} {L : List α} {M : List β}
    (h : (List.zipWith f L M).all id = true) {j : ℕ} (hjL : j < L.length)
    (hjM : j < M.length) : f L[j] M[j] = true := by
  have hlen : j < (List.zipWith f L M).length := by
    rw [List.length_zipWith]; exact lt_min hjL hjM
  have hmem : (List.zipWith f L M)[j] ∈ List.zipWith f L M := List.getElem_mem hlen
  have hh := (List.all_eq_true.mp h) _ hmem
  rw [List.getElem_zipWith] at hh
  exact hh

/-- Extraction of the `no`-witness from `Work.SG.Data.SymCert.chk`: if the check passes with
`a.o ≤ 48`, then `1 ≤ a.o` and for every prime `p ∣ a.o` there is a vector `u ∈ a.nos`
(the entry aligned with `p` in `Work.SG.Data.primesOf a.o`) satisfying `KernCond` and `DotCond`.
The check has the shape
`decide (1 ≤ s.o) && (List.range G).all (…) && (s.nos.length == (primesOf s.o).length) &&
(List.zipWith (fun p u => u.length == 3*G && foldl … == V3.zero && foldl … % (D.n : ℤ) != 0)
(primesOf s.o) s.nos).all id`.
Recipe: unfold with `Bool.and_eq_true`, `decide_eq_true_eq`, `beq_iff_eq`, `bne_iff_ne`,
`List.all_eq_true`; get `Work.SGsep.primesOf_complete` (from `SGsep/sym_prep`) for
`p ∈ Work.SG.Data.primesOf a.o` (needs `0 < a.o`, from `1 ≤ a.o`, and `a.o ≤ 48`); pick the index
`j` with `(Work.SG.Data.primesOf a.o)[j] = p` via `List.mem_iff_getElem`; use
`List.getElem_zipWith` and `List.length_zipWith` to read the `j`-th entry of the `zipWith`
lengths agree via `s.nos.length = (primesOf s.o).length`; finish the `% (D.n : ℤ) ≠ 0` clause
with `Int.dvd_iff_emod_eq_zero`. -/
theorem symChk_extract (k : Fin 230) (a : Work.SG.Data.SymCert)
    (ha : Work.SG.Data.SymCert.chk k.val a = true)
    (p : ℕ) (hp : p.Prime) (hpd : p ∣ a.o) (hao : a.o ≤ 48) :
    1 ≤ a.o ∧ ∃ u ∈ a.nos,
      Work.SGsep.KernCond (Work.SG.Data.repArith k.val) u ∧
      Work.SGsep.DotCond (Work.SG.Data.repArith k.val) a.o p
        (fun g => (Work.SG.Data.repZ.getD k.val []).getD
          ((Work.SG.Data.repArith k.val).genIdx.getD g 0) Work.SG.Data.V3.zero) u := by
  have h := ha
  simp only [Work.SG.Data.SymCert.chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, _h2⟩, hnod⟩, hzipAll⟩ := h
  have hnod' : a.nos.length = (Work.SG.Data.primesOf a.o).length := beq_iff_eq.mp hnod
  have hprim : p ∈ Work.SG.Data.primesOf a.o :=
    Work.SGsep.primesOf_complete (by omega) hao hp hpd
  obtain ⟨j, hj, hjdest⟩ := List.mem_iff_getElem.mp hprim
  have hjM : j < a.nos.length := by rw [hnod']; exact hj
  refine ⟨h1, a.nos[j], List.getElem_mem hjM, ?_, ?_⟩
  · have hfp := zipWith_all_getElem hzipAll hj hjM
    rw [hjdest] at hfp
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hfp
    exact hfp.1.2
  · have hfp := zipWith_all_getElem hzipAll hj hjM
    rw [hjdest] at hfp
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hfp
    exact fun hd => hfp.2 (Int.dvd_iff_emod_eq_zero.mp hd)

end Work.SGsep
