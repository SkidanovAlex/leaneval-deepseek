import Mathlib
import Submission.Work.PTCert.rowHelp
import Submission.Work.PTCert.nSem

namespace Work.PTCert

/-
Goal: the row label `lab0` of a code of `B₂` is one of the 18 rows.

`lab0 eM repInfoT z = cG repInfoT ((eG eM z - 1) / 32) / 128`
(`Submission/PTCert/KernelShared.lean`).  Ingredients, all already proved/importable:
* `Work.PTCert.rinfo_div (t) (ht : t < 611) : cG repInfoT t / 128 < 18` (in `rowHelp`);
* `Work.PTCert.NSemAux.mem_chunks {z} (hz : z ∈ eAll) : z ∈ eC0 ∨ … ∨ z ∈ eC7`
  and `Work.PTCert.NSemAux.chunk_data (l) (hc : eChunkOK cmT eM nT repT l = true)
   (hb : eBoundOK eM l = true) : ∀ z ∈ l, 1 ≤ em z ∧ (em z - 1)/32 < 611 ∧ …`
  (in `Submission.Work.PTCert.nSem`), instantiated at `l = eCj` with the checks
  `C.echunk_ok j`, `C.ebound_ok j` (`Checks/E.lean`, `Checks/X.lean`).
So: split `z ∈ eAll` into the eight chunks, get `(em z - 1)/32 < 611`, then `rinfo_div`.

Instead of splitting the 8-fold disjunction `mem_chunks` by hand, we observe that the relevant
data (`eBoundOK`) is a `allL`-predicate, hence distributes over list concatenation: this gives
`eBoundOK eM eAll = true` directly from the eight kernel checks `C.ebound_ok j`, and then
`NSemAux.allL_iff` extracts the bound `(eG eM z - 1)/32 < 611` for every `z ∈ eAll`.
-/
open Submission.PTCert Submission.PTCert.D

namespace Lab0Aux

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-- `allL` distributes over concatenation. -/
lemma allL_append (l m : List ℕ) (p : ℕ → Bool) :
    allL (l ++ m) p = (allL l p && allL m p) := by
  induction l with
  | nil => simp [NSemAux.allL_nil]
  | cons a t ih => simp only [List.cons_append, NSemAux.allL_cons, ih, Bool.and_assoc]

/-- `eBoundOK` distributes over concatenation. -/
lemma eBoundOK_append (l m : List ℕ) :
    eBoundOK eM (l ++ m) = (eBoundOK eM l && eBoundOK eM m) := by
  simp only [eBoundOK, allL_append]

/-- The bound check holds on the whole `E`-order list, because it holds on each of the eight
chunks (kernel checks `C.ebound_ok0 … C.ebound_ok7`). -/
lemma eBoundOK_eAll : eBoundOK eM eAll = true := by
  rw [NSemAux.eAll_chunks]
  simp only [eBoundOK_append, C.ebound_ok0, C.ebound_ok1, C.ebound_ok2, C.ebound_ok3,
    C.ebound_ok4, C.ebound_ok5, C.ebound_ok6, C.ebound_ok7, Bool.and_true]

end Lab0Aux

/-- The N-representative number `(eG eM z - 1) / 32` of a code `z ∈ eAll` is `< 611`. -/
theorem lab0Lt_aux {z : ℕ} (hz : z ∈ eAll) : (eG eM z - 1) / 32 < 611 := by
  have h : allL eAll (fun z => Nat.blt ((eG eM z - 1) / 32) 611) = true := by
    simpa only [eBoundOK] using Lab0Aux.eBoundOK_eAll
  exact Nat.blt_eq.mp ((NSemAux.allL_iff eAll _).mp h z hz)

theorem lab0Lt : ∀ z ∈ eAll, lab0 eM repInfoT z < 18 := by
  intro z hz
  exact rinfo_div ((eG eM z - 1) / 32) (lab0Lt_aux hz)

end Work.PTCert
