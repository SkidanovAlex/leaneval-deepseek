import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.SB.Assembly
import Submission.Work.Layout.sortByKeyWord
import Submission.Work.Layout.chunksOfWord
import Submission.Work.Layout.enumerateWord
import Submission.Work.Layout.replicateWord
import Submission.Work.Layout.flattenWord
import Submission.Work.SB.prologue
import Submission.Work.SB.epilogue
import Submission.Work.SB.tailWord2
import Submission.Work.SB.phase1
import Submission.Work.SB.phase3b
import Submission.Work.SB.branchWord2
import Submission.Work.SB.slicesFacts
import Submission.Work.SB.outsOfForall2
import Submission.Work.SB.kw1Word
import Submission.Work.SB.kw2Word
import Submission.Work.Layout.SB.vszSpec
import Submission.Work.SB.RawOps.vszUnslicesLe

/-!
# `LayoutLib.applyAlong` (paper Lemma 2.11)

The sort-based route (`Submission/Work/Layout/SB/`): the assembly `Work.Layout.applyAlongSort`
reduces the field to the list words, the two sort phases and the structural pieces, and the present
file discharges those hypotheses with the already-proved words.

Route (index arithmetic in `sliceIdx`/`unslicesIdx`/`keyFacts`/`tgtFacts`):
1. `enumerate` ;; (map `kw1`) ;; `sortByKey` ;; strip  — label the flat array by its slice-major key;
2. `chunksOf m` (or `replicate (A*B) nil` when `m = 0`) — the `A*B` slices in slice order;
3. run `q` on every slice (`KernelLib.mapList`), the only `A*B*c` term;
4. `flatten` ;; `enumerate` ;; (map `kw2`) ;; `sortByKey` ;; strip — relabel by the target index
   `(A*n + j)*B + b` and sort back into the `A × n × B` layout.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

theorem applyAlongWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib) : ∃ (comb : Cmd → Cmd) (K : ℕ),
    ∀ (main q : Cmd) (rest : List Val) (m n : ℕ)
      (P : List Val → Prop) (Q : List Val → List Val → Prop) (c L : ℕ),
      (∀ sl : List Val, sl.length = m → P sl → WordR main q (fun vs => vs = ofList sl :: rest)
        (fun _ out => ∃ ol, out = ofList ol :: rest ∧ ol.length = n ∧ Q sl ol ∧ ∀ y ∈ ol, vsz y ≤ L)
        (fun _ => c)) →
      ∀ (A B : ℕ) (es : List Val), es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      (∀ s < A * B, P ((slices A m B es).getD s [])) →
      WordR main (comb q) (fun vs => vs = .int A :: .int m :: .int n :: .int B :: ofList es :: rest)
        (fun _ out => ∃ outs : List (List Val), out = ofList (unslices A n B outs) :: rest ∧
          outs.length = A * B ∧ ∀ s < A * B, (outs.getD s []).length = n ∧
            Q ((slices A m B es).getD s []) (outs.getD s []))
        (fun _ => A * B * c +
          K * (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) *
            ((A * B * (m + n + 1)).size + 1) + K * (isz A + isz m + isz n + isz B)) := by
  have hSo : SortSpec := sortByKeyWord hI
  have hCh : ChunksSpec := chunksOfWord
  have hEn : EnumerateSpec := enumerateWord hI
  have hRp : ReplicateSpec := replicateWord hI
  have hKw1 : Kw1Spec := Work.SB.kw1Word hK hI
  have hP1 : Phase1Spec := Work.SB.phase1 hK hEn hSo hKw1
  have hBr : Branch2Spec := Work.SB.branchWord2_isz hK hI hCh hRp hP1
  have hPro : PrologueSpec := Work.SB.prologue hK
  have hEpi : EpilogueSpec := Work.SB.epilogue
  have hKw2 : Kw2Spec := Work.SB.kw2Word hK hI
  have hP3 : Phase3bSpec := Work.SB.phase3b hK flattenWord hEn hSo hKw2
  have hTail : TailSpec2 := Work.SB.tailWord2 hK hEpi hP3
  have hVsz : VszSpec := Work.Layout.SB.vszSpec
  have hSF : SlicesSpec :=
    ⟨fun A m B es => (Work.SB.slicesFacts A m B es).1,
     fun A m B es s hs => (Work.SB.slicesFacts A m B es).2.1 s hs,
     fun A m B es => (Work.SB.slicesFacts A m B es).2.2.2.1⟩
  have hUS : UnsliceVszSpec := Work.SB.RawOps.vszUnslicesLe
  exact applyAlongSort hK hSo hCh hEn hRp hP1 hBr hPro hEpi hP3 hTail hVsz
    (Work.SB.outsOfForall2) hSF hUS

end Work.Layout
