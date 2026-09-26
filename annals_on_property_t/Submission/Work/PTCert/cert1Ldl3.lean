import Mathlib
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — `cert1Ldl3`: the LDL data of the `C1` certificate for the base character `k = 3`

We exhibit the witnesses `Cs`, `Ws`, `segs`, `accs` of `LdlData D1.rowTs 3`:

* `Cs := D1.Cs3`, `Ws := D1.Ws3` are the factor-row / weight tables of the certificate;
* `segs` collects the index segments of the kernel chain theorems `C1K.ldl_ok3_{j}` in order;
* `accs j` is the `j`-th accumulator witness `D1.acc3_{j}` (junk `[]` beyond the chain).

The four clauses of `LdlData` are the structural facts `flatten3`, `accZero3`, the chain
`chain3` (one case per kernel theorem, `interval_cases`), and the shape clause `shape3`
obtained from `C1K.ldldata_ok3` through `Work.PTCert.ldlDataOK_iff`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section
namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K

/-- The consecutive index segments of the `k = 3` LDL chain. -/
private def segs3 : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22], [23,24,25,26]]

/-- The accumulator witnesses of the `k = 3` chain. -/
private def accL3 : List (List (List ℤ)) :=
  [acc3_0, acc3_1, acc3_2]

/-- The `j`-th accumulator of the chain (junk `[]` beyond the last step). -/
private def accs3 : ℕ → List (List ℤ) := fun j => accL3.getD j []

private lemma chain3 :
    ∀ j < segs3.length,
      ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk 3) (ksL.getD 3 [])
        (ysL.getD 3 []) Cs3 Ws3 (segs3.getD j []) (accs3 j) =
        some (accs3 (j + 1)) := by
  intro j hj
  have hj' : j < 2 := hj
  interval_cases j
  · exact ldl_ok3_0
  · exact ldl_ok3_1

private lemma flatten3 : segs3.flatten = List.range (nK 3) := by decide +kernel

private lemma accZero3 : accs3 0 = List.replicate 4 (List.replicate (nK 3) 0) := by
  decide +kernel

private lemma shape3 :
    ∀ ψ < 4, (Ws3.getD ψ []).length = nK 3 ∧ (Cs3.getD ψ []).length = nK 3 ∧
      ∀ i < nK 3, 0 < (Ws3.getD ψ []).getD i 1 ∧
        ((Cs3.getD ψ []).getD i []).length ≤ i + 1 :=
  (Work.PTCert.ldlDataOK_iff Cs3 Ws3 27).mp ldldata_ok3

theorem cert1Ldl3 : Submission.PTCert.G.LdlData Submission.PTCert.D1.rowTs 3 :=
  ⟨Cs3, Ws3, segs3, accs3, flatten3, accZero3, chain3, shape3⟩

end Work.PTCert
