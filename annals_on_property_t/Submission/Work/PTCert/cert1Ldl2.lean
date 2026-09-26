import Mathlib
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — `cert1Ldl2`: the LDL data of the `C1` certificate for the base character `k = 2`

We exhibit the witnesses `Cs`, `Ws`, `segs`, `accs` of `LdlData D1.rowTs 2`:

* `Cs := D1.Cs2`, `Ws := D1.Ws2` are the factor-row / weight tables of the certificate `C1`;
* `segs` collects the index segments of the kernel chain theorems `C1K.ldl_ok2_{j}` in order;
* `accs j` is the `j`-th accumulator witness `D1.acc2_{j}` (junk `[]` beyond the chain).

The four clauses of `LdlData` are then the small structural facts `flatten2`, `accZero2`,
the chain `chain2` (one case per kernel theorem), and the shape clause `shape2` obtained
from `C1K.ldldata_ok2` through `Work.PTCert.ldlDataOK_iff`.

This mirrors `Submission/Work/PTCert/Cert2/ldlDataC2.lean` (the `C2` data).
-/

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section
namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K
open scoped BigOperators

/-! ### Base character `k = 2` -/

private def segs2 : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7], [8,9,10,11,12,13], [14,15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29,30], [31,32,33,34,35,36], [37,38,39,40,41,42,43], [44,45,46,47,48,49,50,51,52,53,54,55,56,57,58]]

private def accL2 : List (List (List ℤ)) :=
  [acc2_0, acc2_1, acc2_2, acc2_3, acc2_4, acc2_5, acc2_6, acc2_7, acc2_8]

private def accs2 : ℕ → List (List ℤ) := fun j => accL2.getD j []

private lemma chain2 :
    ∀ j < segs2.length,
      ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk 2) (ksL.getD 2 [])
        (ysL.getD 2 []) Cs2 Ws2 (segs2.getD j []) (accs2 j) =
        some (accs2 (j + 1)) := by
  intro j hj
  have hj' : j < 8 := hj
  interval_cases j
  · exact ldl_ok2_0
  · exact ldl_ok2_1
  · exact ldl_ok2_2
  · exact ldl_ok2_3
  · exact ldl_ok2_4
  · exact ldl_ok2_5
  · exact ldl_ok2_6
  · exact ldl_ok2_7

private lemma flatten2 : segs2.flatten = List.range (nK 2) := by decide +kernel

private lemma accZero2 : accs2 0 = List.replicate 4 (List.replicate (nK 2) 0) := by
  decide +kernel

private lemma shape2 :
    ∀ ψ < 4, (Ws2.getD ψ []).length = nK 2 ∧ (Cs2.getD ψ []).length = nK 2 ∧
      ∀ i < nK 2, 0 < (Ws2.getD ψ []).getD i 1 ∧
        ((Cs2.getD ψ []).getD i []).length ≤ i + 1 :=
  (Work.PTCert.ldlDataOK_iff Cs2 Ws2 59).mp ldldata_ok2

/-- **The LDL data of the `C1` certificate for the base character `k = 2`.** -/
theorem cert1Ldl2 : Submission.PTCert.G.LdlData Submission.PTCert.D1.rowTs 2 :=
  ⟨Cs2, Ws2, segs2, accs2, flatten2, accZero2, chain2, shape2⟩

end Work.PTCert
