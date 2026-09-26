import Mathlib
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — `cert1Ldl4`: the LDL data of base character `4` of the `C1` certificate

We exhibit the witnesses `Cs`, `Ws`, `segs`, `accs` of `LdlData D1.rowTs 4`:

* `Cs := D1.Cs4`, `Ws := D1.Ws4` — the factor-row / weight tables of the certificate;
* `segs := [[0,1,2,3,4,5]]` — the single index segment of the kernel chain theorem `C1K.ldl_ok4_0`;
* `accs j` — the `j`-th accumulator witness `D1.acc4_{j}` (junk `[]` beyond the chain).

The four clauses of `LdlData` are the small structural facts `flatten4`, `accZero4`,
the chain `chain4` (the single kernel theorem), and the shape clause `shape4` obtained
from `C1K.ldldata_ok4` through `Work.PTCert.ldlDataOK_iff`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section
namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K
open scoped BigOperators

private def segs4 : List (List ℕ) := [[0,1,2,3,4,5]]

private def accL4 : List (List (List ℤ)) := [acc4_0, acc4_1]

private def accs4 : ℕ → List (List ℤ) := fun j => accL4.getD j []

private lemma chain4 :
    ∀ j < segs4.length,
      ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk 4) (ksL.getD 4 [])
        (ysL.getD 4 []) Cs4 Ws4 (segs4.getD j []) (accs4 j) =
        some (accs4 (j + 1)) := by
  intro j hj
  have hj' : j < 1 := hj
  interval_cases j
  · exact ldl_ok4_0

private lemma flatten4 : segs4.flatten = List.range (nK 4) := by decide +kernel

private lemma accZero4 : accs4 0 = List.replicate 4 (List.replicate (nK 4) 0) := by
  decide +kernel

private lemma shape4 :
    ∀ ψ < 4, (Ws4.getD ψ []).length = nK 4 ∧ (Cs4.getD ψ []).length = nK 4 ∧
      ∀ i < nK 4, 0 < (Ws4.getD ψ []).getD i 1 ∧
        ((Cs4.getD ψ []).getD i []).length ≤ i + 1 :=
  (Work.PTCert.ldlDataOK_iff Cs4 Ws4 6).mp ldldata_ok4

/-- **The LDL data of base character `4` of the `C1` certificate.** -/
theorem cert1Ldl4 : Submission.PTCert.G.LdlData Submission.PTCert.D1.rowTs 4 :=
  ⟨Cs4, Ws4, segs4, accs4, flatten4, accZero4, chain4, shape4⟩

end Work.PTCert

end
