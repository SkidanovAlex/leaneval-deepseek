import Mathlib
import Submission.Work.PTCert.cert1Aux

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section
namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K
open scoped BigOperators

/-!
# PTCert — `cert1Ldl1`: the LDL data of the C1 certificate at base character `k = 1`

Witnesses of `LdlData D1.rowTs 1`:

* `Cs := Cs1`, `Ws := Ws1` — the factor-row / weight tables of the C1 certificate;
* `segs1` collects the index segments of the kernel chain theorems `C1K.ldl_ok1_{j}` in order;
* `accs1 j := accL1.getD j []` is the `j`-th accumulator witness `D1.acc1_{j}`.

The four clauses of `LdlData` are `flatten1`, `accZero1`, the chain `chain1`
(one case per kernel theorem) and the shape clause `shape1`, the latter obtained from
`C1K.ldldata_ok1` through `Work.PTCert.ldlDataOK_iff`.
-/

/-- The index segments of the 24 kernel chain steps `ldl_ok1_0 … ldl_ok1_23`. -/
private def segs1 : List (List ℕ) :=
  [[0,1,2,3,4,5], [6,7,8,9], [10,11,12,13], [14,15,16], [17,18,19], [20,21,22], [23,24,25],
   [26,27,28], [29,30,31], [32,33,34], [35,36,37], [38,39,40], [41,42,43], [44,45,46],
   [47,48,49], [50,51,52], [53,54,55], [56,57,58], [59,60,61], [62,63,64,65], [66,67,68,69],
   [70,71,72,73,74], [75,76,77,78,79,80,81,82,83], [84,85,86,87]]

/-- The accumulator witnesses, in chain order. -/
private def accL1 : List (List (List ℤ)) :=
  [acc1_0, acc1_1, acc1_2, acc1_3, acc1_4, acc1_5, acc1_6, acc1_7, acc1_8, acc1_9, acc1_10,
   acc1_11, acc1_12, acc1_13, acc1_14, acc1_15, acc1_16, acc1_17, acc1_18, acc1_19, acc1_20,
   acc1_21, acc1_22, acc1_23, acc1_24]

/-- The accumulator function `j ↦ acc1_{j}` (junk `[]` beyond the chain). -/
private def accs1 : ℕ → List (List ℤ) := fun j => accL1.getD j []

private lemma chain1 :
    ∀ j < segs1.length,
      ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk 1) (ksL.getD 1 [])
        (ysL.getD 1 []) Cs1 Ws1 (segs1.getD j []) (accs1 j) =
        some (accs1 (j + 1)) := by
  intro j hj
  have hj' : j < 24 := hj
  interval_cases j
  · exact ldl_ok1_0
  · exact ldl_ok1_1
  · exact ldl_ok1_2
  · exact ldl_ok1_3
  · exact ldl_ok1_4
  · exact ldl_ok1_5
  · exact ldl_ok1_6
  · exact ldl_ok1_7
  · exact ldl_ok1_8
  · exact ldl_ok1_9
  · exact ldl_ok1_10
  · exact ldl_ok1_11
  · exact ldl_ok1_12
  · exact ldl_ok1_13
  · exact ldl_ok1_14
  · exact ldl_ok1_15
  · exact ldl_ok1_16
  · exact ldl_ok1_17
  · exact ldl_ok1_18
  · exact ldl_ok1_19
  · exact ldl_ok1_20
  · exact ldl_ok1_21
  · exact ldl_ok1_22
  · exact ldl_ok1_23

private lemma flatten1 : segs1.flatten = List.range (nK 1) := by decide +kernel

private lemma accZero1 : accs1 0 = List.replicate 4 (List.replicate (nK 1) 0) := by
  decide +kernel

private lemma shape1 :
    ∀ ψ < 4, (Ws1.getD ψ []).length = nK 1 ∧ (Cs1.getD ψ []).length = nK 1 ∧
      ∀ i < nK 1, 0 < (Ws1.getD ψ []).getD i 1 ∧
        ((Cs1.getD ψ []).getD i []).length ≤ i + 1 :=
  (ldlDataOK_iff Cs1 Ws1 88).mp ldldata_ok1

theorem cert1Ldl1 : Submission.PTCert.G.LdlData Submission.PTCert.D1.rowTs 1 :=
  ⟨Cs1, Ws1, segs1, accs1, flatten1, accZero1, chain1, shape1⟩

end Work.PTCert
end
