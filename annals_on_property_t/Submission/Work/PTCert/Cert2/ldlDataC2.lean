import Mathlib
import Submission.Work.PTCert.Checks.C2All
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — `ldlDataC2`: the LDL data of the `C2` certificate

For each base character `k ≤ 4` this file exhibits the witnesses `Cs`, `Ws`, `segs`, `accs`
of `LdlData D2.rowTs k`:

* `Cs := D2.Cs{k}`, `Ws := D2.Ws{k}` are the factor-row / weight tables of the certificate;
* `segs` collects the index segments of the kernel chain theorems `C2K.ldl_ok{k}_{j}` in order;
* `accs j` is the `j`-th accumulator witness `D2.acc{k}_{j}` (junk `[]` beyond the chain).

The four clauses of `LdlData` are then the small structural facts `flatten{k}`, `accZero{k}`,
the chain `chain{k}` (one case per kernel theorem), and the shape clause `shape{k}` obtained
from `C2K.ldldata_ok{k}` through `Work.PTCert.ldlDataOK_iff`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section
namespace Work.PTCert.Cert2

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D2
open Submission.PTCert.C2K
open scoped BigOperators

/-! ### Base character `k = 0` -/

private def segs0 : List (List ℕ) :=
  [[0,1,2], [3,4], [5,6], [7,8], [9,10], [11,12], [13], [14], [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32], [33], [34], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [47], [48], [49], [50], [51], [52], [53], [54], [55], [56], [57], [58], [59], [60], [61], [62], [63], [64], [65], [66], [67], [68], [69], [70], [71], [72], [73], [74], [75], [76], [77], [78], [79], [80], [81], [82], [83], [84], [85], [86], [87], [88], [89], [90], [91], [92], [93], [94], [95], [96], [97], [98], [99], [100], [101], [102], [103], [104], [105], [106], [107], [108], [109], [110], [111], [112], [113], [114], [115], [116], [117], [118], [119], [120], [121], [122], [123], [124], [125], [126], [127], [128], [129], [130], [131], [132], [133], [134], [135], [136,137], [138,139], [140,141], [142,143], [144,145], [146,147,148], [149,150,151,152], [153,154,155,156,157,158,159,160]]

private def accL0 : List (List (List ℤ)) :=
  [acc0_0, acc0_1, acc0_2, acc0_3, acc0_4, acc0_5, acc0_6, acc0_7, acc0_8, acc0_9, acc0_10, acc0_11, acc0_12, acc0_13, acc0_14, acc0_15, acc0_16, acc0_17, acc0_18, acc0_19, acc0_20, acc0_21, acc0_22, acc0_23, acc0_24, acc0_25, acc0_26, acc0_27, acc0_28, acc0_29, acc0_30, acc0_31, acc0_32, acc0_33, acc0_34, acc0_35, acc0_36, acc0_37, acc0_38, acc0_39, acc0_40, acc0_41, acc0_42, acc0_43, acc0_44, acc0_45, acc0_46, acc0_47, acc0_48, acc0_49, acc0_50, acc0_51, acc0_52, acc0_53, acc0_54, acc0_55, acc0_56, acc0_57, acc0_58, acc0_59, acc0_60, acc0_61, acc0_62, acc0_63, acc0_64, acc0_65, acc0_66, acc0_67, acc0_68, acc0_69, acc0_70, acc0_71, acc0_72, acc0_73, acc0_74, acc0_75, acc0_76, acc0_77, acc0_78, acc0_79, acc0_80, acc0_81, acc0_82, acc0_83, acc0_84, acc0_85, acc0_86, acc0_87, acc0_88, acc0_89, acc0_90, acc0_91, acc0_92, acc0_93, acc0_94, acc0_95, acc0_96, acc0_97, acc0_98, acc0_99, acc0_100, acc0_101, acc0_102, acc0_103, acc0_104, acc0_105, acc0_106, acc0_107, acc0_108, acc0_109, acc0_110, acc0_111, acc0_112, acc0_113, acc0_114, acc0_115, acc0_116, acc0_117, acc0_118, acc0_119, acc0_120, acc0_121, acc0_122, acc0_123, acc0_124, acc0_125, acc0_126, acc0_127, acc0_128, acc0_129, acc0_130, acc0_131, acc0_132, acc0_133, acc0_134, acc0_135, acc0_136, acc0_137]

private def accs0 : ℕ → List (List ℤ) := fun j => accL0.getD j []

private lemma chain0 :
    ∀ j < segs0.length,
      ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk 0) (ksL.getD 0 [])
        (ysL.getD 0 []) Cs0 Ws0 (segs0.getD j []) (accs0 j) =
        some (accs0 (j + 1)) := by
  intro j hj
  have hj' : j < 137 := hj
  interval_cases j
  · exact ldl_ok0_0
  · exact ldl_ok0_1
  · exact ldl_ok0_2
  · exact ldl_ok0_3
  · exact ldl_ok0_4
  · exact ldl_ok0_5
  · exact ldl_ok0_6
  · exact ldl_ok0_7
  · exact ldl_ok0_8
  · exact ldl_ok0_9
  · exact ldl_ok0_10
  · exact ldl_ok0_11
  · exact ldl_ok0_12
  · exact ldl_ok0_13
  · exact ldl_ok0_14
  · exact ldl_ok0_15
  · exact ldl_ok0_16
  · exact ldl_ok0_17
  · exact ldl_ok0_18
  · exact ldl_ok0_19
  · exact ldl_ok0_20
  · exact ldl_ok0_21
  · exact ldl_ok0_22
  · exact ldl_ok0_23
  · exact ldl_ok0_24
  · exact ldl_ok0_25
  · exact ldl_ok0_26
  · exact ldl_ok0_27
  · exact ldl_ok0_28
  · exact ldl_ok0_29
  · exact ldl_ok0_30
  · exact ldl_ok0_31
  · exact ldl_ok0_32
  · exact ldl_ok0_33
  · exact ldl_ok0_34
  · exact ldl_ok0_35
  · exact ldl_ok0_36
  · exact ldl_ok0_37
  · exact ldl_ok0_38
  · exact ldl_ok0_39
  · exact ldl_ok0_40
  · exact ldl_ok0_41
  · exact ldl_ok0_42
  · exact ldl_ok0_43
  · exact ldl_ok0_44
  · exact ldl_ok0_45
  · exact ldl_ok0_46
  · exact ldl_ok0_47
  · exact ldl_ok0_48
  · exact ldl_ok0_49
  · exact ldl_ok0_50
  · exact ldl_ok0_51
  · exact ldl_ok0_52
  · exact ldl_ok0_53
  · exact ldl_ok0_54
  · exact ldl_ok0_55
  · exact ldl_ok0_56
  · exact ldl_ok0_57
  · exact ldl_ok0_58
  · exact ldl_ok0_59
  · exact ldl_ok0_60
  · exact ldl_ok0_61
  · exact ldl_ok0_62
  · exact ldl_ok0_63
  · exact ldl_ok0_64
  · exact ldl_ok0_65
  · exact ldl_ok0_66
  · exact ldl_ok0_67
  · exact ldl_ok0_68
  · exact ldl_ok0_69
  · exact ldl_ok0_70
  · exact ldl_ok0_71
  · exact ldl_ok0_72
  · exact ldl_ok0_73
  · exact ldl_ok0_74
  · exact ldl_ok0_75
  · exact ldl_ok0_76
  · exact ldl_ok0_77
  · exact ldl_ok0_78
  · exact ldl_ok0_79
  · exact ldl_ok0_80
  · exact ldl_ok0_81
  · exact ldl_ok0_82
  · exact ldl_ok0_83
  · exact ldl_ok0_84
  · exact ldl_ok0_85
  · exact ldl_ok0_86
  · exact ldl_ok0_87
  · exact ldl_ok0_88
  · exact ldl_ok0_89
  · exact ldl_ok0_90
  · exact ldl_ok0_91
  · exact ldl_ok0_92
  · exact ldl_ok0_93
  · exact ldl_ok0_94
  · exact ldl_ok0_95
  · exact ldl_ok0_96
  · exact ldl_ok0_97
  · exact ldl_ok0_98
  · exact ldl_ok0_99
  · exact ldl_ok0_100
  · exact ldl_ok0_101
  · exact ldl_ok0_102
  · exact ldl_ok0_103
  · exact ldl_ok0_104
  · exact ldl_ok0_105
  · exact ldl_ok0_106
  · exact ldl_ok0_107
  · exact ldl_ok0_108
  · exact ldl_ok0_109
  · exact ldl_ok0_110
  · exact ldl_ok0_111
  · exact ldl_ok0_112
  · exact ldl_ok0_113
  · exact ldl_ok0_114
  · exact ldl_ok0_115
  · exact ldl_ok0_116
  · exact ldl_ok0_117
  · exact ldl_ok0_118
  · exact ldl_ok0_119
  · exact ldl_ok0_120
  · exact ldl_ok0_121
  · exact ldl_ok0_122
  · exact ldl_ok0_123
  · exact ldl_ok0_124
  · exact ldl_ok0_125
  · exact ldl_ok0_126
  · exact ldl_ok0_127
  · exact ldl_ok0_128
  · exact ldl_ok0_129
  · exact ldl_ok0_130
  · exact ldl_ok0_131
  · exact ldl_ok0_132
  · exact ldl_ok0_133
  · exact ldl_ok0_134
  · exact ldl_ok0_135
  · exact ldl_ok0_136

private lemma flatten0 : segs0.flatten = List.range (nK 0) := by decide +kernel

private lemma accZero0 : accs0 0 = List.replicate 4 (List.replicate (nK 0) 0) := by
  decide +kernel

private lemma shape0 :
    ∀ ψ < 4, (Ws0.getD ψ []).length = nK 0 ∧ (Cs0.getD ψ []).length = nK 0 ∧
      ∀ i < nK 0, 0 < (Ws0.getD ψ []).getD i 1 ∧
        ((Cs0.getD ψ []).getD i []).length ≤ i + 1 :=
  (Work.PTCert.ldlDataOK_iff Cs0 Ws0 161).mp ldldata_ok0

/-! ### Base character `k = 1` -/

private def segs1 : List (List ℕ) :=
  [[0,1,2,3,4,5], [6,7,8,9], [10,11,12,13], [14,15,16], [17,18,19], [20,21,22], [23,24,25], [26,27,28], [29,30,31], [32,33,34], [35,36,37], [38,39,40], [41,42,43], [44,45,46], [47,48,49], [50,51,52], [53,54,55], [56,57,58], [59,60,61], [62,63,64,65], [66,67,68,69], [70,71,72,73,74], [75,76,77,78,79,80,81,82,83], [84,85,86,87]]

private def accL1 : List (List (List ℤ)) :=
  [acc1_0, acc1_1, acc1_2, acc1_3, acc1_4, acc1_5, acc1_6, acc1_7, acc1_8, acc1_9, acc1_10, acc1_11, acc1_12, acc1_13, acc1_14, acc1_15, acc1_16, acc1_17, acc1_18, acc1_19, acc1_20, acc1_21, acc1_22, acc1_23, acc1_24]

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
  (Work.PTCert.ldlDataOK_iff Cs1 Ws1 88).mp ldldata_ok1

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

/-! ### Base character `k = 3` -/

private def segs3 : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22], [23,24,25,26]]

private def accL3 : List (List (List ℤ)) :=
  [acc3_0, acc3_1, acc3_2]

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

/-! ### Base character `k = 4` -/

private def segs4 : List (List ℕ) :=
  [[0,1,2,3,4,5]]

private def accL4 : List (List (List ℤ)) :=
  [acc4_0, acc4_1]

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

/-- **The LDL data of the `C2` certificate.** -/
theorem ldlDataC2 : ∀ k ≤ 4, Submission.PTCert.G.LdlData Submission.PTCert.D2.rowTs k := by
  intro k hk
  interval_cases k
  · exact ⟨Cs0, Ws0, segs0, accs0, flatten0, accZero0, chain0, shape0⟩
  · exact ⟨Cs1, Ws1, segs1, accs1, flatten1, accZero1, chain1, shape1⟩
  · exact ⟨Cs2, Ws2, segs2, accs2, flatten2, accZero2, chain2, shape2⟩
  · exact ⟨Cs3, Ws3, segs3, accs3, flatten3, accZero3, chain3, shape3⟩
  · exact ⟨Cs4, Ws4, segs4, accs4, flatten4, accZero4, chain4, shape4⟩

end Work.PTCert.Cert2

end
