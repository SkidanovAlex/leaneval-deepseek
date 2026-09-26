import Mathlib
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — `cert1Ldl0`: the LDL data of the `C1` certificate for the base character `k = 0`

This is the `k = 0` instance of `LdlData D1.rowTs` for certificate 1 (C1), the exact analogue of the
`k = 0` clause of `Work.PTCert.Cert2.ldlDataC2` for certificate 2.  The witnesses are

* `Cs := D1.Cs0`, `Ws := D1.Ws0` — the factor-row / weight tables;
* `segs0` — the index segments of the kernel chain theorems `C1K.ldl_ok0_{0..136}`, in order;
* `accs0 j` — the `j`-th accumulator witness `D1.acc0_{j}` (junk `[]` beyond the chain).

The four clauses of `LdlData` are the structural facts `flatten0`, `accZero0` (both `decide +kernel`),
the chain `chain0` (one case per kernel theorem, each closed by the corresponding `ldl_ok0_{j}`),
and the shape clause `shape0`, obtained from `C1K.ldldata_ok0` through `Work.PTCert.ldlDataOK_iff`.

The segment list has `137` entries and flattens to `List.range 161 = List.range (nK 0)`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 0

noncomputable section
namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K
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
  (ldlDataOK_iff Cs0 Ws0 161).mp ldldata_ok0

/-- **The LDL data of the `C1` certificate for the base character `k = 0`.** -/
theorem cert1Ldl0 : Submission.PTCert.G.LdlData Submission.PTCert.D1.rowTs 0 :=
  ⟨Cs0, Ws0, segs0, accs0, flatten0, accZero0, chain0, shape0⟩

end Work.PTCert

end
