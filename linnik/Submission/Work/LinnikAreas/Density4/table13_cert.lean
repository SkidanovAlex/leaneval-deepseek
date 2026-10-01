import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Density4.T13.Num1
import Submission.Work.LinnikAreas.Density4.T13.Num2
import Submission.Work.LinnikAreas.Density4.T13.Num3
import Submission.Work.LinnikAreas.Density4.T13.Num4

namespace Work.LinnikAreas.Density4

theorem table13_cert :
    ∀ e ∈ Work.LinnikContract.table13,
      Work.LinnikAreas.Density4.bnd13 e.1 e.2.1 < (e.2.2 : ℝ) + 1 := by
  intro e he
  fin_cases he
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63
  · exact row_64
  · exact row_65
  · exact row_66
  · exact row_67
  · exact row_68
  · exact row_69
  · exact row_70
  · exact row_71
  · exact row_72
  · exact row_73
  · exact row_74
  · exact row_75
  · exact row_76
  · exact row_77
  · exact row_78
  · exact row_79
  · exact row_80
  · exact row_81
  · exact row_82
  · exact row_83
  · exact row_84
  · exact row_85
  · exact row_86
  · exact row_87
  · exact row_88
  · exact row_89
  · exact row_90
  · exact row_91
  · exact row_92
  · exact row_93
  · exact row_94
  · exact row_95
  · exact row_96
  · exact row_97
  · exact row_98
  · exact row_99
  · exact row_100

end Work.LinnikAreas.Density4
