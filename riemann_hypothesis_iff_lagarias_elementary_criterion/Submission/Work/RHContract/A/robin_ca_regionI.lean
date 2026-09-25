import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.RegionI.boundary_facts
import Submission.Work.RHContract.A.RegionI.cover_of_chain
import Submission.Work.RHContract.A.RegionI.Core
import Submission.Work.RHContract.A.RegionI.Cuts
import Submission.Work.RHContract.A.RegionI.Block01
import Submission.Work.RHContract.A.RegionI.Block02
import Submission.Work.RHContract.A.RegionI.Block03
import Submission.Work.RHContract.A.RegionI.Block04
import Submission.Work.RHContract.A.RegionI.Block05
import Submission.Work.RHContract.A.RegionI.Block06
import Submission.Work.RHContract.A.RegionI.Block07
import Submission.Work.RHContract.A.RegionI.Block08
import Submission.Work.RHContract.A.RegionI.Block09
import Submission.Work.RHContract.A.RegionI.Block10

/-!
# Region I: Robin's inequality at `N_ε` for `1530 ≤ ξ(ε) < 30000`

The cover of `ξ⁻¹([1530,30000))` by the finitely many cut intervals of
`RegionI.Cuts`, with one certificate (`RegionI.block_j`) per interval.
-/

open scoped BigOperators

namespace Work.RHContract.A

theorem robin_ca_regionI (ε : ℝ) (hε : 0 < ε)
    (hlo : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 30000) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  obtain ⟨hb1, hb2⟩ := Work.RHContract.A.RegionI.boundary_facts ε hε
  -- top: `ε ≤ cF 1531 1 ≤ Fhi 1531 1 ≤ cut 0`
  have htop : ε ≤ ((Work.RHContract.A.RegionI.cut ⟨0, by omega⟩ : ℚ) : ℝ) := by
    have h1 : ε ≤ Work.RHContract.RegionI.cF 1531 1 := hb1 hlo
    have h2 : Work.RHContract.RegionI.cF 1531 1 ≤ (Work.RHContract.RegionI.Fhi 1531 1 : ℝ) :=
      Work.RHContract.RegionI.cF_le_Fhi (p := 1531) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    have h3 : Work.RHContract.RegionI.Fhi 1531 1 ≤ (Work.RHContract.A.RegionI.cut ⟨0, by omega⟩ : ℚ) := by
      decide +kernel
    have h3' : (Work.RHContract.RegionI.Fhi 1531 1 : ℝ) ≤ ((Work.RHContract.A.RegionI.cut ⟨0, by omega⟩ : ℚ) : ℝ) :=
      Rat.cast_le.mpr h3
    linarith
  -- bottom: `cut 386 ≤ Flo 30011 1 ≤ cF 30011 1 < ε`
  have hbot : ((Work.RHContract.A.RegionI.cut ⟨386, by omega⟩ : ℚ) : ℝ) < ε := by
    have h1 : Work.RHContract.RegionI.cF 30011 1 < ε := hb2 hhi
    have h2 : (Work.RHContract.A.RegionI.cut ⟨386, by omega⟩ : ℚ) ≤ Work.RHContract.RegionI.Flo 30011 1 := by
      decide +kernel
    have h2' : ((Work.RHContract.A.RegionI.cut ⟨386, by omega⟩ : ℚ) : ℝ) ≤ (Work.RHContract.RegionI.Flo 30011 1 : ℝ) :=
      Rat.cast_le.mpr h2
    have h3 : (Work.RHContract.RegionI.Flo 30011 1 : ℝ) ≤ Work.RHContract.RegionI.cF 30011 1 :=
      Work.RHContract.RegionI.Flo_le_cF (p := 30011) (k := 1) (by norm_num) (by norm_num) (by norm_num)
    linarith
  -- monotonicity of the cuts
  have hmonoQ : ∀ i : Fin 386, (Work.RHContract.A.RegionI.cut ⟨i.val + 1, by omega⟩ : ℚ)
      < Work.RHContract.A.RegionI.cut ⟨i.val, by omega⟩ := by decide +kernel
  have hmono : ∀ i : Fin 386, (Work.RHContract.A.RegionI.cut ⟨i.val + 1, by omega⟩ : ℝ)
      < (Work.RHContract.A.RegionI.cut ⟨i.val, by omega⟩ : ℝ) := fun i => Rat.cast_lt.mpr (hmonoQ i)
  obtain ⟨i, hi1, hi2⟩ := Work.RHContract.A.RegionI.cover_of_chain
    (fun i : Fin 387 => ((Work.RHContract.A.RegionI.cut i : ℚ) : ℝ)) hmono ε hbot htop
  fin_cases i
  · exact Work.RHContract.A.RegionI.block_0 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_1 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_2 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_3 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_4 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_5 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_6 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_7 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_8 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_9 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_10 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_11 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_12 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_13 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_14 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_15 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_16 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_17 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_18 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_19 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_20 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_21 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_22 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_23 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_24 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_25 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_26 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_27 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_28 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_29 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_30 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_31 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_32 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_33 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_34 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_35 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_36 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_37 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_38 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_39 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_40 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_41 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_42 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_43 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_44 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_45 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_46 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_47 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_48 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_49 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_50 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_51 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_52 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_53 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_54 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_55 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_56 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_57 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_58 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_59 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_60 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_61 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_62 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_63 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_64 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_65 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_66 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_67 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_68 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_69 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_70 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_71 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_72 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_73 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_74 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_75 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_76 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_77 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_78 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_79 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_80 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_81 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_82 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_83 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_84 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_85 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_86 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_87 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_88 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_89 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_90 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_91 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_92 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_93 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_94 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_95 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_96 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_97 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_98 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_99 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_100 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_101 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_102 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_103 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_104 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_105 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_106 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_107 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_108 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_109 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_110 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_111 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_112 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_113 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_114 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_115 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_116 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_117 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_118 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_119 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_120 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_121 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_122 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_123 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_124 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_125 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_126 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_127 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_128 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_129 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_130 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_131 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_132 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_133 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_134 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_135 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_136 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_137 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_138 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_139 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_140 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_141 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_142 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_143 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_144 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_145 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_146 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_147 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_148 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_149 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_150 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_151 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_152 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_153 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_154 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_155 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_156 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_157 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_158 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_159 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_160 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_161 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_162 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_163 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_164 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_165 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_166 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_167 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_168 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_169 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_170 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_171 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_172 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_173 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_174 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_175 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_176 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_177 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_178 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_179 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_180 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_181 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_182 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_183 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_184 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_185 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_186 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_187 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_188 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_189 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_190 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_191 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_192 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_193 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_194 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_195 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_196 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_197 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_198 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_199 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_200 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_201 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_202 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_203 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_204 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_205 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_206 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_207 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_208 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_209 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_210 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_211 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_212 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_213 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_214 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_215 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_216 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_217 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_218 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_219 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_220 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_221 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_222 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_223 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_224 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_225 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_226 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_227 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_228 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_229 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_230 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_231 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_232 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_233 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_234 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_235 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_236 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_237 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_238 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_239 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_240 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_241 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_242 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_243 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_244 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_245 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_246 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_247 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_248 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_249 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_250 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_251 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_252 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_253 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_254 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_255 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_256 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_257 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_258 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_259 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_260 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_261 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_262 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_263 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_264 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_265 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_266 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_267 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_268 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_269 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_270 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_271 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_272 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_273 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_274 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_275 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_276 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_277 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_278 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_279 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_280 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_281 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_282 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_283 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_284 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_285 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_286 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_287 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_288 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_289 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_290 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_291 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_292 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_293 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_294 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_295 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_296 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_297 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_298 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_299 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_300 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_301 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_302 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_303 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_304 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_305 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_306 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_307 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_308 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_309 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_310 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_311 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_312 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_313 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_314 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_315 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_316 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_317 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_318 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_319 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_320 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_321 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_322 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_323 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_324 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_325 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_326 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_327 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_328 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_329 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_330 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_331 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_332 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_333 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_334 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_335 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_336 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_337 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_338 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_339 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_340 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_341 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_342 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_343 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_344 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_345 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_346 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_347 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_348 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_349 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_350 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_351 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_352 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_353 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_354 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_355 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_356 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_357 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_358 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_359 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_360 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_361 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_362 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_363 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_364 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_365 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_366 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_367 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_368 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_369 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_370 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_371 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_372 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_373 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_374 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_375 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_376 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_377 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_378 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_379 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_380 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_381 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_382 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_383 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_384 ε hε hi2 hi1 hlo
  · exact Work.RHContract.A.RegionI.block_385 ε hε hi2 hi1 hlo

end Work.RHContract.A
