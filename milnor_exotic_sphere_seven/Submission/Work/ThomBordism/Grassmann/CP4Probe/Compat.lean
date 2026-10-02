import Mathlib
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Map

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## The decomposition of the inner product and the norm -/

theorem inner_self_split (x : E5) :
    inner ℝ x x = inner ℝ (preC x) (preC x) + inner ℝ (sufC x) (sufC x) := by
  rw [inner_split, ← inner_preC, ← inner_sufC]

theorem toLp_zero_e2 : (WithLp.toLp 2 (0 : Fin 2 → ℂ) : E2) = 0 := rfl

theorem sufC_cfOf_padF (w : Fin 3 → ℂ) : sufC (cfOf (padF w)) = 0 := by
  rw [sufC_cfOf, suf2F_padF, toLp_zero_e2]

theorem norm_cfOf_padF (w : Fin 3 → ℂ) : ‖cfOf (padF w)‖ = ‖cxOf w‖ := by
  have h := inner_self_split (cfOf (padF w))
  rw [preC_cfOf, pre3F_padF, sufC_cfOf_padF, inner_zero_left, add_zero] at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (cfOf (padF w)), norm_nonneg (cxOf w)]

theorem preC_smul_real (a : ℝ) (x : E5) : preC (a • x) = a • preC x :=
  map_smul (preC.restrictScalars ℝ) a x

theorem sufC_smul_real (a : ℝ) (x : E5) : sufC (a • x) = a • sufC x :=
  map_smul (sufC.restrictScalars ℝ) a x

/-! ## The two projections of the unit vector -/

theorem sufC_cfUnit_padF (w : Fin 3 → ℂ) (hw : w ≠ 0) : sufC (cfUnit (padF w)) = 0 := by
  rw [cfUnit, sufC_smul_real, sufC_cfOf_padF]
  simp

theorem preC_cfUnit_padF (w : Fin 3 → ℂ) (hw : w ≠ 0) :
    preC (cfUnit (padF w)) = cxUnit w := by
  rw [cfUnit, preC_smul_real, norm_cfOf_padF w, preC_cfOf, pre3F_padF]
  rfl

/-! ## The embedding of the unit vector -/

theorem emb5_cfUnit_padF (w : Fin 3 → ℂ) (hw : w ≠ 0) :
    emb5 (cfUnit (padF w))
      = probeEmb 2 8 (by norm_num) (by norm_num) (cxE (cxUnit w)) := by
  rw [emb5_apply_eq, preC_cfUnit_padF w hw, sufC_cfUnit_padF w hw, map_zero, add_zero,
    embA_apply]

theorem emb5_I_cfUnit_padF (w : Fin 3 → ℂ) (hw : w ≠ 0) :
    emb5 (Complex.I • cfUnit (padF w))
      = probeEmb 2 8 (by norm_num) (by norm_num) (cxE (Complex.I • cxUnit w)) := by
  rw [emb5_apply_eq, map_smul sufC Complex.I, sufC_cfUnit_padF w hw, smul_zero, map_zero,
    add_zero, embA_apply, map_smul preC Complex.I, preC_cfUnit_padF w hw]

/-! ## The frame of the restriction -/

theorem probeFrameRep_two_zero (w : Fin 3 → ℂ) :
    probeFrameRep 2 8 (by norm_num) (by norm_num) w 0
      = probePairVec 2 8 (by norm_num) (by norm_num) w 0 := by
  rw [← probeFrameRep_inl 2 8 (by norm_num) (by norm_num) w 0]
  congr 1

theorem probeFrameRep_two_one (w : Fin 3 → ℂ) :
    probeFrameRep 2 8 (by norm_num) (by norm_num) w 1
      = probePairVec 2 8 (by norm_num) (by norm_num) w 1 := by
  rw [← probeFrameRep_inl 2 8 (by norm_num) (by norm_num) w 1]
  congr 1

theorem lineFrame_padF (w : Fin 3 → ℂ) (hw : w ≠ 0) :
    lineFrame (padF w) = probeFrameRep 2 8 (by norm_num) (by norm_num) w := by
  have h0 : lineFrame (padF w) 0
      = probeFrameRep 2 8 (by norm_num) (by norm_num) w 0 := by
    rw [lineFrame_zero, probeFrameRep_two_zero, probePairVec_zero, emb5_cfUnit_padF w hw]
  have h1 : lineFrame (padF w) 1
      = probeFrameRep 2 8 (by norm_num) (by norm_num) w 1 := by
    rw [lineFrame_one, probeFrameRep_two_one, probePairVec_one, emb5_I_cfUnit_padF w hw]
  funext a
  fin_cases a
  · exact h0
  · exact h1

theorem lineStiefel_padF (w : {w : Fin 3 → ℂ // w ≠ 0}) :
    lineStiefel ⟨padF w.1, padF_ne_zero w.2⟩
      = probeStiefelRep 2 8 (by norm_num) (by norm_num) w.1 w.2 := by
  apply Subtype.ext
  show lineFrame (padF w.1) = probeFrameRep 2 8 (by norm_num) (by norm_num) w.1
  exact lineFrame_padF w.1 w.2

/-! ## The compatibility of the `ℂP⁴`-probe with the `ℂP²`-probe -/

theorem probeCP4Map_comp_iota :
    probeCP4Map.comp iota = probeSigma 2 8 (by norm_num) (by norm_num) := by
  ext x
  obtain ⟨w, rfl⟩ := Quotient.exists_rep x
  have h1 : probeCP4Map (iota (Quotient.mk'' w))
      = ogMk 2 8 (lineStiefel ⟨padF (w : Fin 3 → ℂ), padF_ne_zero w.2⟩) := by
    rw [show Quotient.mk'' w = Projectivization.mk' ℂ w from rfl, iota_apply_mk]
    exact probeCP4Map_apply ⟨padF (w : Fin 3 → ℂ), padF_ne_zero w.2⟩
  have h2 : probeSigma 2 8 (by norm_num) (by norm_num) (Quotient.mk'' w)
      = ogMk 2 8 (lineStiefel ⟨padF (w : Fin 3 → ℂ), padF_ne_zero w.2⟩) := by
    rw [show Quotient.mk'' w = Projectivization.mk' ℂ w from rfl, lineStiefel_padF w]
    exact probeSigmaFun_mk 2 8 (by norm_num) (by norm_num) w
  rw [ContinuousMap.comp_apply, h1, h2]

end

end Work.ThomBordism.Grassmann
