import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.StripDefs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

theorem stripLo_stripHi_eq_of_logrel {g : Work.FTS.Galerkin.Fn} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {ε : ℝ} (hε : 0 < ε)
    {z' θ' p₂ : ℝ} (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) (hp₂ : |p₂| ≤ ε)
    (hrel : p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ')) :
    Work.FTS.EpsEngine.ThetaFromEps.stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g z' θ' = g z' θ' ∧
    Work.FTS.EpsEngine.ThetaFromEps.stripHi (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g z' θ'
      = g z' θ' := by
  -- `tan θ' = tan θ · e^{-p₂}`, so `tan θ'` lies between `tan θ · e^{-ε}` and `tan θ · e^{ε}`;
  -- applying the increasing `arctan` and using `arctan (tan θ') = θ'` gives the two strip
  -- conditions `θ' ≤ thShift θ (-ε)` and `thShift θ ε ≤ θ'`.
  have hT : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have hT' : 0 < Real.tan θ' := Real.tan_pos_of_pos_of_lt_pi_div_two hθ'.1 hθ'.2
  have hlog : Real.log (Real.tan θ') = Real.log (Real.tan θ) - p₂ := by linarith
  have htan : Real.tan θ' = Real.tan θ * Real.exp (-p₂) := by
    have h := congrArg Real.exp hlog
    rwa [Real.exp_log hT', Real.exp_sub, Real.exp_log hT, div_eq_mul_inv, ← Real.exp_neg] at h
  have hle : -p₂ ≤ ε := by have h := (abs_le.mp hp₂).1; linarith
  have hge : -ε ≤ -p₂ := by have h := (abs_le.mp hp₂).2; linarith
  have harctan : Real.arctan (Real.tan θ') = θ' :=
    Real.arctan_tan (by linarith [hθ'.1, Real.pi_pos]) hθ'.2
  have hA : Real.tan θ' ≤ Real.tan θ * Real.exp ε := by
    rw [htan]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hT.le
  have hB : Real.tan θ * Real.exp (-ε) ≤ Real.tan θ' := by
    rw [htan]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hge) hT.le
  have h1 : θ' ≤ Work.FTS.StrongEps.thShift θ (-ε) := by
    rw [Work.FTS.StrongEps.thShift, neg_neg]
    calc θ' = Real.arctan (Real.tan θ') := harctan.symm
      _ ≤ Real.arctan (Real.tan θ * Real.exp ε) := Real.arctan_mono hA
  have h2 : Work.FTS.StrongEps.thShift θ ε ≤ θ' := by
    rw [Work.FTS.StrongEps.thShift]
    calc Real.arctan (Real.tan θ * Real.exp (-ε)) ≤ Real.arctan (Real.tan θ') := Real.arctan_mono hB
      _ = θ' := harctan
  constructor
  · simp only [Work.FTS.EpsEngine.ThetaFromEps.stripLo]
    rw [if_pos h1]
  · simp only [Work.FTS.EpsEngine.ThetaFromEps.stripHi]
    rw [if_pos (by linarith)]

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
