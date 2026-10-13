import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.ClassCHon.CmpSupp.eNorm_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.HcoefSplit

theorem hcoef_Lterm_le {α L : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hL : 0 ≤ L) {m : ℕ}
    (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
      ≤ L * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  -- `α` cancels between `rgK` and `1/rgQ + 1/rgP`; what remains is
  -- `(m+1)/((2m+5)·2m) · 1/√(eNorm m) ≤ m^{-3/2}`, since `eNorm m ≥ m`.
  have hαne : α ≠ 0 := ne_of_gt hα
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  -- the cancellation of `α`
  have hkey : Work.FTS.EllExist.rgK α m * (1 / Work.FTS.EllExist.rgQ α m
        + 1 / Work.FTS.EllExist.rgP α m)
      = 1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
    rw [Work.FTS.EllExist.rgK, Work.FTS.EllExist.rgQ, Work.FTS.EllExist.rgP]
    field_simp
    ring
  -- `(m+1)/((2m+5)·2m) ≤ 1/m`, since `m(m+1) ≤ (2m+5)·2m`
  have hcoef : ((m : ℝ) + 1) / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))) ≤ 1 / (m : ℝ) := by
    have hpos : (0 : ℝ) < (2 * (m : ℝ) + 5) * (2 * (m : ℝ)) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : 1 / (m : ℝ) * ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))) = 2 * (2 * (m : ℝ) + 5) := by
      field_simp
    rw [h1]
    linarith
  -- `1/√(eNorm m) ≤ 1/√m`, from `eNorm m ≥ m`
  have hsqrtinv :
      1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≤ 1 / Real.sqrt (m : ℝ) := by
    have hge : (m : ℝ) ≤ Work.EllipticEst.ModalSolution.eNorm m :=
      (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds m).2
    have hsq : Real.sqrt (m : ℝ) ≤ Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
      Real.sqrt_le_sqrt hge
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hm0) hsq
  -- `m^{-3/2} = 1/(m·√m)`
  have hrpow : (m : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
    have hmul : (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) ^ (3 / 2 : ℝ) := by
      have h := Real.rpow_add hm0 (1 : ℝ) (1 / 2 : ℝ)
      rw [Real.rpow_one, show (1 : ℝ) + 1 / 2 = 3 / 2 from by norm_num,
        ← Real.sqrt_eq_rpow] at h
      exact h.symm
    rw [Real.rpow_neg (le_of_lt hm0), hmul, one_div]
  have hright : (1 / (m : ℝ)) * (1 / Real.sqrt (m : ℝ)) = (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [hrpow]
    field_simp
  have step1 : ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
      = L * (((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))) := by
    rw [show ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
        = ((m : ℝ) + 1) * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (Work.FTS.EllExist.rgK α m * (1 / Work.FTS.EllExist.rgQ α m
              + 1 / Work.FTS.EllExist.rgP α m))) from by ring,
      hkey]
    ring
  have step2 : ((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
      * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ)))) ≤ (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hval : ((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
        * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))
        = (((m : ℝ) + 1) / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))
            * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) := by ring
    rw [hval, ← hright]
    exact mul_le_mul hcoef hsqrtinv (by positivity) (by positivity)
  calc ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
      = L * (((m : ℝ) + 1) * (1 / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ))))) := step1
    _ ≤ L * (m : ℝ) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left step2 hL

end Work.FTS.ClassCHon.HcoefSplit
