import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SpikeDefs

namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane

/-- `j` is unchanged by the unit translation `τ ↦ τ - 1`. -/
lemma jInvariantFun_neg_vadd_one (τ : UpperHalfPlane) :
    Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  have h := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by
    rw [← add_vadd, show (1 : ℝ) + (-1 : ℝ) = 0 by norm_num, zero_vadd]] at h
  exact h.symm

/-- The `dslope`-based remainder `Tleft` at the translated pole `ζ ≠ τ ± 1`. -/
lemma Tleft_coe_eq (τ ζ : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) :
    Tleft τ (ζ : ℂ) =
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) * PP τ ζ := by
  have hne1 : (ζ : ℂ) ≠ (τ : ℂ) - 1 := by
    intro hc
    refine h ?_
    have hzeta : ζ = (-1 : ℝ) +ᵥ τ := by
      apply UpperHalfPlane.ext
      rw [coe_neg_one_vadd]
      exact hc
    rw [hzeta, jInvariantFun_neg_vadd_one]
  have hne2 : (ζ : ℂ) ≠ (τ : ℂ) + 1 := by
    intro hc
    refine h ?_
    have hzeta : ζ = (1 : ℝ) +ᵥ τ := by
      apply UpperHalfPlane.ext
      rw [coe_one_vadd]
      exact hc
    rw [hzeta, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]
  have hD1 : D1 τ (ζ : ℂ) =
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) /
        ((ζ : ℂ) - ((τ : ℂ) - 1)) := by
    unfold D1
    rw [dslope_of_ne _ hne1, slope_def_field]
    have hc : jlDiff τ ((τ : ℂ) - 1) = 0 := by
      simp only [jlDiff, ofComplex_sub_one, jInvariantFun_neg_vadd_one]
      ring
    rw [hc, sub_zero]
    simp only [jlDiff, UpperHalfPlane.ofComplex_apply]
  have hD2 : D2 τ (ζ : ℂ) =
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) /
        ((ζ : ℂ) - ((τ : ℂ) + 1)) := by
    unfold D2
    rw [dslope_of_ne _ hne2, slope_def_field]
    have hc : jlDiff τ ((τ : ℂ) + 1) = 0 := by
      simp only [jlDiff, ofComplex_add_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]
      ring
    rw [hc, sub_zero]
    simp only [jlDiff, UpperHalfPlane.ofComplex_apply]
  simp only [Tleft, PP]
  rw [hD1, hD2]
  ring

theorem Wlift_id (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ ζ : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) : Work.Asymptotics.SpikeCircle.Wlift ℓ d τ (ζ : ℂ) = Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun ζ * ((Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) * (Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.SpikeCircle.PP τ ζ)) := by
  have hT := Tleft_coe_eq τ ζ h
  have hA : AfunFun ℓ d τ ζ =
      Work.Kernels.Kfun ℓ d τ ζ * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) :=
    (Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ h).symm
  simp only [Wlift, UpperHalfPlane.ofComplex_apply]
  rw [hT, hA]
  ring

end Work.Asymptotics.SpikeCircle
