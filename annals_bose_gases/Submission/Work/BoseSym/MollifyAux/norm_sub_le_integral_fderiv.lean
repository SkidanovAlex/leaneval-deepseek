import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mean-value estimate along a straight segment, in real integrals

For `f : Conf N → ℝ` of class `C¹` and `x y : Conf N`, the fundamental theorem of
calculus along the segment `s ↦ x - s • y` (`s ∈ [0,1]`) gives

`f (x - y) - f x = ∫_0^1 (fderiv ℝ f (x - s • y)) (-y) ds`

and, bounding the norm of the integrand by `‖fderiv ℝ f (x - s • y)‖ * ‖y‖` and
using `‖∫ g‖ ≤ ∫ ‖g‖`,

`‖f x - f (x - y)‖ ≤ ∫_0^1 ‖fderiv ℝ f (x - t • y)‖ * ‖y‖ dt`.

This is the real-valued form of `Mollify.enorm_sub_translate_le`; it is stated
here as a standalone lemma so that later estimates can consume it directly.
-/

namespace Work.BoseSym.MollifyAux

open MeasureTheory intervalIntegral

open Work.BoseSym

theorem norm_sub_le_integral_fderiv {N : ℕ} {f : Conf N → ℝ} (hf : Smooth1 f) (x y : Conf N) :
    ‖f x - f (x - y)‖ ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (x - t • y)‖ * ‖y‖ := by
  -- the parametrised curve along the segment from `x` to `x - y`
  let γ : ℝ → ℝ := fun s => f (x - s • y)
  have hγ1 : γ 1 = f (x - y) := by simp [γ]
  have hγ0 : γ 0 = f x := by simp [γ]
  -- its derivative is `(fderiv ℝ f (x - s • y)) (-y)`
  have hderiv : ∀ s : ℝ, HasDerivAt γ ((fderiv ℝ f (x - s • y)) (-y)) s := by
    intro s
    have hsm : HasDerivAt (fun u : ℝ => u • y) y s := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) s).smul_const y
    have hφd : HasDerivAt (fun u : ℝ => x - u • y) (-y) s := by
      simpa using hsm.const_sub x
    have hf' : HasFDerivAt f (fderiv ℝ f (x - s • y)) (x - s • y) :=
      (hf.differentiable_one.differentiableAt).hasFDerivAt
    exact hf'.comp_hasDerivAt s hφd
  -- continuity of `fderiv ℝ f` and of the segment
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hφc : Continuous (fun s : ℝ => x - s • y) :=
    continuous_const.sub
      (Continuous.smul continuous_id (continuous_const : Continuous fun _ : ℝ => y))
  have hcontD : Continuous (fun s : ℝ => (fderiv ℝ f (x - s • y)) (-y)) :=
    (hfd.comp hφc).clm_apply continuous_const
  have hcontN : Continuous (fun s : ℝ => ‖(fderiv ℝ f (x - s • y)) (-y)‖) := hcontD.norm
  have hcontM : Continuous (fun s : ℝ => ‖fderiv ℝ f (x - s • y)‖ * ‖y‖) :=
    ((hfd.comp hφc).norm).mul_const ‖y‖
  -- the fundamental theorem of calculus
  have hFTC : ∫ s in (0:ℝ)..1, (fderiv ℝ f (x - s • y)) (-y) = γ 1 - γ 0 :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcontD.intervalIntegrable 0 1)
  calc ‖f x - f (x - y)‖
      = ‖∫ s in (0:ℝ)..1, (fderiv ℝ f (x - s • y)) (-y)‖ := by
        rw [hFTC, hγ1, hγ0, norm_sub_rev]
    _ ≤ ∫ s in (0:ℝ)..1, ‖(fderiv ℝ f (x - s • y)) (-y)‖ :=
        norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ s in (0:ℝ)..1, ‖fderiv ℝ f (x - s • y)‖ * ‖y‖ := by
        apply integral_mono zero_le_one
        · exact hcontN.intervalIntegrable 0 1
        · exact hcontM.intervalIntegrable 0 1
        · intro s
          calc ‖(fderiv ℝ f (x - s • y)) (-y)‖
              ≤ ‖fderiv ℝ f (x - s • y)‖ * ‖-y‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖fderiv ℝ f (x - s • y)‖ * ‖y‖ := by rw [norm_neg]

end Work.BoseSym.MollifyAux
