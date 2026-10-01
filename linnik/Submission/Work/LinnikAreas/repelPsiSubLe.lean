import Mathlib
import Submission.Work.LinnikAreas.RepelDefs

/-!
# The global finite-difference bound for the triangular kernel `Ψ`

`repelPsi u - repelPsi (u - w) ≤ w e^u / 6` for `0 ≤ u`, `0 ≤ w`.

Unlike `repelPsiDiffBound`/`repelW_diff`, which require `0 < a` (and give `δ e^a / a²`, useful
only for large `a`), this bound is uniform in `u ≥ 0`; its value comes from `∫₀¹ t(1-t) dt = 1/6`,
which bounds the derivative `Ψ'(u) = ∫₀¹ t(1-t) e^{ut} dt ≤ e^u/6`.

The proof is a direct integral comparison. With `repelPsi u = ∫₀¹ e^{ut}(1-t) dt`,

`Ψ u - Ψ (u-w) = ∫₀¹ (e^{ut} - e^{(u-w)t})(1-t) dt`,

and pointwise, using `1 - x ≤ e^{-x}` in the form `e^{y} - 1 ≤ y e^{y}`,
`e^{ut} - e^{(u-w)t} = e^{(u-w)t}(e^{wt} - 1) ≤ w t e^{ut}`.
Since `u ≥ 0` and `t ≤ 1` give `e^{ut} ≤ e^u`, the difference is at most `w e^u t`, and
multiplying by `1 - t ≥ 0` and integrating yields `w e^u ∫₀¹ t(1-t) dt = w e^u/6`.
No restriction relating `w` to `u` is needed.
-/

namespace Work.LinnikAreas

open MeasureTheory intervalIntegral

/-- `∫₀¹ t(1-t) dt = 1/6`, the second moment of the triangle. -/
lemma repel_tri_integral : ∫ t in (0:ℝ)..1, t * (1 - t) = 1 / 6 := by
  have he : (fun t : ℝ => t * (1 - t)) = (fun t : ℝ => t - t ^ 2) := by funext t; ring
  rw [he,
    intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun t : ℝ => t ^ 2)
      (continuous_id.intervalIntegrable (0:ℝ) 1)
      ((continuous_id.pow 2).intervalIntegrable (0:ℝ) 1)]
  rw [integral_id, integral_pow]
  norm_num

theorem repelPsiSubLe {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    repelPsi u - repelPsi (u - w) ≤ w * Real.exp u / 6 := by
  have hf : IntervalIntegrable (fun t : ℝ => Real.exp (u*t)*(1-t)) volume (0:ℝ) 1 :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (u*t)*(1-t)).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun t : ℝ => Real.exp ((u-w)*t)*(1-t)) volume (0:ℝ) 1 :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp ((u-w)*t)*(1-t)).intervalIntegrable _ _
  have hsub : repelPsi u - repelPsi (u-w)
      = ∫ t in (0:ℝ)..1, (Real.exp (u*t) - Real.exp ((u-w)*t))*(1-t) := by
    rw [repelPsi, repelPsi, ← intervalIntegral.integral_sub hf hg]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hsub]
  -- pointwise: integrand ≤ w * (t*(1-t)*e^{ut})
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (Real.exp (u*t) - Real.exp ((u-w)*t))*(1-t) ≤ w * (t*(1-t)*Real.exp (u*t)) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := by linarith
    have hkey : Real.exp (w*t) - 1 ≤ w*t*Real.exp (w*t) := by
      have h := Real.one_sub_le_exp_neg (w*t)
      have hpos : 0 < Real.exp (w*t) := Real.exp_pos _
      have h2 : (1 - w*t) * Real.exp (w*t) ≤ Real.exp (-(w*t)) * Real.exp (w*t) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hpos)
      rw [Real.exp_neg, inv_mul_cancel₀ (ne_of_gt hpos)] at h2
      nlinarith [h2]
    have hbm : Real.exp (u*t) = Real.exp ((u-w)*t) * Real.exp (w*t) := by
      rw [← Real.exp_add]; congr 1; ring
    have key : Real.exp (u*t) - Real.exp ((u-w)*t) ≤ w*t*Real.exp (u*t) := by
      calc Real.exp (u*t) - Real.exp ((u-w)*t)
          = Real.exp ((u-w)*t) * (Real.exp (w*t) - 1) := by rw [hbm]; ring
        _ ≤ Real.exp ((u-w)*t) * (w*t*Real.exp (w*t)) :=
              mul_le_mul_of_nonneg_left hkey (le_of_lt (Real.exp_pos _))
        _ = w*t*Real.exp (u*t) := by rw [hbm]; ring
    calc (Real.exp (u*t) - Real.exp ((u-w)*t))*(1-t)
        ≤ (w*t*Real.exp (u*t))*(1-t) := mul_le_mul_of_nonneg_right key h1t
      _ = w * (t*(1-t)*Real.exp (u*t)) := by ring
  -- the kernel integral is at most e^u/6
  have hker : ∫ t in (0:ℝ)..1, t*(1-t)*Real.exp (u*t) ≤ Real.exp u / 6 := by
    have hpt2 : ∀ t ∈ Set.Icc (0:ℝ) 1, t*(1-t)*Real.exp (u*t) ≤ t*(1-t)*Real.exp u := by
      intro t ht
      have hfac : 0 ≤ t*(1-t) := mul_nonneg ht.1 (by linarith [ht.2])
      have hexp : Real.exp (u*t) ≤ Real.exp u := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hu (sub_nonneg.mpr ht.2)]
      exact mul_le_mul_of_nonneg_left hexp hfac
    have hI1 : IntervalIntegrable (fun t : ℝ => t*(1-t)*Real.exp (u*t)) volume (0:ℝ) 1 :=
      (by fun_prop : Continuous fun t : ℝ => t*(1-t)*Real.exp (u*t)).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun t : ℝ => t*(1-t)*Real.exp u) volume (0:ℝ) 1 :=
      (by fun_prop : Continuous fun t : ℝ => t*(1-t)*Real.exp u).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hI1 hI2 hpt2
    have hval : ∫ t in (0:ℝ)..1, t*(1-t)*Real.exp u = Real.exp u / 6 := by
      have he : (fun t : ℝ => t*(1-t)*Real.exp u) = (fun t : ℝ => Real.exp u * (t*(1-t))) := by
        funext t; ring
      rw [he, intervalIntegral.integral_const_mul, repel_tri_integral]
      ring
    rw [hval] at hm
    exact hm
  have hfI : IntervalIntegrable (fun t : ℝ => (Real.exp (u*t) - Real.exp ((u-w)*t))*(1-t))
      volume (0:ℝ) 1 :=
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (u*t) - Real.exp ((u-w)*t))*(1-t)).intervalIntegrable _ _
  have hgI : IntervalIntegrable (fun t : ℝ => w * (t*(1-t)*Real.exp (u*t))) volume (0:ℝ) 1 :=
    (by fun_prop : Continuous fun t : ℝ => w * (t*(1-t)*Real.exp (u*t))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hfI hgI hpt
  have hgval : ∫ t in (0:ℝ)..1, w * (t*(1-t)*Real.exp (u*t))
      = w * ∫ t in (0:ℝ)..1, t*(1-t)*Real.exp (u*t) :=
    intervalIntegral.integral_const_mul w _
  calc ∫ t in (0:ℝ)..1, (Real.exp (u*t) - Real.exp ((u-w)*t))*(1-t)
      ≤ ∫ t in (0:ℝ)..1, w * (t*(1-t)*Real.exp (u*t)) := hmono
    _ = w * ∫ t in (0:ℝ)..1, t*(1-t)*Real.exp (u*t) := hgval
    _ ≤ w * (Real.exp u / 6) := mul_le_mul_of_nonneg_left hker hw
    _ = w * Real.exp u / 6 := by ring

end Work.LinnikAreas
