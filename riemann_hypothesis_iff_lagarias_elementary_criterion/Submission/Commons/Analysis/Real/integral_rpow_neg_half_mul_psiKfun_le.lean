import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open MeasureTheory intervalIntegral Set

noncomputable section

/-- `log` is continuous on `[x,Y]` when `1 < x`. -/
private lemma log_contOn_Icc (x Y : ℝ) (hx : 1 < x) :
    ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc x Y) := by
  intro t ht
  exact (Real.continuousAt_log (ne_of_gt (by linarith [ht.1]))).continuousWithinAt

/-- The antiderivative candidate `t ↦ -(t^{-3/2} / log t)` is continuous on `[x,Y]` when `1 < x`. -/
private lemma F_contOn_Icc (x Y : ℝ) (hx : 1 < x) :
    ContinuousOn (fun s : ℝ => -(s ^ ((-3:ℝ)/2) * (Real.log s)⁻¹)) (Set.Icc x Y) := by
  apply ContinuousOn.neg
  apply ContinuousOn.mul
  · apply continuousOn_id.rpow_const
    intro t ht
    left
    exact ne_of_gt (by show (0:ℝ) < t; linarith [ht.1])
  · apply ContinuousOn.inv₀ (log_contOn_Icc x Y hx)
    intro t ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))

/-- The majorant `t ↦ t^{-5/2} * (3/2 log t + 1)/log²t` is continuous on `[x,Y]` when `1 < x`. -/
private lemma G_contOn_Icc (x Y : ℝ) (hx : 1 < x) :
    ContinuousOn
      (fun s : ℝ => s ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log s + 1) / (Real.log s)^2))
      (Set.Icc x Y) := by
  apply ContinuousOn.mul
  · apply continuousOn_id.rpow_const
    intro t ht
    left
    exact ne_of_gt (by show (0:ℝ) < t; linarith [ht.1])
  · apply ContinuousOn.div
    · exact ((log_contOn_Icc x Y hx).const_mul ((3:ℝ)/2)).add_const 1
    · exact (log_contOn_Icc x Y hx).pow 2
    · intro t ht
      exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1])))

/-- The integrand `t ↦ t^{-1/2} * (log t + 1)/(t² log²t)` is continuous on `[x,Y]` when `1 < x`. -/
private lemma I_contOn_Icc (x Y : ℝ) (hx : 1 < x) :
    ContinuousOn
      (fun s : ℝ => s ^ ((-1:ℝ)/2) * ((Real.log s + 1) / (s ^ 2 * (Real.log s) ^ 2)))
      (Set.Icc x Y) := by
  apply ContinuousOn.mul
  · apply continuousOn_id.rpow_const
    intro t ht
    left
    exact ne_of_gt (by show (0:ℝ) < t; linarith [ht.1])
  · apply ContinuousOn.div
    · exact (log_contOn_Icc x Y hx).add_const 1
    · exact (continuousOn_id.pow 2).mul ((log_contOn_Icc x Y hx).pow 2)
    · intro t ht
      apply mul_ne_zero
      · exact pow_ne_zero 2 (ne_of_gt (by show (0:ℝ) < t; linarith [ht.1]))
      · exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1])))

/-- Derivative of `t ↦ -(t^{-3/2} / log t)`. -/
private lemma F_hasDerivAt (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => -(s ^ ((-3:ℝ)/2) * (Real.log s)⁻¹))
      (t ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log t + 1) / (Real.log t)^2)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t ≠ 1 := by linarith
  have htm1 : t ≠ -1 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h1 : HasDerivAt (fun s : ℝ => s ^ ((-3:ℝ)/2))
      (((-3:ℝ)/2) * t ^ (((-3:ℝ)/2) - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht0)
  have h2 : HasDerivAt (fun s : ℝ => (Real.log s)⁻¹) (-t⁻¹ / (Real.log t)^2) t :=
    Real.hasDerivAt_inv_log ht0 ht1 htm1
  have h3 : HasDerivAt (fun s : ℝ => s ^ ((-3:ℝ)/2) * (Real.log s)⁻¹)
      (((-3:ℝ)/2) * t ^ (((-3:ℝ)/2) - 1) * (Real.log t)⁻¹
        + t ^ ((-3:ℝ)/2) * (-t⁻¹ / (Real.log t)^2)) t :=
    h1.mul h2
  refine h3.neg.congr_deriv ?_
  rw [show (((-3:ℝ)/2) - 1) = ((-5:ℝ)/2) by norm_num]
  rw [show ((-3:ℝ)/2) = ((-5:ℝ)/2) + 1 by norm_num]
  rw [Real.rpow_add (by linarith : (0:ℝ) < t)]
  norm_num
  field_simp
  ring

/-- Pointwise comparison of the integrand with the majorant. -/
private lemma I_le_G (t : ℝ) (ht : 1 < t) :
    t ^ ((-1:ℝ)/2) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤
      t ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log t + 1) / (Real.log t)^2) := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hlne : Real.log t ≠ 0 := ne_of_gt hl
  have hB : t ^ ((-5:ℝ)/2) = t ^ ((-1:ℝ)/2) / t^2 := by
    rw [eq_div_iff (by positivity : (t:ℝ)^2 ≠ 0), mul_comm, ← Real.rpow_natCast t 2,
      ← Real.rpow_add ht0]
    norm_num
  rw [hB]
  have hrw : (t ^ ((-1:ℝ)/2) / t^2) * (((3:ℝ)/2 * Real.log t + 1) / (Real.log t)^2)
      = t ^ ((-1:ℝ)/2) * (((3:ℝ)/2 * Real.log t + 1) / (t^2 * (Real.log t)^2)) := by
    field_simp
  rw [hrw]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt ht0) _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- Lagarias-criterion estimate: for `1 < x ≤ Y`,
`∫_x^Y t^{-1/2} (log t + 1)/(t² log²t) dt ≤ 2 x^{-3/2}/log x`. -/
theorem integral_rpow_neg_half_mul_psiKfun_le {x Y : ℝ} (hx : 1 < x) (hxY : x ≤ Y) :
    (∫ t in x..Y, t ^ (-(1 / 2) : ℝ) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) ≤
      2 * x ^ (-(3 / 2) : ℝ) / Real.log x := by
  rw [show (-(1/2):ℝ) = ((-1:ℝ)/2) by norm_num,
      show (-(3/2):ℝ) = ((-3:ℝ)/2) by norm_num]
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hI_int : IntervalIntegrable
      (fun s : ℝ => s ^ ((-1:ℝ)/2) * ((Real.log s + 1) / (s ^ 2 * (Real.log s) ^ 2)))
      volume x Y :=
    (I_contOn_Icc x Y hx).intervalIntegrable_of_Icc hxY
  have hG_int : IntervalIntegrable
      (fun s : ℝ => s ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log s + 1) / (Real.log s)^2))
      volume x Y :=
    (G_contOn_Icc x Y hx).intervalIntegrable_of_Icc hxY
  have hmono :
      (∫ s in x..Y, s ^ ((-1:ℝ)/2) * ((Real.log s + 1) / (s ^ 2 * (Real.log s) ^ 2)))
        ≤ ∫ s in x..Y, s ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log s + 1) / (Real.log s)^2) := by
    apply integral_mono_on hxY hI_int hG_int
    intro s hs
    exact I_le_G s (lt_of_lt_of_le hx hs.1)
  have hF_deriv : ∀ s ∈ Set.Ioo x Y,
      HasDerivAt (fun u : ℝ => -(u ^ ((-3:ℝ)/2) * (Real.log u)⁻¹))
        (s ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log s + 1) / (Real.log s)^2)) s :=
    fun s hs => F_hasDerivAt s (lt_trans hx hs.1)
  have hftc :
      (∫ s in x..Y, s ^ ((-5:ℝ)/2) * (((3:ℝ)/2 * Real.log s + 1) / (Real.log s)^2))
        = (fun u : ℝ => -(u ^ ((-3:ℝ)/2) * (Real.log u)⁻¹)) Y
          - (fun u : ℝ => -(u ^ ((-3:ℝ)/2) * (Real.log u)⁻¹)) x :=
    integral_eq_sub_of_hasDerivAt_of_le hxY (F_contOn_Icc x Y hx) hF_deriv hG_int
  rw [hftc] at hmono
  have hbound :
      (fun u : ℝ => -(u ^ ((-3:ℝ)/2) * (Real.log u)⁻¹)) Y
        - (fun u : ℝ => -(u ^ ((-3:ℝ)/2) * (Real.log u)⁻¹)) x
        ≤ 2 * x ^ ((-3:ℝ)/2) / Real.log x := by
    simp only
    have hY0 : 0 < Y := by linarith
    have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
    have hA0 : 0 ≤ Y ^ ((-3:ℝ)/2) * (Real.log Y)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hY0) _) (inv_nonneg.mpr (le_of_lt hlogY))
    have hB0 : 0 ≤ x ^ ((-3:ℝ)/2) * (Real.log x)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (inv_nonneg.mpr (le_of_lt hlogx))
    have h1 : -(Y ^ ((-3:ℝ)/2) * (Real.log Y)⁻¹) - -(x ^ ((-3:ℝ)/2) * (Real.log x)⁻¹)
        = x ^ ((-3:ℝ)/2) * (Real.log x)⁻¹ - Y ^ ((-3:ℝ)/2) * (Real.log Y)⁻¹ := by ring
    rw [h1]
    have h3 : x ^ ((-3:ℝ)/2) * (Real.log x)⁻¹ ≤ 2 * x ^ ((-3:ℝ)/2) / Real.log x := by
      have h : 2 * x ^ ((-3:ℝ)/2) / Real.log x
          = 2 * (x ^ ((-3:ℝ)/2) * (Real.log x)⁻¹) := by ring
      rw [h]
      nlinarith [hB0]
    linarith
  linarith [hmono, hbound]

end

end Commons.Analysis.Real