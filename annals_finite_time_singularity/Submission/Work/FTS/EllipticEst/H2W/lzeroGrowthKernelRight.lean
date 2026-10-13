import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.H2W

/-- **Pointwise domination of the right half of the `L₀`-kernel.**

For `s ∈ [π/4, π/2)` one has, writing `δ = π/2 - s ∈ (0, π/4]`,
`cos s = sin δ` and `sin (2s) = sin (2δ)`, so

`1/(cos s · sin²(2s)) = 1/(sin δ · sin²(2δ))`.

Jordan's inequality `sin x ≥ (2/π) x` on `[0, π/2]` applied to `δ` and to `2δ` gives
`sin δ ≥ (2/π) δ` and `sin (2δ) ≥ (4/π) δ`, whence
`sin δ · sin²(2δ) ≥ 32 δ³ / π³`, i.e. the bound below. -/
lemma lzeroGrowthKernelRight_pointwise {s : ℝ} (hs1 : Real.pi / 4 ≤ s)
    (hs2 : s < Real.pi / 2) :
    1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ Real.pi ^ 3 / (32 * (Real.pi / 2 - s) ^ 3) := by
  set δ := Real.pi / 2 - s with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδle : δ ≤ Real.pi / 4 := by rw [hδ]; linarith
  have hδ2le : 2 * δ ≤ Real.pi / 2 := by linarith
  have hδ2pos : 0 < 2 * δ := by linarith
  have hs_eq : s = Real.pi / 2 - δ := by rw [hδ]; ring
  have hcos : Real.cos s = Real.sin δ := by rw [hs_eq, Real.cos_pi_div_two_sub]
  have hsin : Real.sin (2 * s) = Real.sin (2 * δ) := by
    have : 2 * s = Real.pi - 2 * δ := by rw [hs_eq]; ring
    rw [this, Real.sin_pi_sub]
  have hsin1 : 2 / Real.pi * δ ≤ Real.sin δ :=
    Real.mul_le_sin (le_of_lt hδpos) (by linarith)
  have hsin2 : 2 / Real.pi * (2 * δ) ≤ Real.sin (2 * δ) :=
    Real.mul_le_sin (le_of_lt hδ2pos) hδ2le
  have hsinδ_pos : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith)
  have hab : (2 / Real.pi * δ) * (2 / Real.pi * (2 * δ)) ^ 2
      ≤ Real.sin δ * (Real.sin (2 * δ)) ^ 2 := by
    apply mul_le_mul hsin1 _ (by positivity) (le_of_lt hsinδ_pos)
    exact pow_le_pow_left₀ (by positivity) hsin2 2
  have h1 : 1 / (Real.sin δ * (Real.sin (2 * δ)) ^ 2)
      ≤ 1 / ((2 / Real.pi * δ) * (2 / Real.pi * (2 * δ)) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hab
  have h2 : 1 / ((2 / Real.pi * δ) * (2 / Real.pi * (2 * δ)) ^ 2)
      = Real.pi ^ 3 / (32 * δ ^ 3) := by
    field_simp
    ring
  rw [hcos, hsin]
  calc 1 / (Real.sin δ * (Real.sin (2 * δ)) ^ 2)
      ≤ 1 / ((2 / Real.pi * δ) * (2 / Real.pi * (2 * δ)) ^ 2) := h1
    _ = Real.pi ^ 3 / (32 * δ ^ 3) := h2

/-- Derivative bookkeeping: the value produced by differentiating
`π³/64 · (π/2 - x)^{-2}` equals `π³/(32·(π/2 - x)³)`. -/
lemma lzeroGrowthKernelRight_derivAux {u : ℝ} (hu : 0 < u) :
    Real.pi ^ 3 / 64 * ((-2:ℝ) * u ^ ((-2:ℝ) - 1) * (-1)) = Real.pi ^ 3 / (32 * u ^ 3) := by
  rw [show ((-2:ℝ) - 1) = -(3:ℝ) by norm_num, Real.rpow_neg (le_of_lt hu), Real.rpow_ofNat]
  field_simp
  ring

theorem lzeroGrowthKernelRight {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    ∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ (Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2 := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hε : 0 < Real.pi / 2 - θ := by linarith
  -- Integrability of the two integrands on `[π/4, θ]`.
  have hcontF : ContinuousOn
      (fun s : ℝ => 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) (Set.uIcc (Real.pi / 4) θ) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuous_cos.continuousOn.mul
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 2))
    · intro x hx
      rw [Set.uIcc_of_le hθ1] at hx
      exact mul_ne_zero
        (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩))
        (pow_ne_zero 2 (ne_of_gt
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2]))))
  have hI1 : IntervalIntegrable
      (fun s : ℝ => 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) volume (Real.pi / 4) θ :=
    hcontF.intervalIntegrable
  have hcontG : ContinuousOn
      (fun s : ℝ => Real.pi ^ 3 / (32 * (Real.pi / 2 - s) ^ 3)) (Set.uIcc (Real.pi / 4) θ) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_const.mul ((continuous_const.sub continuous_id).continuousOn.pow 3)
    · intro x hx
      rw [Set.uIcc_of_le hθ1] at hx
      have hpx : 0 < Real.pi / 2 - x := by linarith [hx.2]
      exact ne_of_gt (mul_pos (by norm_num) (pow_pos hpx 3))
  have hI2 : IntervalIntegrable
      (fun s : ℝ => Real.pi ^ 3 / (32 * (Real.pi / 2 - s) ^ 3)) volume (Real.pi / 4) θ :=
    hcontG.intervalIntegrable
  -- Monotonicity of the integral with the pointwise bound.
  have hmono : ∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ ∫ s in (Real.pi / 4)..θ, Real.pi ^ 3 / (32 * (Real.pi / 2 - s) ^ 3) :=
    intervalIntegral.integral_mono_on hθ1 hI1 hI2
      (fun x hx => lzeroGrowthKernelRight_pointwise hx.1 (lt_of_le_of_lt hx.2 hθ2))
  -- The comparison integral, via the fundamental theorem of calculus.
  have hderiv : ∀ x ∈ Set.uIcc (Real.pi / 4) θ,
      HasDerivAt (fun s : ℝ => Real.pi ^ 3 / 64 * (Real.pi / 2 - s) ^ (-2:ℝ))
        (Real.pi ^ 3 / (32 * (Real.pi / 2 - x) ^ 3)) x := by
    intro x hx
    rw [Set.uIcc_of_le hθ1] at hx
    have hxpos : 0 < Real.pi / 2 - x := by linarith [hx.2]
    have hlin : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
    have hp : HasDerivAt (fun y : ℝ => y ^ (-2:ℝ))
        ((-2:ℝ) * (Real.pi / 2 - x) ^ ((-2:ℝ) - 1)) (Real.pi / 2 - x) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))
    have hcomp : HasDerivAt (fun s : ℝ => (Real.pi / 2 - s) ^ (-2:ℝ))
        (((-2:ℝ) * (Real.pi / 2 - x) ^ ((-2:ℝ) - 1)) * (-1)) x :=
      hp.comp x hlin
    have hfin := hcomp.const_mul (Real.pi ^ 3 / 64)
    exact hfin.congr_deriv (lzeroGrowthKernelRight_derivAux hxpos)
  have hFTC : ∫ s in (Real.pi / 4)..θ, Real.pi ^ 3 / (32 * (Real.pi / 2 - s) ^ 3)
      = Real.pi ^ 3 / 64 * (Real.pi / 2 - θ) ^ (-2:ℝ)
        - Real.pi ^ 3 / 64 * (Real.pi / 2 - Real.pi / 4) ^ (-2:ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hI2
  have hY : 0 ≤ Real.pi ^ 3 / 64 * (Real.pi / 2 - Real.pi / 4) ^ (-2:ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)
  have hX : Real.pi ^ 3 / 64 / (Real.pi / 2 - θ) ^ 2
      = Real.pi ^ 3 / 64 * (Real.pi / 2 - θ) ^ (-2:ℝ) := by
    rw [Real.rpow_neg hε.le, Real.rpow_ofNat, div_eq_mul_inv]
  calc ∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ ∫ s in (Real.pi / 4)..θ, Real.pi ^ 3 / (32 * (Real.pi / 2 - s) ^ 3) := hmono
    _ = Real.pi ^ 3 / 64 * (Real.pi / 2 - θ) ^ (-2:ℝ)
        - Real.pi ^ 3 / 64 * (Real.pi / 2 - Real.pi / 4) ^ (-2:ℝ) := hFTC
    _ ≤ (Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2 := by
        rw [hX]; linarith

end Work.FTS.EllipticEst.H2W
