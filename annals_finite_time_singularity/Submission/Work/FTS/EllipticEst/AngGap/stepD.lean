import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- Hints: the integrand `F θ = (deriv h θ - 2 cot(2θ) h θ)² - (deriv h θ)² + 4 (h θ)²`
is the derivative on `(0,π/2)` of `angPhiD h θ = -2 (h θ)² cot(2θ)` (product rule with
`hasDerivAt_cot_two` from `Defs.lean`, then `ring`).  `angPhiD h` tends to `0` at both
endpoints by `squeeze_zero'`: `|angPhiD h θ| ≤ 2 C² sin(2θ)` using `hbdd` and
`abs_cot_two_le`.  `F` is continuous on `Ioo 0 (π/2)` and bounded there by `hbdd`,`hbdd'`,
so `IntervalIntegrable F volume 0 (π/2)` (`Integrable.of_bound` on `Ioo`, moved to `uIcc` by
`MeasureTheory.Ioo_ae_eq_Icc`).  Then
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` gives `∫ F = 0` over `0..π/2`;
transfer to the set integral over `Iθ` with `MeasureTheory.integral_Icc_eq_integral_Ioc` and
`intervalIntegral.integral_of_le`, and split with `integral_add`/`integral_sub`. -/
theorem stepD (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (h0 : h 0 = 0)
    (h1 : h (π / 2) = 0) (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C) :
    (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) - 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- ## continuity of the ingredients on the open interval
  have hcontH : ContinuousOn h (Set.Ioo (0 : ℝ) (π / 2)) := (hh.mono hsub).continuousOn
  have hcontD : ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hh.mono hsub).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontCot : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) := by
    have hfun : (fun θ : ℝ => Real.cot (2 * θ))
        = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
      funext θ; rw [Real.cot_eq_cos_div_sin]
    rw [hfun]
    exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).div
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
      (fun θ hθ => ne_of_gt (sin_two_pos hθ))
  -- ## elementary pointwise bounds
  have hhbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |h θ| ≤ C := by
    intro θ hθ
    have h1' := hbdd θ (hsub hθ)
    have h2' : C * Real.sin (2 * θ) ≤ C :=
      mul_le_of_le_one_right (le_of_lt hC) (Real.sin_le_one (2 * θ))
    linarith
  have hderiv_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv h θ - 2 * Real.cot (2 * θ) * h θ| ≤ 3 * C := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hcot := abs_cot_two_le hθ
    have h2 : |2 * Real.cot (2 * θ) * h θ| ≤ 2 * C := by
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      calc 2 * |Real.cot (2 * θ)| * |h θ|
          ≤ 2 * (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hcot (by norm_num))
              (hbdd θ (hsub hθ)) (by positivity) (by positivity)
        _ = 2 * C := by
            have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
            field_simp
    have htri : |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [le_abs_self (deriv h θ),
                neg_abs_le (2 * Real.cot (2 * θ) * h θ)],
             by linarith [neg_abs_le (deriv h θ),
                le_abs_self (2 * Real.cot (2 * θ) * h θ)]⟩
    calc |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := htri
      _ ≤ C + 2 * C := add_le_add (hbdd' θ hθ) h2
      _ = 3 * C := by ring
  -- ## squared bounds
  have hAsq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 ≤ 9 * C ^ 2 := by
    intro θ hθ
    calc (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2
        = |deriv h θ - 2 * Real.cot (2 * θ) * h θ| ^ 2 := (sq_abs _).symm
      _ ≤ (3 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hderiv_le θ hθ) 2
      _ = 9 * C ^ 2 := by ring
  have hBsq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), (deriv h θ) ^ 2 ≤ C ^ 2 := by
    intro θ hθ
    calc (deriv h θ) ^ 2 = |deriv h θ| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbdd' θ hθ) 2
  have hCsq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 4 * (h θ) ^ 2 ≤ 4 * C ^ 2 := by
    intro θ hθ
    have h2 : (h θ) ^ 2 ≤ C ^ 2 := by
      calc (h θ) ^ 2 = |h θ| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hhbd θ hθ) 2
    linarith
  -- ## the pointwise bound for the integrand `F`
  have hboundF : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ‖(deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2‖
        ≤ 14 * C ^ 2 := by
    intro θ hθ
    have hA := hAsq θ hθ
    have hB := hBsq θ hθ
    have hD := hCsq θ hθ
    rw [Real.norm_eq_abs]
    have hA0 : 0 ≤ (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 := sq_nonneg _
    have hB0 : 0 ≤ (deriv h θ) ^ 2 := sq_nonneg _
    have hD0 : 0 ≤ 4 * (h θ) ^ 2 := by positivity
    have htri : |(deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
          + 4 * (h θ) ^ 2|
        ≤ (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 + (deriv h θ) ^ 2 + 4 * (h θ) ^ 2 := by
      rw [abs_le]
      constructor <;> linarith
    calc |(deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
          + 4 * (h θ) ^ 2|
        ≤ (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 + (deriv h θ) ^ 2 + 4 * (h θ) ^ 2 :=
          htri
      _ ≤ 9 * C ^ 2 + C ^ 2 + 4 * C ^ 2 := by linarith
      _ = 14 * C ^ 2 := by ring
  -- ## endpoint limits of the primitive
  have hphi_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ‖angPhiD h θ‖ ≤ 2 * C ^ 2 * Real.sin (2 * θ) := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hsq : (h θ) ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 := by
      calc (h θ) ^ 2 = |h θ| ^ 2 := (sq_abs _).symm
        _ ≤ (C * Real.sin (2 * θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hbdd θ (hsub hθ)) 2
    have habs : |angPhiD h θ| = 2 * (h θ) ^ 2 * |Real.cot (2 * θ)| := by
      rw [show angPhiD h θ = -2 * (h θ) ^ 2 * Real.cot (2 * θ) from rfl,
        abs_mul, abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (sq_nonneg (h θ))]
    rw [Real.norm_eq_abs, habs]
    calc 2 * (h θ) ^ 2 * |Real.cot (2 * θ)|
        ≤ 2 * (C * Real.sin (2 * θ)) ^ 2 * |Real.cot (2 * θ)| :=
          mul_le_mul_of_nonneg_right (by linarith [hsq]) (abs_nonneg _)
      _ ≤ 2 * (C * Real.sin (2 * θ)) ^ 2 * (1 / Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_left (abs_cot_two_le hθ) (by positivity)
      _ = 2 * C ^ 2 * Real.sin (2 * θ) := by
          have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
          field_simp
  have htend0 : Tendsto (angPhiD h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsin0 : Tendsto (fun θ : ℝ => 2 * C ^ 2 * Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (0 : ℝ))
            (𝓝 (Real.sin (2 * (0 : ℝ)))) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
        rw [show Real.sin (2 * (0 : ℝ)) = 0 by simp] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      simpa using Tendsto.const_mul (2 * C ^ 2) h1'
    refine squeeze_zero_norm' ?_ hsin0
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact hphi_le θ hθ
  have htendπ : Tendsto (angPhiD h) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hsinπ : Tendsto (fun θ : ℝ => 2 * C ^ 2 * Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
      have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
        have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (π / 2))
            (𝓝 (Real.sin (2 * (π / 2)))) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
        rw [show Real.sin (2 * (π / 2)) = 0 by
              rw [show 2 * (π / 2) = π by ring, Real.sin_pi]] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      simpa using Tendsto.const_mul (2 * C ^ 2) h1'
    refine squeeze_zero_norm' ?_ hsinπ
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    exact hphi_le θ hθ
  -- ## derivative of the primitive
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), HasDerivAt (angPhiD h)
      ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2) θ := by
    intro θ hθ
    have hhAt : HasDerivAt h (deriv h θ) θ :=
      ((hh.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by norm_num)).hasDerivAt
    have hprod := ((hhAt.pow 2).const_mul (-2)).mul (hasDerivAt_cot_two θ hθ)
    refine hprod.congr_deriv ?_
    simp only [Pi.pow_apply]
    ring
  -- ## a general integrability criterion on `Iθ`
  have int_bdd : ∀ (g : ℝ → ℝ) (M : ℝ), ContinuousOn g (Set.Ioo (0 : ℝ) (π / 2)) →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), ‖g θ‖ ≤ M) →
      Integrable g (volume.restrict Work.Spaces.Iθ) := by
    intro g M hcont hbnd
    have hIoo : Integrable g (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine Integrable.of_bound (hcont.aestronglyMeasurable measurableSet_Ioo) M ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hbnd θ hθ
    have hIcc : Integrable g (volume.restrict (Set.Icc (0 : ℝ) (π / 2))) := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
      exact hIoo
    exact hIcc
  -- ## integrability of the pieces
  have hcontA : ContinuousOn (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hcontD.sub ((hcontCot.const_mul 2).mul hcontH)).pow 2
  have hcontB : ContinuousOn (fun θ : ℝ => (deriv h θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hcontD.pow 2
  have hcontCc : ContinuousOn (fun θ : ℝ => 4 * (h θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hcontH.pow 2).const_mul 4
  have hAint : Integrable (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    int_bdd (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2) (9 * C ^ 2) hcontA
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hAsq θ hθ)
  have hBint : Integrable (fun θ : ℝ => (deriv h θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    int_bdd (fun θ : ℝ => (deriv h θ) ^ 2) (C ^ 2) hcontB
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hBsq θ hθ)
  have hCint : Integrable (fun θ : ℝ => 4 * (h θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    int_bdd (fun θ : ℝ => 4 * (h θ) ^ 2) (4 * C ^ 2) hcontCc
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hCsq θ hθ)
  have hcontF : ContinuousOn
      (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
        + 4 * (h θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hcontA.sub hcontB).add hcontCc
  have hFint : Integrable
      (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
        + 4 * (h θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    int_bdd _ (14 * C ^ 2) hcontF hboundF
  -- ## interval integrability on `0..π/2`
  have hIntF : IntervalIntegrable
      (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
        + 4 * (h θ) ^ 2) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpi2.le]
    show Integrable _ (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
    exact hFint
  -- ## the fundamental theorem of calculus
  have hFTC : (∫ θ in (0 : ℝ)..(π / 2),
      ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2 hderiv hIntF
      htend0 htendπ
    simpa using h
  have hzero : (∫ θ in Work.Spaces.Iθ,
      ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2)) = 0 := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hpi2.le]
    exact hFTC
  -- ## splitting the integral
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
        - (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, 4 * (h θ) ^ 2) := by
    have e1 : (∫ θ in Work.Spaces.Iθ,
          ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2) + 4 * (h θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2))
          + (∫ θ in Work.Spaces.Iθ, 4 * (h θ) ^ 2) :=
      integral_add (hAint.sub hBint) hCint
    have e2 : (∫ θ in Work.Spaces.Iθ,
            ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2))
        = (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
          - (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) :=
      integral_sub hAint hBint
    linarith [e1, e2]
  have hCmul : (∫ θ in Work.Spaces.Iθ, 4 * (h θ) ^ 2)
      = 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) :=
    integral_const_mul 4 (fun θ : ℝ => (h θ) ^ 2)
  linarith [hzero, hsplit, hCmul]

end Work.FTS.EllipticEst.AngGap
