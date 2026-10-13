/-
Copyright: work module for the Elgindi finite-time singularity project.

# The difference-quotient bound for the mode numerator `numW`

This file proves the quantitative heart of `cmode_Dz`: for a source `F` which is `C^∞` on the
open quadrant together with the `θ`-slice integrability hypotheses and the second-order slice
bound `|∂_z²F(τ,θ)| ≤ (2/τ²)·√(HkIntegrand α 2 F τ θ)`, the difference quotient of
`numW m F` at `z₀` differs from `pwF m F z₀` by at most

  `Cφ · (2/a²) · ∫_{uIoc z₀ x} Hsq α F`

where `Cφ` bounds the angular weight `φ_m = e_m cos` on `Iθ`, `a > 0` is a lower bound for the
radii involved, and `Hsq α F τ = ∫_θ √(HkIntegrand α 2 F τ θ)`.

The chain of inequalities is

* linearity of the `θ`-integral (the remainder is the integral of the pointwise remainder);
* `|∫| ≤ ∫|·|` and the pointwise bound `|φ_m| ≤ Cφ`;
* the second-order FTC bound `ftc2_bound`;
* pulling out the constant `|x - z₀|` and Tonelli (`hswap`);
* the `θ`-slice bound for `∂_z²F`, with `2/τ² ≤ 2/a²` on the range of radii.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.Zpz.Defs
import Submission.Work.FTS.ClassCHon.Zpz.Ftc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The `z`-slope bound.**  Under the integrability and slice-bound hypotheses, the difference
quotient of `numW m F` at `z₀` differs from `pwF m F z₀` by at most
`Cφ · (2/a²) · ∫_{uIoc z₀ x} Hsq α F` — the factor `2/a²` being the `θ`-slice bound for
`∂_z²F` on the interval of radii `≥ a`. -/
theorem slope_bound {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ) {Cφ : ℝ} (hCφnn : 0 ≤ Cφ)
    (hCφ : ∀ θ ∈ Work.Spaces.Iθ, |phiW m θ| ≤ Cφ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hphi : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => F z θ * phiW m θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz F z θ * phiW m θ)
        Work.Spaces.Iθ)
    (habs : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => |F z θ|) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F z θ|) Work.Spaces.Iθ)
    (hpt2 : ∀ τ θ : ℝ, 0 < τ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |Work.Spaces.pzIter 2 F τ θ|
        ≤ (2 / τ ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
    (hsl : ∀ τ : ℝ, 0 ≤ τ → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) Work.Spaces.Iθ)
    (hout : ∀ a b : ℝ, 0 < a → MeasureTheory.IntegrableOn
      (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) (Set.Icc a b))
    (hswap : ∀ {z x : ℝ}, 0 < z → 0 < x →
      MeasureTheory.Integrable (Function.uncurry (fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|))
          ((MeasureTheory.volume.restrict (Set.uIoc z x)).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
        (∫ θ in Work.Spaces.Iθ, (∫ τ in Set.uIoc z x, |Work.Spaces.pzIter 2 F τ θ|))
          = ∫ τ in Set.uIoc z x,
              (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|))
    {a z₀ x : ℝ} (ha : 0 < a) (haz : a ≤ z₀) (hax : a ≤ x) (hxb : x ≤ 2 * z₀)
    (hz₀ : 0 < z₀) (hx : 0 < x) (hne : x ≠ z₀) :
    |slope (numW m F) z₀ x - pwF m F z₀|
      ≤ Cφ * (2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ := by
  have hHsq_nn : ∀ τ : ℝ, 0 ≤ Hsq α F τ := fun τ =>
    MeasureTheory.integral_nonneg fun θ => Real.sqrt_nonneg _
  -- integrability of the |·|-slice of the second-order remainder
  have hXint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ|)
      Work.Spaces.Iθ := by
    have hY : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        |F x θ| + |F z₀ θ| + |x - z₀| * |Work.Spaces.pz F z₀ θ|) Work.Spaces.Iθ :=
      ((habs x hx).1.add (habs z₀ hz₀).1).add ((habs z₀ hz₀).2.const_mul |x - z₀|)
    refine MeasureTheory.Integrable.mono' hY ?_ ?_
    · exact (((hsm.aesm_slice_pzIter 0 hx).sub (hsm.aesm_slice_pzIter 0 hz₀)).sub
        ((hsm.aesm_slice_pzIter 1 hz₀).const_mul (x - z₀))).norm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      calc |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ|
          ≤ |F x θ - F z₀ θ| + |(x - z₀) * Work.Spaces.pz F z₀ θ| := abs_sub _ _
        _ ≤ |F x θ| + |F z₀ θ| + |x - z₀| * |Work.Spaces.pz F z₀ θ| := by
            rw [abs_mul]
            have := abs_sub (F x θ) (F z₀ θ)
            linarith
  -- Step 1: linearity, the remainder as a `θ`-integral
  have hlin : numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀
      = ∫ θ in Work.Spaces.Iθ,
          (F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ) * phiW m θ := by
    have hx1 := (hphi x hx).1
    have hz1 := (hphi z₀ hz₀).1
    have hz2 := (hphi z₀ hz₀).2
    have hB : MeasureTheory.Integrable
        (fun θ : ℝ => (x - z₀) * (Work.Spaces.pz F z₀ θ * phiW m θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hz2.const_mul _
    have hA : MeasureTheory.Integrable
        (fun θ : ℝ => F x θ * phiW m θ - F z₀ θ * phiW m θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hx1.sub hz1
    have e1 : (∫ θ in Work.Spaces.Iθ, F x θ * phiW m θ)
          - (∫ θ in Work.Spaces.Iθ, F z₀ θ * phiW m θ)
        = ∫ θ in Work.Spaces.Iθ, F x θ * phiW m θ - F z₀ θ * phiW m θ :=
      (MeasureTheory.integral_sub hx1 hz1).symm
    have e2 : (x - z₀) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z₀ θ * phiW m θ)
        = ∫ θ in Work.Spaces.Iθ, (x - z₀) * (Work.Spaces.pz F z₀ θ * phiW m θ) :=
      (MeasureTheory.integral_const_mul (x - z₀)
        (fun θ : ℝ => Work.Spaces.pz F z₀ θ * phiW m θ)).symm
    have e3 : (∫ θ in Work.Spaces.Iθ, F x θ * phiW m θ - F z₀ θ * phiW m θ)
          - (∫ θ in Work.Spaces.Iθ, (x - z₀) * (Work.Spaces.pz F z₀ θ * phiW m θ))
        = ∫ θ in Work.Spaces.Iθ,
            (F x θ * phiW m θ - F z₀ θ * phiW m θ)
              - (x - z₀) * (Work.Spaces.pz F z₀ θ * phiW m θ) :=
      (MeasureTheory.integral_sub hA hB).symm
    rw [numW, numW, pwF, e1, e2, e3]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  -- Step 2: pull out the absolute value
  have hstep2 : |numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀|
      ≤ ∫ θ in Work.Spaces.Iθ,
          |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| * |phiW m θ| := by
    rw [hlin]
    refine le_trans MeasureTheory.abs_integral_le_integral_abs (le_of_eq ?_)
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [abs_mul])
  -- Step 3: insert the bound `Cφ` on the angular weight
  have hstep3 : (∫ θ in Work.Spaces.Iθ,
          |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| * |phiW m θ|)
      ≤ Cφ * ∫ θ in Work.Spaces.Iθ,
          |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| := by
    rw [← MeasureTheory.integral_const_mul Cφ
      (fun θ : ℝ => |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ|)]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (hXint.const_mul Cφ) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    calc |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| * |phiW m θ|
        ≤ |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| * Cφ :=
          mul_le_mul_of_nonneg_left (hCφ θ hθ) (abs_nonneg _)
      _ = Cφ * |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| := by ring
  -- Step 4: the second-order FTC bound, a.e. in `θ`
  have hstep4 : (∫ θ in Work.Spaces.Iθ,
          |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (|x - z₀| * ∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) ?_ ?_
    · exact ((hswap hz₀ hx).1.integral_prod_right).const_mul |x - z₀|
    · rw [Work.Spaces.Iθ, MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2)).symm]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => ftc2_bound hsm hz₀ hx hθ)
  -- Step 5: pull out the constant `|x - z₀|`
  have hstep5 : (∫ θ in Work.Spaces.Iθ,
          (|x - z₀| * ∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|))
      = |x - z₀| * ∫ θ in Work.Spaces.Iθ,
          (∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|) :=
    MeasureTheory.integral_const_mul _ _
  -- Step 6: Tonelli
  have hstep6 : (∫ θ in Work.Spaces.Iθ,
          (∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|))
      = ∫ τ in Set.uIoc z₀ x,
          (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|) := (hswap hz₀ hx).2
  -- Step 7: the slice bound for `∂_z²F`
  have hstep7 : (∫ τ in Set.uIoc z₀ x,
          (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|))
      ≤ (2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ := by
    rw [← MeasureTheory.integral_const_mul (2 / a ^ 2) (Hsq α F)]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun τ => MeasureTheory.integral_nonneg
        fun θ => abs_nonneg _) ?_ ?_
    · have h1 : MeasureTheory.IntegrableOn (Hsq α F) (Set.Icc a (2 * z₀)) :=
        hout a (2 * z₀) ha
      refine (h1.mono_set ?_).const_mul _
      intro τ hτ
      rcases Set.mem_uIoc.mp hτ with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨le_trans (le_min haz hax) (le_trans (min_le_left z₀ x) h1'.le),
          le_trans h2' hxb⟩
      · exact ⟨le_trans hax h1'.le, le_trans h2' (by linarith)⟩
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun τ hτ => ?_)
      have hτmin : min z₀ x < τ := hτ.1
      have hτa : a ≤ τ := le_trans (le_min haz hax) hτmin.le
      have hτpos : 0 < τ := lt_of_lt_of_le ha hτa
      have hinner : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|)
          ≤ (2 / τ ^ 2) * Hsq α F τ := by
        rw [Hsq, ← MeasureTheory.integral_const_mul (2 / τ ^ 2)
          (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))]
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => abs_nonneg _)
          ((hsl τ hτpos.le).const_mul _) ?_
        rw [Work.Spaces.Iθ, MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
            (b := Real.pi / 2)).symm]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => hpt2 τ θ hτpos hθ)
      have hmono : (2 / τ ^ 2) ≤ (2 / a ^ 2) := by
        have h2 : a ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ ha.le hτa 2
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
      calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|)
          ≤ (2 / τ ^ 2) * Hsq α F τ := hinner
        _ ≤ (2 / a ^ 2) * Hsq α F τ := mul_le_mul_of_nonneg_right hmono (hHsq_nn τ)
  -- assembly
  have hbound : |numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀|
      ≤ Cφ * |x - z₀| * ((2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ) := by
    calc |numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀|
        ≤ ∫ θ in Work.Spaces.Iθ,
            |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| * |phiW m θ| := hstep2
      _ ≤ Cφ * ∫ θ in Work.Spaces.Iθ,
            |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ| := hstep3
      _ ≤ Cφ * ∫ θ in Work.Spaces.Iθ,
            (|x - z₀| * ∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|) :=
          mul_le_mul_of_nonneg_left hstep4 hCφnn
      _ = Cφ * (|x - z₀| * ∫ θ in Work.Spaces.Iθ,
            (∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|)) := by rw [hstep5]
      _ = Cφ * |x - z₀| * (∫ τ in Set.uIoc z₀ x,
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|)) := by
          rw [hstep6]; ring
      _ ≤ Cφ * |x - z₀| * ((2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ) :=
          mul_le_mul_of_nonneg_left hstep7 (mul_nonneg hCφnn (abs_nonneg _))
  have hslope : |slope (numW m F) z₀ x - pwF m F z₀|
      = |x - z₀|⁻¹ * |numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀| := by
    rw [slope_fun_def]
    simp only [vsub_eq_sub, smul_eq_mul]
    have hx0 : x - z₀ ≠ 0 := sub_ne_zero.mpr hne
    have hcancel : (x - z₀)⁻¹ * ((x - z₀) * pwF m F z₀) = pwF m F z₀ := by
      rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    rw [show (x - z₀)⁻¹ * (numW m F x - numW m F z₀) - pwF m F z₀
        = (x - z₀)⁻¹ * (numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀) from by
      calc (x - z₀)⁻¹ * (numW m F x - numW m F z₀) - pwF m F z₀
          = (x - z₀)⁻¹ * (numW m F x - numW m F z₀)
              - (x - z₀)⁻¹ * ((x - z₀) * pwF m F z₀) := by rw [hcancel]
        _ = (x - z₀)⁻¹ * (numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀) := by ring,
      abs_mul, abs_inv]
  calc |slope (numW m F) z₀ x - pwF m F z₀|
      = |x - z₀|⁻¹ * |numW m F x - numW m F z₀ - (x - z₀) * pwF m F z₀| := hslope
    _ ≤ |x - z₀|⁻¹ * (Cφ * |x - z₀| * ((2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (abs_nonneg _))
    _ = Cφ * (2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ := by
        have hZ0 : |x - z₀| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
        rw [show Cφ * |x - z₀| * ((2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ)
            = |x - z₀| * (Cφ * ((2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ)) from by
          ring,
          ← mul_assoc, inv_mul_cancel₀ hZ0, one_mul]
        ring

/-- `∫_t∈uIoc z x f = |∫_{z}^{x} f|` for a nonnegative `f`. -/
theorem setIntegral_uIoc_eq_abs {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) (z x : ℝ) :
    (∫ t in Set.uIoc z x, f t) = |∫ t in z..x, f t| := by
  rcases le_total z x with h | h
  · rw [Set.uIoc_of_le h, ← intervalIntegral.integral_of_le h,
      abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall h hf)]
  · rw [Set.uIoc_of_ge h, ← intervalIntegral.integral_of_le h]
    rw [show (∫ t in z..x, f t) = -∫ t in x..z, f t from
        intervalIntegral.integral_symm x z,
      abs_neg, abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall h hf)]

end Work.FTS.ClassCHon.Zpz
