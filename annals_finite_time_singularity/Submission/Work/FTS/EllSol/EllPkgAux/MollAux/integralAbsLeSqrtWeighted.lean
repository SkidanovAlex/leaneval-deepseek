import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollAux

open MeasureTheory

/-- `sin (2θ)` is nonnegative on `[0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- For a nonnegative base `sin (2s)`, the inverse of the weight `sin (2s)^{-99/100}` is the
weight `sin (2s)^{99/100}` of the opposite exponent. -/
private lemma inv_sin_two_rpow_neg_eq {s : ℝ} (hs : 0 ≤ Real.sin (2 * s)) :
    (((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) = (Real.sin (2 * s)) ^ (99 / 100 : ℝ) := by
  rw [Real.rpow_neg hs (99 / 100 : ℝ), inv_inv]

/-- On `[0, π/2]` the reciprocal weight `sin (2θ)^{99/100}` is bounded by `1`. -/
private lemma sigma_inv_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ((Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))⁻¹ ≤ 1 := by
  rw [inv_sin_two_rpow_neg_eq (sin_two_nonneg_of_mem_Icc hx)]
  exact Real.rpow_le_one (sin_two_nonneg_of_mem_Icc hx) (Real.sin_le_one _) (by norm_num)

/-- `θ ↦ sin (2θ)^p` is integrable on `[0, π/2]` for every `p ≥ 0` (it is bounded by `1`
there and the interval has finite measure). -/
private lemma integrableOn_sin_two_rpow_of_nonneg (p : ℝ) (hp : 0 ≤ p) :
    MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sin (2 * s)) ^ p) (Set.Icc 0 (Real.pi / 2)) := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Set.Icc (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ)) ?_) ?_ ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hθ) p)]
    exact Real.rpow_le_one (sin_two_nonneg_of_mem_Icc hθ) (Real.sin_le_one _) hp

/-- Weighted Cauchy–Schwarz (Bunyakovsky) in the form needed for the `L¹`–`L²` interpolation:
if `∫_{[0,π/2]} h² sin(2θ)^{-99/100}` is finite, then
`∫_{[0,π/2]} |h| ≤ √(π/2) · √(∫_{[0,π/2]} h² sin(2θ)^{-99/100})`.

The proof writes `|h| = √(h²σ)·√(σ⁻¹)` with `σ = sin(2θ)^{-99/100}`, applies the
Cauchy–Schwarz inequality `interval_integral_sq_le_mul`, and uses that on `[0, π/2]` the
reciprocal weight `σ⁻¹ = sin(2θ)^{99/100}` is bounded by `1`, so its integral is at most
`π/2`.  No measurability of `h` is needed: only `h²σ` appears, and the two factors are
exhibited as genuine `L²` functions. -/
theorem integralAbsLeSqrtWeighted {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in Set.Icc 0 (Real.pi / 2), |h θ|) ≤ Real.sqrt (Real.pi / 2) *
      Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
        h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- Move everything to interval integrals over `0..π/2`.
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  have hσ : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    intro s hs
    exact Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])) _
  have hf : MeasureTheory.IntegrableOn
      (fun s : ℝ => |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioc 0 (Real.pi / 2)) := by
    have h := hint.mono_set Set.Ioc_subset_Icc_self
    simpa only [sq_abs] using h
  have hσi : MeasureTheory.IntegrableOn
      (fun s : ℝ => ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) (Set.Ioc 0 (Real.pi / 2)) := by
    have hb := (integrableOn_sin_two_rpow_of_nonneg (99 / 100) (by norm_num)).mono_set
      Set.Ioc_subset_Icc_self
    exact hb.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => (inv_sin_two_rpow_neg_eq (sin_two_nonneg_of_mem_Icc
        ⟨le_of_lt hs.1, hs.2⟩)).symm))
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul hab hσ hf hσi
  -- `|h|² = h²`.
  have hA1 : (∫ s in (0 : ℝ)..(Real.pi / 2),
        |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))
      = ∫ s in (0 : ℝ)..(Real.pi / 2), h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [sq_abs]
  -- The reciprocal weight contributes at most `π/2`.
  have hB' : (∫ s in (0 : ℝ)..(Real.pi / 2),
        ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) ≤ Real.pi / 2 := by
    have hint' : IntervalIntegrable
        (fun s : ℝ => ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) volume 0 (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hσi
    have hcone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (MeasureTheory.integrableOn_const (s := Set.Ioc (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
          (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
    have h := intervalIntegral.integral_mono_on hab hint' hcone (fun x hx => sigma_inv_le_one hx)
    simpa [intervalIntegral.integral_const, sub_zero] using h
  have hA1_nonneg : 0 ≤ ∫ s in (0 : ℝ)..(Real.pi / 2),
      |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hu) _)
  have hA_nonneg : 0 ≤ ∫ s in (0 : ℝ)..(Real.pi / 2),
      h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hu) _)
  have hkey : (∫ s in (0 : ℝ)..(Real.pi / 2), |h s|) ^ 2 ≤
      (∫ s in (0 : ℝ)..(Real.pi / 2), h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) *
        (Real.pi / 2) := by
    calc (∫ s in (0 : ℝ)..(Real.pi / 2), |h s|) ^ 2
        ≤ (∫ s in (0 : ℝ)..(Real.pi / 2),
              |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) *
            (∫ s in (0 : ℝ)..(Real.pi / 2), ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) := hcs
      _ ≤ (∫ s in (0 : ℝ)..(Real.pi / 2),
              |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) * (Real.pi / 2) :=
            mul_le_mul_of_nonneg_left hB' hA1_nonneg
      _ = (∫ s in (0 : ℝ)..(Real.pi / 2),
              h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) * (Real.pi / 2) := by
            rw [hA1]
  have h1 := Real.le_sqrt_of_sq_le hkey
  rw [Real.sqrt_mul hA_nonneg] at h1
  simpa [mul_comm] using h1

end Work.FTS.EllSol.EllPkgAux.MollAux
