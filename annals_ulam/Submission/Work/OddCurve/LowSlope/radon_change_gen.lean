import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs

/-!
# The general change of variables of Prop. `workHARD1`

The substitution `ν ↦ φ ν = ρ (cν)·(cν)` (with `c = (√(1+s²))⁻¹`), which is a monotone `C¹`
bijection of `(-1,1)` onto the chord `(-(x s), y s)` with derivative
`ψ ν = c (ρ(cν) + cν ρ'(cν)) ≥ 0`, transported to an arbitrary integrand `K`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The general change of variables.** -/
theorem radon_change_of_variables_gen (K : ℝ → ℝ) {ρ x y : ℝ → ℝ} {s : ℝ}
    (hs : 0 < s)
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hderiv_nonneg : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
      0 ≤ ρ u + u * deriv ρ u)
    (hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s)
    (hend_x : ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s)) :
    (∫ ν in (-1 : ℝ)..1,
        K (ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν)) *
          ((Real.sqrt (1 + s ^ 2))⁻¹ * (ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) +
            ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * deriv ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν))))
      = ∫ t in (-(x s))..(y s), K t := by
  -- the constant `c` and its basic properties
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcc : c * c * (1 + s ^ 2) = 1 := by
    rw [hc]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  have hsc : Real.sqrt (1 + s ^ 2) * c = 1 := by
    rw [hc]; exact mul_inv_cancel₀ (ne_of_gt hspos)
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    have h1 : (1 : ℝ) < 1 + s ^ 2 := by nlinarith [hs, sq_nonneg s]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
  -- the composite substitution and its derivative
  set φ : ℝ → ℝ := fun ν => ρ (c * ν) * (c * ν) with hφ
  set ψ : ℝ → ℝ := fun ν => c * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) with hψ
  -- membership of `cν` in `(-1,1)`
  have hmem : ∀ ν ∈ Set.uIcc (-1 : ℝ) 1, c * ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro ν hν
    have h1 : -(1 : ℝ) ≤ ν := by
      have := hν; rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this; exact this.1
    have h2 : ν ≤ 1 := by
      have := hν; rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this; exact this.2
    constructor
    · nlinarith [hcpos, hclt]
    · nlinarith [hcpos, hclt]
  -- the two endpoint values
  have hφ1 : φ 1 = y s := by
    simp only [hφ]
    rw [mul_one]
    exact hend_y
  have hφm1 : φ (-1) = -(x s) := by
    simp only [hφ]
    have h : c * (-1) = -(c) := by ring
    rw [h]
    exact hend_x
  -- the change of variables
  have hρd : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt ρ (deriv ρ u) u := by
    intro u hu
    exact ((hρC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) (fun v hv => hv))).hasDerivAt
  have hfunct : ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1) := hρC1.continuousOn
  have hφd : ∀ ν ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt φ (ψ ν) ν := by
    intro ν hν
    have hu := hmem ν hν
    have hinner : HasDerivAt (fun x : ℝ => c * x) c ν := by
      have h := (hasDerivAt_id ν).const_mul c
      simpa using h
    have h1 : HasDerivAt (fun x : ℝ => ρ (c * x)) (deriv ρ (c * ν) * c) ν := by
      have h := HasDerivAt.comp ν (hρd (c * ν) hu) hinner
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with x
      simp [Function.comp]
    have h2 : HasDerivAt (fun x : ℝ => c * x) c ν := hinner
    have h3 := h1.mul h2
    have hfun : φ = fun x : ℝ => ρ (c * x) * (c * x) := by
      funext x; simp only [hφ]
    rw [hfun]
    refine h3.congr_deriv ?_
    simp only [hψ]
    ring
  have hφcont : ContinuousOn φ (Set.uIcc (-1 : ℝ) 1) := by
    have h1 : ContinuousOn (fun x : ℝ => ρ (c * x)) (Set.uIcc (-1 : ℝ) 1) :=
      hfunct.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun x hx => hmem x hx)
    have hfun : φ = fun x : ℝ => ρ (c * x) * (c * x) := by
      funext x; simp only [hφ]
    rw [hfun]
    exact h1.mul ((continuous_const.mul continuous_id).continuousOn)
  have hminmax : ∀ ν ∈ Set.Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1), ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro ν hν
    rwa [show min (-1 : ℝ) 1 = -1 from min_eq_left (by norm_num),
      show max (-1 : ℝ) 1 = 1 from max_eq_right (by norm_num)] at hν
  have hIoo_sub : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1, ν ∈ Set.uIcc (-1 : ℝ) 1 := by
    intro ν hν
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨hν.1.le, hν.2.le⟩
  have hψnonneg : ∀ ν ∈ Set.Ioo (min (-1:ℝ) 1) (max (-1:ℝ) 1), 0 ≤ ψ ν := by
    intro ν hν
    have hν' : ν ∈ Set.Ioo (-1 : ℝ) 1 := by
      rw [show min (-1 : ℝ) 1 = -1 from min_eq_left (by norm_num),
        show max (-1 : ℝ) 1 = 1 from max_eq_right (by norm_num)] at hν
      exact hν
    have hu : c * ν ∈ Set.Ioo (-c) c := by
      have h1 : -(c) < c * ν := by nlinarith [hcpos, hν'.1]
      have h2 : c * ν < c := by nlinarith [hcpos, hν'.2]
      exact ⟨by simpa using h1, h2⟩
    simp only [hψ]
    exact mul_nonneg (le_of_lt hcpos) (hderiv_nonneg (c * ν) hu)
  have hchange : (∫ ν in (-1 : ℝ)..1, K (φ ν) * ψ ν) = ∫ t in (-(x s))..(y s), K t := by
    rw [show (fun ν : ℝ => K (φ ν) * ψ ν) = fun ν : ℝ => (K ∘ φ) ν * ψ ν from by
      funext ν; rfl]
    rw [intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hφcont
      (fun ν hν => hφd ν (hIoo_sub ν (hminmax ν hν))) hψnonneg]
    rw [hφ1, hφm1]
  exact hchange

end

end Work.OddCurve.LowSlope
