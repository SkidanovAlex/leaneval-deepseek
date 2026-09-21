import Mathlib
import Submission.Work.OddCurve.LowSlope.CruxStatements
import Submission.Work.OddCurve.LowSlope.section_ibp
import Submission.Work.OddCurve.LowSlope.radial_identity
import Submission.Work.OddCurve.LowSlope.sphereArea_eq_ballVol

/-!
# `radon_data_eq_inertiaIntegral`: Prop. `workHARD1` in one dimension

Statement: `Work.OddCurve.LowSlope.RadonDataEqInertiaIntegral` (`LowSlope/CruxStatements.lean`).

With `c = (√(1+s²))⁻¹`, `u = cν`, `t = ρ u · u`, `R = f t² - (s t)²`:

* `R = (ρ u)² (1 - ν²)`, so `1 - ν² = R/(ρu)²` and `√(1-ν²) = √R/(ρ u)`;
* `√(1+s²) · c = 1`;
* the pointwise identity `ρ³ = f (f - t f')(ρ + u ρ')` of `Work.OddCurve.LowSlope.radial_identity`
  turns the Radon integrand into the section integrand
  `t² f (f - t f') R^{n-1}/√R` (times the Jacobian `c (ρ + u ρ')` and `√(1+s²) · c = 1`);
* the change of variables `ν ↦ t = ρ (cν) · (cν)` (a monotone `C¹` bijection onto the chord) gives
  the integral over the chord, where `Work.OddCurve.LowSlope.section_ibp` and
  `Work.OddCurve.LowSlope.sphereArea_eq_ballVol` finish.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The change of variables of Prop. `workHARD1`.**  With `c = (√(1+s²))⁻¹`, the composite map
`ν ↦ φ ν = ρ (cν)·(cν)` is a monotone `C¹` map taking `(-1,1)` onto the chord `(-(x s), y s)`, so
the integral of `ν ↦ K (φ ν) · ψ ν` (where `ψ = φ'` and `K` is the section integrand of
`Work.OddCurve.LowSlope.section_ibp`) is the integral of `K` over the chord. -/
theorem radon_change_of_variables (n : ℕ) {f ρ x y : ℝ → ℝ} {s : ℝ}
    (hs : 0 < s)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hderiv_nonneg : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
      0 ≤ ρ u + u * deriv ρ u)
    (hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s)
    (hend_x : ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s)) :
    (∫ ν in (-1 : ℝ)..1,
        (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t))
            (ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν)) *
          ((Real.sqrt (1 + s ^ 2))⁻¹ * (ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) +
            ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * deriv ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν))))
      = ∫ t in (-(x s))..(y s), t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t) := by
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
  set K : ℝ → ℝ := fun t => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
    Real.sqrt (rad0 f s t) with hK
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
  have hfun_eq : (fun ν : ℝ =>
        (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν)) *
          (c * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν))))
      = fun ν : ℝ => K (φ ν) * ψ ν := by
    funext ν
    simp only [hK, hφ, hψ]
  rw [hfun_eq]
  exact hchange



/-- Pointwise algebra core of Prop. `workHARD1`. -/
lemma pointwise_radon_core (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℝ} {s c ν ρu dρ : ℝ}
    (hsc : Real.sqrt (1 + s ^ 2) * c = 1)
    (hρu : 0 < ρu) (hRpos : 0 < rad0 f s (ρu * (c * ν))) (hν2 : 0 < 1 - ν ^ 2)
    (hR : rad0 f s (ρu * (c * ν)) = ρu ^ 2 * (1 - ν ^ 2))
    (hrad : f (ρu * (c * ν)) * (f (ρu * (c * ν)) - ρu * (c * ν) * deriv f (ρu * (c * ν))) *
        (ρu + c * ν * dρ) = ρu ^ 3) :
    (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρu ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2)
      = Real.sqrt (1 + s ^ 2) *
        ((ρu * (c * ν)) ^ 2 * f (ρu * (c * ν)) *
            (f (ρu * (c * ν)) - ρu * (c * ν) * deriv f (ρu * (c * ν))) *
            rad0 f s (ρu * (c * ν)) ^ (n - 1) / Real.sqrt (rad0 f s (ρu * (c * ν))) *
            (c * (ρu + c * ν * dρ))) := by
  set R : ℝ := rad0 f s (ρu * (c * ν)) with hRdef
  have hs1ν : Real.sqrt (1 - ν ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hν2)
  have hsR : Real.sqrt R ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hRpos)
  have hρune : ρu ≠ 0 := ne_of_gt hρu
  have hsqrtR : Real.sqrt R = ρu * Real.sqrt (1 - ν ^ 2) := by
    rw [hR, Real.sqrt_mul (sq_nonneg ρu), Real.sqrt_sq (le_of_lt hρu)]
  have hkey : (1 - ν ^ 2) ^ (n - 1) * ρu ^ (2 * n - 2) = R ^ (n - 1) := by
    have h22 : ρu ^ (2 * n - 2) = (ρu ^ 2) ^ (n - 1) := by
      rw [← pow_mul]; congr 1; omega
    rw [h22, ← mul_pow]
    congr 1
    rw [hR]; ring
  have hbracket : (1 - ν ^ 2) ^ (n - 1) * ρu ^ (2 * n + 2) * ρu = ρu ^ 5 * R ^ (n - 1) := by
    have h3 : ρu ^ (2 * n + 2) * ρu = ρu ^ (2 * n - 2) * ρu ^ 5 := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    calc (1 - ν ^ 2) ^ (n - 1) * ρu ^ (2 * n + 2) * ρu
        = (1 - ν ^ 2) ^ (n - 1) * (ρu ^ (2 * n + 2) * ρu) := by ring
      _ = (1 - ν ^ 2) ^ (n - 1) * (ρu ^ (2 * n - 2) * ρu ^ 5) := by rw [h3]
      _ = ((1 - ν ^ 2) ^ (n - 1) * ρu ^ (2 * n - 2)) * ρu ^ 5 := by ring
      _ = R ^ (n - 1) * ρu ^ 5 := by rw [hkey]
      _ = ρu ^ 5 * R ^ (n - 1) := by ring
  have keyL : (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρu ^ (2 * n + 2)) * Real.sqrt R
      = (c * ν) ^ 2 * ρu ^ 5 * R ^ (n - 1) * Real.sqrt (1 - ν ^ 2) := by
    rw [hsqrtR]
    calc (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρu ^ (2 * n + 2)) * (ρu * Real.sqrt (1 - ν ^ 2))
        = ((1 - ν ^ 2) ^ (n - 1) * ρu ^ (2 * n + 2) * ρu) *
            ((c * ν) ^ 2 * Real.sqrt (1 - ν ^ 2)) := by ring
      _ = (ρu ^ 5 * R ^ (n - 1)) * ((c * ν) ^ 2 * Real.sqrt (1 - ν ^ 2)) := by rw [hbracket]
      _ = (c * ν) ^ 2 * ρu ^ 5 * R ^ (n - 1) * Real.sqrt (1 - ν ^ 2) := by ring
  have hshape : Real.sqrt (1 + s ^ 2) *
          ((ρu * (c * ν)) ^ 2 * f (ρu * (c * ν)) *
              (f (ρu * (c * ν)) - ρu * (c * ν) * deriv f (ρu * (c * ν))) *
              R ^ (n - 1) / (ρu * Real.sqrt (1 - ν ^ 2)) * (c * (ρu + c * ν * dρ))) *
          (ρu * Real.sqrt (1 - ν ^ 2))
        = (Real.sqrt (1 + s ^ 2) * c) *
            (f (ρu * (c * ν)) * (f (ρu * (c * ν)) - ρu * (c * ν) * deriv f (ρu * (c * ν))) *
              (ρu + c * ν * dρ)) *
            ((ρu * (c * ν)) ^ 2 * R ^ (n - 1)) := by
    field_simp [hρune, hs1ν]
  have keyR : Real.sqrt (1 + s ^ 2) *
        ((ρu * (c * ν)) ^ 2 * f (ρu * (c * ν)) *
            (f (ρu * (c * ν)) - ρu * (c * ν) * deriv f (ρu * (c * ν))) *
            R ^ (n - 1) / Real.sqrt R * (c * (ρu + c * ν * dρ))) * Real.sqrt R
      = (c * ν) ^ 2 * ρu ^ 5 * R ^ (n - 1) := by
    rw [hsqrtR]
    rw [hshape]
    rw [hsc, one_mul, hrad]
    ring
  have hLval : (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρu ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2)
      = (c * ν) ^ 2 * ρu ^ 5 * R ^ (n - 1) / Real.sqrt R := by
    rw [div_eq_div_iff hs1ν hsR]
    exact keyL
  have hRval : Real.sqrt (1 + s ^ 2) *
        ((ρu * (c * ν)) ^ 2 * f (ρu * (c * ν)) *
            (f (ρu * (c * ν)) - ρu * (c * ν) * deriv f (ρu * (c * ν))) *
            R ^ (n - 1) / Real.sqrt R * (c * (ρu + c * ν * dρ)))
      = (c * ν) ^ 2 * ρu ^ 5 * R ^ (n - 1) / Real.sqrt R := by
    rw [eq_div_iff hsR]
    exact keyR
  exact hLval.trans hRval.symm

/-- **Prop. `workHARD1` in one dimension** (the inertia identity). -/
theorem radon_data_eq_inertiaIntegral : RadonDataEqInertiaIntegral := by
  intro n hn f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderiv_nonneg hend_y hend_x hφmem hxI hyI
    hfy hfx huniqy huniqx hxy hrad hintA hintB
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcpos : 0 < c := by rw [hc]; positivity
  have hfact : (1 : ℝ) < 1 + s ^ 2 := by nlinarith [hs, sq_nonneg s]
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) hfact
  have hsc : Real.sqrt (1 + s ^ 2) * c = 1 := by
    rw [hc]; exact mul_inv_cancel₀ (ne_of_gt hspos)
  have hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1, c * ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro ν hν
    constructor <;> nlinarith [hcpos, hclt, hν.1, hν.2]
  have hρd : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt ρ (deriv ρ u) u := by
    intro u hu
    exact ((hρC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) (fun v hv => hv))).hasDerivAt
  have hfd : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt f (deriv f t) t := by
    intro t ht
    exact ((hfC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun v hv => ⟨hv.1.le, hv.2.le⟩))).hasDerivAt
  have hpoint : ∀ ν ∈ Set.uIcc (-1 : ℝ) 1,
      (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2)
        = Real.sqrt (1 + s ^ 2) *
          ((fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν)) *
            (c * (ρ (c * ν) + c * ν * deriv ρ (c * ν)))) := by
    intro ν hν
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
    rcases eq_or_lt_of_le hν.2 with h1 | hlt
    · subst h1
      have hy0 : rad0 f s (y s) = 0 := by rw [rad0, hfy]; ring
      have hφ1 : ρ (c * 1) * (c * 1) = y s := by rw [mul_one]; exact hend_y
      simp only [hφ1, hy0]
      have h11 : (1 : ℝ) - 1 ^ 2 = 0 := by norm_num
      rw [h11, Real.sqrt_zero]
      simp only [div_zero, zero_mul, mul_zero]
    · rcases eq_or_lt_of_le (show -ν ≤ 1 from by linarith [hν.1]) with h2 | hgt
      · have hνm : ν = -1 := by linarith
        subst hνm
        have hx0 : rad0 f s (-(x s)) = 0 := by rw [rad0, hfx]; ring
        have hφm1 : ρ (c * (-1)) * (c * (-1)) = -(x s) := by
          have hcm : c * (-1 : ℝ) = -c := by ring
          rw [hcm]; exact hend_x
        simp only [hφm1, hx0]
        have hm11 : (1 : ℝ) - (-1) ^ 2 = 0 := by norm_num
        rw [hm11, Real.sqrt_zero]
        simp only [div_zero, zero_mul, mul_zero]
      · have hνIoo : ν ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hlt⟩
        have hu : c * ν ∈ Set.Ioo (-1 : ℝ) 1 := hmem ν hνIoo
        have hφmemν : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-(x s)) (y s) := hφmem ν hνIoo
        have hchord : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-1 : ℝ) 1 :=
          ⟨lt_trans (by linarith [hxI.1]) hφmemν.1, lt_trans hφmemν.2 hyI.2⟩
        have hRpos : 0 < rad0 f s (ρ (c * ν) * (c * ν)) := hrad _ hφmemν
        have hs1 : 0 < 1 - ν ^ 2 := by nlinarith [hνIoo.1, hνIoo.2]
        have hcc : c * c * (1 + s ^ 2) = 1 := by
          rw [hc]; field_simp; rw [Real.sq_sqrt (by positivity)]
        have huv : (c * ν) ^ 2 * (1 + s ^ 2) = ν ^ 2 := by
          calc (c * ν) ^ 2 * (1 + s ^ 2) = (c * c * (1 + s ^ 2)) * ν ^ 2 := by ring
            _ = ν ^ 2 := by rw [hcc, one_mul]
        have hRcalc : rad0 f s (ρ (c * ν) * (c * ν)) = ρ (c * ν) ^ 2 * (1 - ν ^ 2) := by
          have hrel : ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2) = f (ρ (c * ν) * (c * ν)) :=
            hρ (c * ν) hu
          rw [rad0, ← hrel]
          have hsqu : Real.sqrt (1 - (c * ν) ^ 2) ^ 2 = 1 - (c * ν) ^ 2 :=
            Real.sq_sqrt (by nlinarith [hu.1, hu.2, sq_nonneg (c * ν)])
          calc (ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2)) ^ 2 - (s * (ρ (c * ν) * (c * ν))) ^ 2
              = ρ (c * ν) ^ 2 * (1 - (c * ν) ^ 2) - s ^ 2 * (ρ (c * ν) * (c * ν)) ^ 2 := by
                rw [mul_pow, hsqu]; ring
            _ = ρ (c * ν) ^ 2 * (1 - ν ^ 2) := by
                rw [show ρ (c * ν) ^ 2 * (1 - (c * ν) ^ 2) - s ^ 2 * (ρ (c * ν) * (c * ν)) ^ 2
                    = ρ (c * ν) ^ 2 * (1 - (c * ν) ^ 2 * (1 + s ^ 2)) from by ring, huv]
        have hradinst : f (ρ (c * ν) * (c * ν)) *
            (f (ρ (c * ν) * (c * ν)) - ρ (c * ν) * (c * ν) * deriv f (ρ (c * ν) * (c * ν))) *
            (ρ (c * ν) + c * ν * deriv ρ (c * ν)) = ρ (c * ν) ^ 3 :=
          radial_identity hu (hρpos _ hu) (hρd _ hu) (hfd _ hchord) hρ
        exact pointwise_radon_core n hn hsc (hρpos _ hu) hRpos hs1 hRcalc hradinst
  have hint : (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
        ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2))
      = Real.sqrt (1 + s ^ 2) *
        (∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν)) *
          (c * (ρ (c * ν) + c * ν * deriv ρ (c * ν)))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hpoint
  have hcv := radon_change_of_variables n hs hρpos hρC1 hmono hρ hderiv_nonneg hend_y hend_x
  rw [← hc] at hcv
  have hibp := section_ibp n hn f (x s) (y s) s hs hfC1 hxI hyI hxy hfy (by rw [hfx]; ring) hrad hintA hintB
  have hne : (2 * (n : ℝ) - 1) ≠ 0 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hIf : (∫ t in (-(x s))..(y s),
        (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) t)
      = ((2 * (n : ℝ) + 2) * inertiaIntegral n f x y s) / (2 * (n : ℝ) - 1) := by
    rw [eq_div_iff hne]
    calc (∫ t in (-(x s))..(y s), (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
          rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) t) * (2 * (n : ℝ) - 1)
        = (2 * (n : ℝ) - 1) * (∫ t in (-(x s))..(y s), (fun t : ℝ => t ^ 2 * f t *
            (f t - t * deriv f t) * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) t) := by ring
      _ = (2 * (n : ℝ) + 2) * inertiaIntegral n f x y s := by
        simpa only [inertiaIntegral] using hibp
  have hsph : Work.OddRadon.sphereArea (2 * n - 2) = (2 * (n : ℝ) - 1) * ballVol (2 * n - 1) := by
    rw [sphereArea_eq_ballVol (2 * n - 2)]
    have h2 : 2 ≤ 2 * n := by omega
    have hcast : (((2 * n - 2 : ℕ)) : ℝ) + 1 = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub h2]; push_cast; ring
    have h3 : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    rw [hcast, h3]
  rw [hint, hcv, hIf, hsph]
  field_simp


end

end Work.OddCurve.LowSlope
