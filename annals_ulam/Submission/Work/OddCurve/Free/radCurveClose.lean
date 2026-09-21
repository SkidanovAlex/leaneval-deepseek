import Mathlib
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddEnvelope.Close.profileX_deriv_formulas

/-!
# The radial chord function of a nearly circular profile is close to the semicircle's

Let `ρ : ℝ → ℝ` be the radial function of a body of revolution, written in the *polar angle*
parametrisation: the point of the boundary at polar angle `θ` is at distance `ρ θ`.  Its chord
endpoint function, parametrised by the slope `σ = tan θ` of the chord direction, is

`x σ = ρ (arctan σ) * cos (arctan σ)`,

whose `σ`-derivatives carry the factor `dθ/dσ = 1/(1+σ²) = cos(arctan σ)²`.  The semicircle
(`ρ ≡ 1`) has `profileX σ = cos (arctan σ) = 1/√(1+σ²)`.

This file proves `radCurveClose`: if `|ρ - 1| ≤ ε`, `|ρ'| ≤ ε`, `|ρ''| ≤ ε` on `[0, π/2]` and
`8 ε ≤ 1/100`, then `x` is `1/100`-close to `profileX` in `C²` on the positive half-line, and `x`
is strictly decreasing on the slope window `[1/2, 4/5]`.

The two derivative formulas (writing `c = cos (arctan σ)`, `s = sin (arctan σ)`, `A = ρ (arctan σ)`,
`B = ρ' (arctan σ)`, `C = ρ'' (arctan σ)`) are

* `x' - profileX' = c² * (B * c - (A - 1) * s)`,
* `x'' - profileX'' = -4 * c⁴ * s * B + c⁵ * C + (2 * c³ * s² - c⁵) * (A - 1)`,

so `|x - profileX| ≤ ε`, `|x' - profileX'| ≤ 2ε`, `|x'' - profileX''| ≤ 4ε + ε + 3ε = 8ε`, which is
where the hypothesis `8 ε ≤ 1/100` comes from.
-/

namespace Work.OddCurve.Free

open Filter Topology Set
open scoped ContDiff

noncomputable section

/-! ## Elementary trigonometric identities -/

lemma inv_one_add_sq_eq_cos_sq (σ : ℝ) : (1 + σ ^ 2)⁻¹ = Real.cos (Real.arctan σ) ^ 2 := by
  rw [Real.cos_sq_arctan, inv_eq_one_div]

/-- `σ * cos (arctan σ) = sin (arctan σ)`. -/
lemma mul_cos_arctan_eq_sin_arctan (σ : ℝ) :
    σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) := by
  rw [Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1 + σ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

lemma arctan_mem_Icc_of_pos {σ : ℝ} (hσ : 0 < σ) :
    Real.arctan σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨(Real.arctan_pos.mpr hσ).le, (Real.arctan_lt_pi_div_two σ).le⟩

lemma arctan_Icc_mem_nhds_of_pos {σ : ℝ} (hσ : 0 < σ) :
    Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan σ) :=
  mem_of_superset (isOpen_Ioo.mem_nhds
      ⟨Real.arctan_pos.mpr hσ, Real.arctan_lt_pi_div_two σ⟩)
    (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)

/-- `1/4 ≤ sin (arctan σ)` for `σ ∈ [1/2, 4/5]`: this is the quantitative content of the fact that
the window `[1/2, 4/5]` stays away from the origin. -/
lemma sin_arctan_ge_quarter {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 4 / 5) :
    1 / 4 ≤ Real.sin (Real.arctan σ) := by
  have hσ : (0 : ℝ) < σ := by linarith
  have hden : 1 + σ ^ 2 ≤ 4 := by nlinarith
  have hcsq : Real.cos (Real.arctan σ) ^ 2 = 1 / (1 + σ ^ 2) := Real.cos_sq_arctan σ
  have hc2 : (1 / 2 : ℝ) ^ 2 ≤ Real.cos (Real.arctan σ) ^ 2 := by
    rw [hcsq, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + σ ^ 2)]
    nlinarith
  have hcpos : 0 < Real.cos (Real.arctan σ) := Real.cos_arctan_pos σ
  have hc : (1 / 2 : ℝ) ≤ Real.cos (Real.arctan σ) := by
    have h := sq_le_sq.mp hc2
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hcpos] at h
    exact h
  have hmul : (1 / 2 : ℝ) * (1 / 2) ≤ σ * Real.cos (Real.arctan σ) :=
    mul_le_mul h1 hc (by norm_num) (by linarith)
  rw [← mul_cos_arctan_eq_sin_arctan σ]
  linarith

/-! ## The derivative formulas for the radial chord function

This is the computation of the first and second derivatives of `σ ↦ ρ (arctan σ) cos (arctan σ)`,
relative to the semicircle's `profileX`.  The pattern follows
`Work.OddCurve.LowSlope.lowSlopeCurveY_derivs_sub`, with the two-piece curve replaced by the radial
parametrisation itself. -/

/-- `x'` as a pointwise product, so that the chain and product rules apply syntactically. -/
private def F1 (ρ : ℝ → ℝ) : ℝ → ℝ :=
  (fun τ : ℝ => (1 + τ ^ 2)⁻¹) *
    ((fun τ => deriv ρ (Real.arctan τ)) * (fun τ => Real.cos (Real.arctan τ))
      - (fun τ => ρ (Real.arctan τ)) * (fun τ => Real.sin (Real.arctan τ)))

private lemma deriv_radCurve_eq_F1 {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Icc 0 (Real.pi / 2)))
    {τ : ℝ} (hτ : 0 < τ) :
    deriv (fun t : ℝ => ρ (Real.arctan t) * Real.cos (Real.arctan t)) τ = F1 ρ τ := by
  have ha : Real.arctan τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_pos.mpr hτ, Real.arctan_lt_pi_div_two τ⟩
  have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan τ) :=
    mem_of_superset (isOpen_Ioo.mem_nhds ha) (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hRc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Real.arctan τ) := hρ.contDiffAt hmem
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hRd : DifferentiableAt ℝ ρ (Real.arctan τ) := hRc.differentiableAt hne
  have harc : HasDerivAt Real.arctan ((1 + τ ^ 2)⁻¹) τ := Real.hasDerivAt_arctan' τ
  have h1 : HasDerivAt (fun t => ρ (Real.arctan t))
      (deriv ρ (Real.arctan τ) * (1 + τ ^ 2)⁻¹) τ := hRd.hasDerivAt.comp τ harc
  have h2 : HasDerivAt (fun t => Real.cos (Real.arctan t))
      (-Real.sin (Real.arctan τ) * (1 + τ ^ 2)⁻¹) τ := (Real.hasDerivAt_cos _).comp τ harc
  have h3d : deriv (fun t => ρ (Real.arctan t) * Real.cos (Real.arctan t)) τ
      = deriv ρ (Real.arctan τ) * (1 + τ ^ 2)⁻¹ * Real.cos (Real.arctan τ)
        + ρ (Real.arctan τ) * (-Real.sin (Real.arctan τ) * (1 + τ ^ 2)⁻¹) := (h1.mul h2).deriv
  rw [h3d]
  simp only [F1, Pi.mul_apply, Pi.sub_apply]
  ring

/-- **The deviations of the first two derivatives of the radial chord function from those of the
semicircle's.**  Writing `c = cos (arctan σ)`, `s = sin (arctan σ)`, `A = ρ (arctan σ)`,
`B = deriv ρ (arctan σ)`, `C = deriv (deriv ρ) (arctan σ)`:

* `x' - profileX' = c² * (B * c - (A - 1) * s)`,
* `x'' - profileX'' = -4 c⁴ s B + c⁵ C + (2 c³ s² - c⁵)(A - 1)`.

Only `0 < σ` is needed: then `arctan σ ∈ (0, π/2)` is an interior point of `Icc 0 (π/2)`, so `ρ`
and `ρ'` are differentiable there. -/
theorem radCurve_derivs_sub (ρ : ℝ → ℝ)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Icc 0 (Real.pi / 2))) {σ : ℝ}
    (hσ : 0 < σ) :
    deriv (fun τ : ℝ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ -
        deriv Work.OddEnvelope.profileX σ =
      Real.cos (Real.arctan σ) ^ 2 *
        (deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ) -
          (ρ (Real.arctan σ) - 1) * Real.sin (Real.arctan σ)) ∧
    deriv (deriv (fun τ : ℝ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ))) σ -
        deriv (deriv Work.OddEnvelope.profileX) σ =
      (-4 : ℝ) * Real.cos (Real.arctan σ) ^ 4 * Real.sin (Real.arctan σ)
          * deriv ρ (Real.arctan σ) +
        Real.cos (Real.arctan σ) ^ 5 * deriv (deriv ρ) (Real.arctan σ) +
        (2 * Real.cos (Real.arctan σ) ^ 3 * Real.sin (Real.arctan σ) ^ 2 -
          Real.cos (Real.arctan σ) ^ 5) * (ρ (Real.arctan σ) - 1) := by
  have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan σ) :=
    arctan_Icc_mem_nhds_of_pos hσ
  have hRc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Real.arctan σ) := hρ.contDiffAt hmem
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hRd : DifferentiableAt ℝ ρ (Real.arctan σ) := hRc.differentiableAt hne
  have hR2d : DifferentiableAt ℝ (deriv ρ) (Real.arctan σ) :=
    (hRc.derivWithin (by simp)).differentiableAt hne
  have hKval : (1 + σ ^ 2)⁻¹ = Real.cos (Real.arctan σ) ^ 2 := inv_one_add_sq_eq_cos_sq σ
  have hσc : σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) :=
    mul_cos_arctan_eq_sin_arctan σ
  -- the derivative of the radial chord function, explicitly
  have hDg : deriv (fun τ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ
      = deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ) ^ 3
        - ρ (Real.arctan σ) * Real.sin (Real.arctan σ) * Real.cos (Real.arctan σ) ^ 2 := by
    have harc : HasDerivAt Real.arctan ((1 + σ ^ 2)⁻¹) σ := Real.hasDerivAt_arctan' σ
    have h1 : HasDerivAt (fun τ => ρ (Real.arctan τ))
        (deriv ρ (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := hRd.hasDerivAt.comp σ harc
    have h2 : HasDerivAt (fun τ => Real.cos (Real.arctan τ))
        (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_cos _).comp σ harc
    have h3d : deriv (fun τ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ
        = deriv ρ (Real.arctan σ) * (1 + σ ^ 2)⁻¹ * Real.cos (Real.arctan σ)
          + ρ (Real.arctan σ) * (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) :=
      (h1.mul h2).deriv
    rw [h3d, hKval]; ring
  -- the semicircle's derivative formulas, in trigonometric form
  have hP1 : deriv Work.OddEnvelope.profileX σ = -σ * Real.cos (Real.arctan σ) ^ 3 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).1,
      Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
  have hP2 : deriv (deriv Work.OddEnvelope.profileX) σ
      = (2 * σ ^ 2 - 1) * Real.cos (Real.arctan σ) ^ 5 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).2.1,
      Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
  -- on a neighbourhood of `σ` the derivative is `F1 ρ`
  have hFF : deriv (fun τ : ℝ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) =ᶠ[𝓝 σ] F1 ρ := by
    filter_upwards [isOpen_Ioi.mem_nhds hσ] with τ hτ
    exact deriv_radCurve_eq_F1 hρ hτ
  have hD2 : deriv (deriv (fun τ : ℝ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ))) σ
      = deriv (F1 ρ) σ := Filter.EventuallyEq.deriv_eq hFF
  have hF1d : deriv (F1 ρ) σ =
      (-4 : ℝ) * Real.cos (Real.arctan σ) ^ 4 * Real.sin (Real.arctan σ)
          * deriv ρ (Real.arctan σ)
        + Real.cos (Real.arctan σ) ^ 5 * deriv (deriv ρ) (Real.arctan σ)
        + (2 * Real.cos (Real.arctan σ) ^ 3 * Real.sin (Real.arctan σ) ^ 2
            - Real.cos (Real.arctan σ) ^ 5) * (ρ (Real.arctan σ) - 1)
        + (2 * σ ^ 2 - 1) * Real.cos (Real.arctan σ) ^ 5 := by
    have harc : HasDerivAt Real.arctan ((1 + σ ^ 2)⁻¹) σ := Real.hasDerivAt_arctan' σ
    have hg : HasDerivAt (fun τ : ℝ => 1 + τ ^ 2) (2 * σ) σ := by
      simpa using ((hasDerivAt_id σ).pow 2).const_add 1
    have hK : HasDerivAt (fun τ : ℝ => (1 + τ ^ 2)⁻¹) (-2 * σ * ((1 + σ ^ 2)⁻¹) ^ 2) σ := by
      have hinv : HasDerivAt (fun τ : ℝ => (1 + τ ^ 2)⁻¹) (-(2 * σ) / (1 + σ ^ 2) ^ 2) σ :=
        hg.inv (by positivity)
      rw [show (-2 * σ * ((1 + σ ^ 2)⁻¹) ^ 2) = (-(2 * σ) / (1 + σ ^ 2) ^ 2) from by
        rw [div_eq_mul_inv, inv_pow]; ring]
      exact hinv
    have hA : HasDerivAt (fun τ => ρ (Real.arctan τ))
        (deriv ρ (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := hRd.hasDerivAt.comp σ harc
    have hB : HasDerivAt (fun τ => deriv ρ (Real.arctan τ))
        (deriv (deriv ρ) (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ :=
      hR2d.hasDerivAt.comp σ harc
    have hC : HasDerivAt (fun τ => Real.cos (Real.arctan τ))
        (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_cos _).comp σ harc
    have hS : HasDerivAt (fun τ => Real.sin (Real.arctan τ))
        (Real.cos (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_sin _).comp σ harc
    have hBC := (hB.mul hC).sub (hA.mul hS)
    have hF1 : HasDerivAt (F1 ρ) _ σ := hK.mul hBC
    rw [hF1.deriv, hKval]
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (norm := ring_nf)
      (-2 * Real.cos (Real.arctan σ) ^ 4 * deriv ρ (Real.arctan σ)
        + 2 * Real.cos (Real.arctan σ) ^ 3 * ρ (Real.arctan σ) * Real.sin (Real.arctan σ)
        - 2 * Real.cos (Real.arctan σ) ^ 3
            * (Real.sin (Real.arctan σ) + σ * Real.cos (Real.arctan σ))) * hσc
  refine ⟨?_, ?_⟩
  · rw [hDg, hP1]
    linear_combination (norm := ring_nf) (Real.cos (Real.arctan σ) ^ 2) * hσc
  · rw [hD2, hF1d, hP2]
    ring

/-! ## The main theorem -/

theorem radCurveClose (ρ : ℝ → ℝ)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Icc 0 (Real.pi / 2))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : 8 * ε ≤ 1 / 100)
    (h0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |ρ α - 1| ≤ ε)
    (h1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv ρ α| ≤ ε)
    (h2 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv ρ) α| ≤ ε) :
    Work.OddCurve.LowSlope.CloseToProfileX
        (fun σ : ℝ => ρ (Real.arctan σ) * Real.cos (Real.arctan σ)) ∧
      (∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 4 / 5 →
        deriv (fun τ : ℝ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0) := by
  have hε800 : ε ≤ 1 / 800 := by linarith
  constructor
  · unfold Work.OddCurve.LowSlope.CloseToProfileX
    intro s hs
    rw [Work.OddCurve.LowSlope.profileX_eq_cos_arctan s]
    obtain ⟨hd1, hd2⟩ := radCurve_derivs_sub ρ hρ hs
    rw [hd1, hd2]
    set A := ρ (Real.arctan s) with hAdef
    set B := deriv ρ (Real.arctan s) with hBdef
    set C := deriv (deriv ρ) (Real.arctan s) with hCdef
    set c := Real.cos (Real.arctan s) with hcdef
    set t := Real.sin (Real.arctan s) with htdef
    have hmem : Real.arctan s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := arctan_mem_Icc_of_pos hs
    have hA : |A - 1| ≤ ε := by rw [hAdef]; exact h0 _ hmem
    have hB : |B| ≤ ε := by rw [hBdef]; exact h1 _ hmem
    have hC : |C| ≤ ε := by rw [hCdef]; exact h2 _ hmem
    have hcpos : 0 < c := by rw [hcdef]; exact Real.cos_arctan_pos s
    have hc0 : 0 ≤ c := hcpos.le
    have hc1 : c ≤ 1 := by rw [hcdef]; exact Real.cos_le_one _
    have ht : |t| ≤ 1 := by rw [htdef]; exact Real.abs_sin_le_one _
    have hcsq : |c ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hc0, hc1]
    refine ⟨?_, ?_, ?_⟩
    · -- closeness of the values
      have heq : A * c - c = (A - 1) * c := by ring
      rw [heq, abs_mul]
      calc |A - 1| * |c| ≤ ε * 1 := by
            refine mul_le_mul hA ?_ (abs_nonneg c) hε0
            rw [abs_of_pos hcpos]; exact hc1
        _ ≤ 1 / 100 := by linarith
    · -- closeness of the first derivatives
      have hinner : |B * c - (A - 1) * t| ≤ 2 * ε := by
        calc |B * c - (A - 1) * t| ≤ |B * c| + |(A - 1) * t| := abs_sub _ _
          _ = |B| * |c| + |A - 1| * |t| := by rw [abs_mul, abs_mul]
          _ ≤ ε * 1 + ε * 1 := by
              refine add_le_add ?_ ?_
              · refine mul_le_mul hB ?_ (abs_nonneg c) hε0
                rw [abs_of_pos hcpos]; exact hc1
              · exact mul_le_mul hA ht (abs_nonneg t) hε0
          _ = 2 * ε := by ring
      calc |c ^ 2 * (B * c - (A - 1) * t)| = |c ^ 2| * |B * c - (A - 1) * t| := abs_mul _ _
        _ ≤ 1 * (2 * ε) := mul_le_mul hcsq hinner (abs_nonneg _) (by norm_num)
        _ ≤ 1 / 100 := by linarith
    · -- closeness of the second derivatives
      have ht' : -1 ≤ t ∧ t ≤ 1 := abs_le.mp ht
      have hc3 : c ^ 3 ≤ 1 := pow_le_one₀ hc0 hc1
      have hc5 : c ^ 5 ≤ 1 := pow_le_one₀ hc0 hc1
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht'.1, ht'.2]
      have hcoef : |2 * c ^ 3 * t ^ 2 - c ^ 5| ≤ 3 := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · nlinarith [hc0, hc5, sq_nonneg c, sq_nonneg t, pow_nonneg hc0 3]
        · nlinarith [hc3, ht2, sq_nonneg t, pow_nonneg hc0 5]
      have e1 : |(-4 : ℝ) * c ^ 4 * t * B| ≤ 4 * ε := by
        have hc4 : |c ^ 4| ≤ 1 := by
          rw [abs_of_nonneg (by positivity)]
          nlinarith [hc0, hc1]
        calc |(-4 : ℝ) * c ^ 4 * t * B| = 4 * |c ^ 4| * |t| * |B| := by
              rw [abs_mul, abs_mul, abs_mul]; norm_num
          _ ≤ 4 * 1 * 1 * ε := by
              refine mul_le_mul (mul_le_mul (mul_le_mul (le_refl (4 : ℝ)) hc4
                  (abs_nonneg _) (by norm_num)) ht (abs_nonneg t) (by norm_num)) hB
                (abs_nonneg B) (by norm_num)
          _ = 4 * ε := by ring
      have e2 : |c ^ 5 * C| ≤ ε := by
        calc |c ^ 5 * C| = |c ^ 5| * |C| := abs_mul _ _
          _ ≤ 1 * ε := by
              refine mul_le_mul ?_ hC (abs_nonneg C) (by norm_num)
              rw [abs_of_nonneg (pow_nonneg hc0 5)]; exact hc5
          _ = ε := by ring
      have e3 : |(2 * c ^ 3 * t ^ 2 - c ^ 5) * (A - 1)| ≤ 3 * ε := by
        rw [abs_mul]
        exact mul_le_mul hcoef hA (abs_nonneg (A - 1)) (by norm_num)
      have hsum :
          |(-4 : ℝ) * c ^ 4 * t * B + c ^ 5 * C + (2 * c ^ 3 * t ^ 2 - c ^ 5) * (A - 1)| ≤
            |(-4 : ℝ) * c ^ 4 * t * B| + |c ^ 5 * C|
              + |(2 * c ^ 3 * t ^ 2 - c ^ 5) * (A - 1)| := by
        have h1' := abs_add_le ((-4 : ℝ) * c ^ 4 * t * B + c ^ 5 * C)
          ((2 * c ^ 3 * t ^ 2 - c ^ 5) * (A - 1))
        have h2' := abs_add_le ((-4 : ℝ) * c ^ 4 * t * B) (c ^ 5 * C)
        linarith
      linarith [hsum, e1, e2, e3, hε1]
  · intro σ hσ1 hσ2
    have hσpos : 0 < σ := by linarith
    obtain ⟨hd1, hd2⟩ := radCurve_derivs_sub ρ hρ hσpos
    have hP1 : deriv Work.OddEnvelope.profileX σ = -σ * Real.cos (Real.arctan σ) ^ 3 := by
      rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).1,
        Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
    have hval : deriv (fun τ : ℝ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ =
        Real.cos (Real.arctan σ) ^ 2 *
          (deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ)
            - ρ (Real.arctan σ) * Real.sin (Real.arctan σ)) := by
      have hv := hd1
      rw [hP1] at hv
      have hkey : σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) :=
        mul_cos_arctan_eq_sin_arctan σ
      linear_combination (norm := ring_nf)
        hv - (Real.cos (Real.arctan σ) ^ 2) * hkey
    have hcpos := Real.cos_arctan_pos σ
    have hc2pos : 0 < Real.cos (Real.arctan σ) ^ 2 := by positivity
    have htq : 1 / 4 ≤ Real.sin (Real.arctan σ) := sin_arctan_ge_quarter hσ1 hσ2
    have hmem : Real.arctan σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := arctan_mem_Icc_of_pos hσpos
    have hA := abs_le.mp (h0 _ hmem)
    have hB := abs_le.mp (h1 _ hmem)
    have hcle : Real.cos (Real.arctan σ) ≤ 1 := Real.cos_le_one _
    have hkey : deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ)
        - ρ (Real.arctan σ) * Real.sin (Real.arctan σ) < 0 := by
      have hb : deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ) ≤ ε := by
        calc deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ) ≤ ε * 1 :=
              mul_le_mul hB.2 hcle hcpos.le hε0
          _ = ε := by ring
      have ha : (1 - ε) * (1 / 4) ≤ ρ (Real.arctan σ) * Real.sin (Real.arctan σ) := by
        refine mul_le_mul (by linarith [hA.1]) htq (by norm_num) ?_
        linarith [hA.1, hε800]
      nlinarith [hb, ha, hε800]
    rw [hval]
    exact mul_neg_of_pos_of_neg hc2pos hkey


end

end Work.OddCurve.Free
