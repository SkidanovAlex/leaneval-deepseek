import Mathlib
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddEnvelope.Close.profileX_deriv_formulas
import Submission.Work.OddEnvelope.Defs

/-!
# The first and second derivatives of the radial free chord curve, minus the semicircle's

`ρ ↦ (fun τ => ρ (arctan τ) * cos (arctan τ))` is the radial parametrisation of the chord-endpoint
curve of the free odd-dimensional construction.  Here we compute the deviation of its first and
second derivatives from those of the semicircle's chord function `profileX σ = cos (arctan σ)`
(the free version of the §4 formulas).  Writing `c = cos (arctan σ)`, `s = sin (arctan σ)`,
`A = ρ (arctan σ)`, `B = deriv ρ (arctan σ)`, `C = deriv (deriv ρ) (arctan σ)`, they read

* `deriv (fun τ => ρ (arctan τ) * cos (arctan τ)) σ - deriv profileX σ = c^2 * (B * c - (A - 1) * s)`,
* `deriv (deriv (fun τ => ρ (arctan τ) * cos (arctan τ))) σ - deriv (deriv profileX) σ
     = -4 * c^4 * s * B + c^5 * C + (2 * c^3 * s^2 - c^5) * (A - 1)`.

The only input on `ρ` is `C^∞`-smoothness on the closed interval `[0, π/2]`, which suffices because
`arctan σ ∈ (0, π/2)` is an interior point.  The elementary identity used throughout is
`σ * cos (arctan σ) = sin (arctan σ)`, together with `deriv arctan σ = (1 + σ^2)⁻¹ =
cos (arctan σ)^2`.
-/

namespace Work.OddCurve.Free

open Filter Topology Set
open scoped ContDiff

noncomputable section

/-- The explicit expression of `deriv (fun τ => ρ (arctan τ) * cos (arctan τ))`, written as a
pointwise product so that the chain/product-rule lemmas apply syntactically. -/
private def F1 (ρ : ℝ → ℝ) : ℝ → ℝ :=
  (fun τ : ℝ => (1 + τ ^ 2)⁻¹) *
    ((fun τ => deriv ρ (Real.arctan τ)) * (fun τ => Real.cos (Real.arctan τ))
      - (fun τ => ρ (Real.arctan τ)) * (fun τ => Real.sin (Real.arctan τ)))

/-- The derivative of the radial curve is `F1`.  Only `0 < τ` is needed: then
`arctan τ ∈ (0, π/2)` is an interior point of the interval on which `ρ` is smooth. -/
private lemma deriv_radCurve_eq_F1 {ρ : ℝ → ℝ} {τ : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Icc 0 (Real.pi / 2))) (hτ : 0 < τ) :
    deriv (fun t => ρ (Real.arctan t) * Real.cos (Real.arctan t)) τ = F1 ρ τ := by
  have ha : Real.arctan τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_pos.mpr hτ, Real.arctan_lt_pi_div_two τ⟩
  have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan τ) :=
    mem_of_superset (isOpen_Ioo.mem_nhds ha) (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hρc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Real.arctan τ) := hρ.contDiffAt hmem
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hρd : DifferentiableAt ℝ ρ (Real.arctan τ) := hρc.differentiableAt hne
  have harc : HasDerivAt Real.arctan ((1 + τ ^ 2)⁻¹) τ := Real.hasDerivAt_arctan' τ
  have h1 : HasDerivAt (fun t => ρ (Real.arctan t))
      (deriv ρ (Real.arctan τ) * (1 + τ ^ 2)⁻¹) τ := hρd.hasDerivAt.comp τ harc
  have h2 : HasDerivAt (fun t => Real.cos (Real.arctan t))
      (-Real.sin (Real.arctan τ) * (1 + τ ^ 2)⁻¹) τ := (Real.hasDerivAt_cos _).comp τ harc
  have h3d : deriv (fun t => ρ (Real.arctan t) * Real.cos (Real.arctan t)) τ
      = deriv ρ (Real.arctan τ) * (1 + τ ^ 2)⁻¹ * Real.cos (Real.arctan τ)
        + ρ (Real.arctan τ) * (-Real.sin (Real.arctan τ) * (1 + τ ^ 2)⁻¹) := (h1.mul h2).deriv
  show deriv (fun t => ρ (Real.arctan t) * Real.cos (Real.arctan t)) τ = _
  rw [h3d]
  simp only [F1, Pi.mul_apply, Pi.sub_apply]
  ring

/-- `deriv arctan σ = (1 + σ^2)⁻¹` in terms of the cosine, `(1 + σ^2)⁻¹ = cos (arctan σ)^2`. -/
private lemma inv_one_add_sq {σ : ℝ} :
    (1 + σ ^ 2)⁻¹ = Real.cos (Real.arctan σ) ^ 2 := by
  rw [Real.cos_sq_arctan]; rw [inv_eq_one_div]

/-- The elementary relation `σ * cos (arctan σ) = sin (arctan σ)`. -/
private lemma mul_cos_arctan_eq_sin_arctan {σ : ℝ} :
    σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) := by
  rw [Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1 + σ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

theorem radCurveDerivs (ρ : ℝ → ℝ)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Icc 0 (Real.pi / 2))) {σ : ℝ} (hσ : 0 < σ) :
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
  obtain ⟨ha1, ha2⟩ : Real.arctan σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_pos.mpr hσ, Real.arctan_lt_pi_div_two σ⟩
  have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan σ) :=
    mem_of_superset (isOpen_Ioo.mem_nhds ⟨ha1, ha2⟩)
      (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hρc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Real.arctan σ) := hρ.contDiffAt hmem
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hρd : DifferentiableAt ℝ ρ (Real.arctan σ) := hρc.differentiableAt hne
  have hρ2d : DifferentiableAt ℝ (deriv ρ) (Real.arctan σ) :=
    (hρc.derivWithin (by simp)).differentiableAt hne
  have hKval : (1 + σ ^ 2)⁻¹ = Real.cos (Real.arctan σ) ^ 2 := inv_one_add_sq
  have hσc : σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) :=
    mul_cos_arctan_eq_sin_arctan
  -- the derivative of the radial curve
  have hDg : deriv (fun τ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ
      = deriv ρ (Real.arctan σ) * Real.cos (Real.arctan σ) ^ 3
        - ρ (Real.arctan σ) * Real.sin (Real.arctan σ) * Real.cos (Real.arctan σ) ^ 2 := by
    have harc : HasDerivAt Real.arctan ((1 + σ ^ 2)⁻¹) σ := Real.hasDerivAt_arctan' σ
    have h1 : HasDerivAt (fun τ => ρ (Real.arctan τ))
        (deriv ρ (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := hρd.hasDerivAt.comp σ harc
    have h2 : HasDerivAt (fun τ => Real.cos (Real.arctan τ))
        (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_cos _).comp σ harc
    have h3d : deriv (fun τ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)) σ
        = deriv ρ (Real.arctan σ) * (1 + σ ^ 2)⁻¹ * Real.cos (Real.arctan σ)
          + ρ (Real.arctan σ) * (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) :=
      (h1.mul h2).deriv
    rw [h3d, hKval]; ring
  -- the semicircle's derivative formulas
  have hP1 : deriv Work.OddEnvelope.profileX σ = -σ * Real.cos (Real.arctan σ) ^ 3 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).1,
      Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
  have hP2 : deriv (deriv Work.OddEnvelope.profileX) σ
      = (2 * σ ^ 2 - 1) * Real.cos (Real.arctan σ) ^ 5 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).2.1,
      Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
  -- on a neighbourhood of `σ` the derivative of the radial curve is `F1`
  have hFF : deriv (fun t => ρ (Real.arctan t) * Real.cos (Real.arctan t)) =ᶠ[𝓝 σ] F1 ρ := by
    filter_upwards [isOpen_Ioi.mem_nhds hσ] with τ hτ
    exact deriv_radCurve_eq_F1 hρ hτ
  have hD2 : deriv (deriv (fun t => ρ (Real.arctan t) * Real.cos (Real.arctan t))) σ
      = deriv (F1 ρ) σ :=
    Filter.EventuallyEq.deriv_eq hFF
  -- the value of the derivative of `F1` at `σ`, by the chain and product rules
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
        (deriv ρ (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := hρd.hasDerivAt.comp σ harc
    have hB : HasDerivAt (fun τ => deriv ρ (Real.arctan τ))
        (deriv (deriv ρ) (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ :=
      hρ2d.hasDerivAt.comp σ harc
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

end

end Work.OddCurve.Free
