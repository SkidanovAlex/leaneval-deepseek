import Mathlib
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddEnvelope.Close.profileX_deriv_formulas

/-!
# The first and second derivatives of the low-slope chord curve, minus the semicircle's

`lowSlopeCurveY R Y` is the right-hand chord-endpoint function of the low-slope reconstruction
(see `Submission/Work/OddCurve/LowSlope/CurveDefs.lean`): on the low-slope piece `σ < 3/4` it is
the radial parametrisation `σ ↦ R (arctan σ) * cos (arctan σ)`, and for `σ ≥ 3/4` it is the
anchor's curve `Y`.

Here we compute, for `0 < σ < 3/4`, the deviation of its first and second derivatives from those
of the semicircle's chord function `profileX σ = cos (arctan σ)` — the §4 formulas of the
low-slope endgame.  Writing `c = cos (arctan σ)`, `s = sin (arctan σ)`, `A = R (arctan σ)`,
`B = deriv R (arctan σ)`, `C = deriv (deriv R) (arctan σ)`, they read

* `deriv (lowSlopeCurveY R Y) σ - deriv profileX σ = c^2 * (B * c - (A - 1) * s)`,
* `deriv (deriv (lowSlopeCurveY R Y)) σ - deriv (deriv profileX) σ
     = -4 * c^4 * s * B + c^5 * C + (2 * c^3 * s^2 - c^5) * (A - 1)`.

The only input on `R` is `C^∞`-smoothness on the closed interval `[0, π/2]`, which suffices
because `arctan σ ∈ (0, π/2)` is an interior point; nothing is assumed of the anchor curve `Y`.

The basic identity used throughout is `σ * cos (arctan σ) = sin (arctan σ)`, together with the
elementary values `deriv arctan σ = (1 + σ^2)⁻¹ = cos (arctan σ)^2` (the former in the
`Real.hasDerivAt_arctan'` normalisation `(1 + τ^2)⁻¹`).
-/

namespace Work.OddCurve.LowSlope

open Filter Topology Set
open scoped ContDiff

noncomputable section

/-- The explicit expression of `deriv (fun τ => R (arctan τ) * cos (arctan τ))` on the low-slope
piece, written as a pointwise product so that the chain/product-rule lemmas apply syntactically. -/
private def F1 (R : ℝ → ℝ) : ℝ → ℝ :=
  (fun τ : ℝ => (1 + τ ^ 2)⁻¹) *
    ((fun τ => deriv R (Real.arctan τ)) * (fun τ => Real.cos (Real.arctan τ))
      - (fun τ => R (Real.arctan τ)) * (fun τ => Real.sin (Real.arctan τ)))

/-- On the low-slope piece the derivative of the radial parametrisation is `F1`.  Only
`0 < τ` is needed: then `arctan τ ∈ (0, π/2)` is an interior point of the interval on which `R`
is smooth. -/
private lemma deriv_piece_eq_F1 {R : ℝ → ℝ} {τ : ℝ}
    (hR : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2))) (hτ : 0 < τ) :
    deriv (fun t => R (Real.arctan t) * Real.cos (Real.arctan t)) τ = F1 R τ := by
  have ha : Real.arctan τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_pos.mpr hτ, Real.arctan_lt_pi_div_two τ⟩
  have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan τ) :=
    mem_of_superset (isOpen_Ioo.mem_nhds ha) (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hRc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Real.arctan τ) := hR.contDiffAt hmem
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hRd : DifferentiableAt ℝ R (Real.arctan τ) := hRc.differentiableAt hne
  have harc : HasDerivAt Real.arctan ((1 + τ ^ 2)⁻¹) τ := Real.hasDerivAt_arctan' τ
  have h1 : HasDerivAt (fun t => R (Real.arctan t))
      (deriv R (Real.arctan τ) * (1 + τ ^ 2)⁻¹) τ := hRd.hasDerivAt.comp τ harc
  have h2 : HasDerivAt (fun t => Real.cos (Real.arctan t))
      (-Real.sin (Real.arctan τ) * (1 + τ ^ 2)⁻¹) τ := (Real.hasDerivAt_cos _).comp τ harc
  have h3d : deriv (fun t => R (Real.arctan t) * Real.cos (Real.arctan t)) τ
      = deriv R (Real.arctan τ) * (1 + τ ^ 2)⁻¹ * Real.cos (Real.arctan τ)
        + R (Real.arctan τ) * (-Real.sin (Real.arctan τ) * (1 + τ ^ 2)⁻¹) := (h1.mul h2).deriv
  show deriv (fun t => R (Real.arctan t) * Real.cos (Real.arctan t)) τ = _
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

theorem lowSlopeCurveY_derivs_sub {R Y : ℝ → ℝ} {σ : ℝ} (h0 : 0 < σ) (h : σ < 3 / 4)
    (hR : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2))) :
    deriv (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) σ -
        deriv Work.OddEnvelope.profileX σ =
      Real.cos (Real.arctan σ) ^ 2 *
        (deriv R (Real.arctan σ) * Real.cos (Real.arctan σ) -
          (R (Real.arctan σ) - 1) * Real.sin (Real.arctan σ)) ∧
    deriv (deriv (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)) σ -
        deriv (deriv Work.OddEnvelope.profileX) σ =
      (-4 : ℝ) * Real.cos (Real.arctan σ) ^ 4 * Real.sin (Real.arctan σ)
          * deriv R (Real.arctan σ) +
        Real.cos (Real.arctan σ) ^ 5 * deriv (deriv R) (Real.arctan σ) +
        (2 * Real.cos (Real.arctan σ) ^ 3 * Real.sin (Real.arctan σ) ^ 2 -
          Real.cos (Real.arctan σ) ^ 5) * (R (Real.arctan σ) - 1) := by
  obtain ⟨ha1, ha2⟩ : Real.arctan σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_pos.mpr h0, Real.arctan_lt_pi_div_two σ⟩
  have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arctan σ) :=
    mem_of_superset (isOpen_Ioo.mem_nhds ⟨ha1, ha2⟩)
      (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hRc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Real.arctan σ) := hR.contDiffAt hmem
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hRd : DifferentiableAt ℝ R (Real.arctan σ) := hRc.differentiableAt hne
  have hR2d : DifferentiableAt ℝ (deriv R) (Real.arctan σ) :=
    (hRc.derivWithin (by simp)).differentiableAt hne
  have hKval : (1 + σ ^ 2)⁻¹ = Real.cos (Real.arctan σ) ^ 2 := inv_one_add_sq
  have hσc : σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) :=
    mul_cos_arctan_eq_sin_arctan
  -- the derivative of the radial piece `τ ↦ R (arctan τ) * cos (arctan τ)`
  have hDg : deriv (fun τ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ
      = deriv R (Real.arctan σ) * Real.cos (Real.arctan σ) ^ 3
        - R (Real.arctan σ) * Real.sin (Real.arctan σ) * Real.cos (Real.arctan σ) ^ 2 := by
    have harc : HasDerivAt Real.arctan ((1 + σ ^ 2)⁻¹) σ := Real.hasDerivAt_arctan' σ
    have h1 : HasDerivAt (fun τ => R (Real.arctan τ))
        (deriv R (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := hRd.hasDerivAt.comp σ harc
    have h2 : HasDerivAt (fun τ => Real.cos (Real.arctan τ))
        (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_cos _).comp σ harc
    have h3d : deriv (fun τ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ
        = deriv R (Real.arctan σ) * (1 + σ ^ 2)⁻¹ * Real.cos (Real.arctan σ)
          + R (Real.arctan σ) * (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) :=
      (h1.mul h2).deriv
    rw [h3d, hKval]; ring
  -- `lowSlopeCurveY` agrees with the radial piece near `σ`
  have hD1 : deriv (lowSlopeCurveY R Y) σ
      = deriv (fun τ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ :=
    Filter.EventuallyEq.deriv_eq (f₁ := lowSlopeCurveY R Y)
      (f := fun τ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) (by
        filter_upwards [isOpen_Iio.mem_nhds h] with y hy
        exact lowSlopeCurveY_of_lt hy)
  -- the semicircle's derivative formulas
  have hP1 : deriv Work.OddEnvelope.profileX σ = -σ * Real.cos (Real.arctan σ) ^ 3 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).1, profileX_eq_cos_arctan]
  have hP2 : deriv (deriv Work.OddEnvelope.profileX) σ
      = (2 * σ ^ 2 - 1) * Real.cos (Real.arctan σ) ^ 5 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).2.1, profileX_eq_cos_arctan]
  -- on a neighbourhood of `σ` the derivative of `lowSlopeCurveY` is `F1`
  have hFF : deriv (lowSlopeCurveY R Y) =ᶠ[𝓝 σ] F1 R := by
    filter_upwards [isOpen_Iio.mem_nhds h, isOpen_Ioi.mem_nhds h0] with τ hτ hτ0
    have hev : deriv (lowSlopeCurveY R Y) τ
        = deriv (fun t => R (Real.arctan t) * Real.cos (Real.arctan t)) τ :=
      Filter.EventuallyEq.deriv_eq (f₁ := lowSlopeCurveY R Y)
        (f := fun t => R (Real.arctan t) * Real.cos (Real.arctan t)) (by
          filter_upwards [isOpen_Iio.mem_nhds hτ] with y hy
          exact lowSlopeCurveY_of_lt hy)
    rw [hev]
    exact deriv_piece_eq_F1 hR hτ0
  have hD2 : deriv (deriv (lowSlopeCurveY R Y)) σ = deriv (F1 R) σ :=
    Filter.EventuallyEq.deriv_eq hFF
  -- the value of the derivative of `F1` at `σ`, by the chain and product rules
  have hF1d : deriv (F1 R) σ =
      (-4 : ℝ) * Real.cos (Real.arctan σ) ^ 4 * Real.sin (Real.arctan σ)
          * deriv R (Real.arctan σ)
        + Real.cos (Real.arctan σ) ^ 5 * deriv (deriv R) (Real.arctan σ)
        + (2 * Real.cos (Real.arctan σ) ^ 3 * Real.sin (Real.arctan σ) ^ 2
            - Real.cos (Real.arctan σ) ^ 5) * (R (Real.arctan σ) - 1)
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
    have hA : HasDerivAt (fun τ => R (Real.arctan τ))
        (deriv R (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := hRd.hasDerivAt.comp σ harc
    have hB : HasDerivAt (fun τ => deriv R (Real.arctan τ))
        (deriv (deriv R) (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ :=
      hR2d.hasDerivAt.comp σ harc
    have hC : HasDerivAt (fun τ => Real.cos (Real.arctan τ))
        (-Real.sin (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_cos _).comp σ harc
    have hS : HasDerivAt (fun τ => Real.sin (Real.arctan τ))
        (Real.cos (Real.arctan σ) * (1 + σ ^ 2)⁻¹) σ := (Real.hasDerivAt_sin _).comp σ harc
    have hBC := (hB.mul hC).sub (hA.mul hS)
    have hF1 : HasDerivAt (F1 R) _ σ := hK.mul hBC
    rw [hF1.deriv, hKval]
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (norm := ring_nf)
      (-2 * Real.cos (Real.arctan σ) ^ 4 * deriv R (Real.arctan σ)
        + 2 * Real.cos (Real.arctan σ) ^ 3 * R (Real.arctan σ) * Real.sin (Real.arctan σ)
        - 2 * Real.cos (Real.arctan σ) ^ 3
            * (Real.sin (Real.arctan σ) + σ * Real.cos (Real.arctan σ))) * hσc
  refine ⟨?_, ?_⟩
  · rw [hD1, hDg, hP1]
    linear_combination (norm := ring_nf) (Real.cos (Real.arctan σ) ^ 2) * hσc
  · rw [hD2, hF1d, hP2]
    ring

end

end Work.OddCurve.LowSlope
