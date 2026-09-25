import Mathlib
import Submission.Work.CR.Flat.Cauchy.polarDz

open scoped NNReal ENNReal Real Topology
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## The `θ`-derivative of `M`, as a continuous function of `(r,θ)`

`polG F p` is the value of `∂_θ (θ ↦ M(r,θ))` at `θ = p.2`, i.e. the factor appearing in
`hasDerivAt_polM_theta`.  By construction `polZ2 F p = -(i/2) polG F p / p.1`. -/

/-- The `θ`-derivative of the polar numerator `M = polM F`,
`∂_θ M = e^{-2iθ}(∂_θ(F(ρe^{iθ}) - F 0) - 2 i (F(ρe^{iθ}) - F 0))`, as a function of `p = (ρ,θ)`.
The statement of `hasDerivAt_polM_theta` is definitionally this expression. -/
noncomputable def polG (F : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ *
    (polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)))

/-- `polZ2` is `-(i/2) · ∂_θ M / ρ`, by definition of `polG`. -/
lemma polZ2_eq (F : ℂ → ℂ) (p : ℝ × ℝ) :
    polZ2 F p = -((Complex.I / 2) * polG F p / (p.1 : ℂ)) := rfl

lemma continuous_polG {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (polG F) := by
  have hp : Continuous (fun p : ℝ × ℝ => (polarUnit p.2)⁻¹) := by
    rw [show (fun p : ℝ × ℝ => (polarUnit p.2)⁻¹) = fun p : ℝ × ℝ => polarUnit (-p.2) by
      funext p; rw [polarUnit_neg]]
    exact continuous_polarUnit.comp continuous_snd.neg
  refine hp.mul (hp.mul ?_)
  refine ((continuous_polB hF).sub ?_)
  exact continuous_const.mul ((hF.continuous.comp continuous_polarCoord_symm).sub continuous_const)

/-- The angular integral of `polZ2 F (r,·)` vanishes for every `r > 0`: it is
`-(i/2)/r` times `∫_{-π}^{π} ∂_θ M(r,θ) dθ = M(r,π) - M(r,-π) = 0`. -/
lemma setIntegral_polZ2_inner {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) {r : ℝ} (_hr : 0 < r) :
    ∫ θ in Ioo (-Real.pi) Real.pi, polZ2 F (r, θ) = 0 := by
  -- the `θ`-fundamental theorem of calculus for `θ ↦ M(r,θ)`
  have hM : ∫ θ in Ioo (-Real.pi) Real.pi, polG F (r, θ) = 0 := by
    have hcont : Continuous fun θ : ℝ => polG F (r, θ) :=
      (continuous_polG hF).comp (continuous_const.prodMk continuous_id)
    have hderiv : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun θ : ℝ => polM F (r, θ)) (polG F (r, θ)) θ :=
      fun θ _ => hasDerivAt_polM_theta hF (r, θ)
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc' Real.volume_singleton)]
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
    rw [polM_pi]
    ring
  -- pull the constant `-(i/2)/r` out of the integral
  have hpt : ∀ θ : ℝ, polZ2 F (r, θ) = (-(Complex.I / 2) / (r : ℂ)) * polG F (r, θ) := by
    intro θ
    rw [polZ2_eq F (r, θ)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hpt θ),
    MeasureTheory.integral_const_mul, hM, mul_zero]

/-- The angular part of the polar integrand integrates to zero over the disc
`(0,ρ) × (-π,π)`:

`∫_{(0,ρ)×(-π,π)} polZ2 F = -(i/2) ∫_0^ρ (1/r) (∫_{-π}^{π} ∂_θ M(r,θ) dθ) dr
  = -(i/2) ∫_0^ρ (1/r) (M(r,π) - M(r,-π)) dr = 0`,

where `M = polM F` satisfies `∂_θ M = e^{-2iθ} (∂_θ(F(ρe^{iθ}) - F 0) - 2i(F(ρe^{iθ}) - F 0))`
(`hasDerivAt_polM_theta`), the inner integral is evaluated by
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, and the boundary terms agree because
`polarCoord.symm (r,π) = polarCoord.symm (r,-π)` (`polM_pi`).  The Fubini step needs integrability
of `polZ2 F` on the disc, which is `integrableOn_polZ2` (from the pointwise bound
`norm_polZ2_le`).  All these are in `Submission/Work/CR/Flat/Cauchy/polarDz.lean`. -/
theorem setIntegral_polZ2_zero {ρ : ℝ} (hρ : 0 < ρ) {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : Work.CR.Flat.SupportedInBall ρ F) :
    ∫ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi,
        Work.CR.Flat.Cauchy.polZ2 F p
      ∂(MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.volume) = 0 := by
  -- Fubini: the box is a product of intervals and `polZ2 F` is integrable on it
  rw [setIntegral_prod _ (integrableOn_polZ2 hF hsupp)]
  -- the inner `θ`-integral vanishes identically in `r`
  rw [setIntegral_congr_fun measurableSet_Ioo (fun r hr => setIntegral_polZ2_inner hF hr.1)]
  simp

end Work.CR.Flat.Cauchy
