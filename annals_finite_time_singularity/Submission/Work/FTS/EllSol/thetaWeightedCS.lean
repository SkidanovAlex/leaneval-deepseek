import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.FTS.EllSol.amgmRpow
import Submission.Work.FTS.EllSol.csNumeric

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllSol

/-- **Weighted Cauchy–Schwarz on the angular interval.**

For any `G : ℝ → ℝ`, if `τ ↦ sin(2τ)^{-η} · G τ ^ 2` is integrable on `Iθ = [0,π/2]`, then on
every subinterval `[θ₀,θ]` with `0 < θ₀ ≤ θ < π/2`

`∫_{θ₀}^{θ} |G| ≤ √(∫_{Iθ} sin(2τ)^{-η} G²) · √(∫_{θ₀}^{θ} sin(2τ)^{η})`.

The proof is the weighted Cauchy–Schwarz inequality `|G| = (|G| s^{-η/2}) · s^{η/2}` combined
with the pointwise AM–GM `amgmRpow` (applied at every `l > 0`) and the numerical optimisation
`csNumeric`; the (nonnegative) weight `sin(2τ)^{-η}` is *larger* on `Iθ` than on the
subinterval, which is why the first square root may be taken over the whole of `Iθ`.

No measurability of `G` is needed: the pointwise bound is integrated with
`MeasureTheory.integral_mono_of_nonneg`, which only requires the dominating function to be
integrable. -/
theorem weighted_cs_abs {η : ℝ} (hη : 0 ≤ η) {G : ℝ → ℝ}
    {θ₀ θ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀θ : θ₀ ≤ θ) (hθ : θ < Real.pi / 2)
    (hint : IntegrableOn (fun τ : ℝ => (Real.sin (2 * τ)) ^ (-η) * (G τ) ^ 2)
      Work.Spaces.Iθ) :
    ∫ τ in θ₀..θ, |G τ| ≤
      Real.sqrt (∫ τ in Work.Spaces.Iθ, (Real.sin (2 * τ)) ^ (-η) * (G τ) ^ 2)
        * Real.sqrt (∫ τ in θ₀..θ, (Real.sin (2 * τ)) ^ η) := by
  -- the subinterval is contained in `Iθ`
  have hsub : Ioc θ₀ θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt (lt_of_lt_of_le hθ₀ hx.1.le), le_of_lt (lt_of_le_of_lt hx.2 hθ)⟩
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- integrability of the weighted square on the subinterval
  have hIntIoc : IntegrableOn (fun τ : ℝ => (Real.sin (2*τ))^(-η) * (G τ)^2)
      (Ioc θ₀ θ) := hint.mono_set hsub
  -- `sin (2τ) > 0` on the subinterval
  have hsinpos : ∀ x ∈ Ioc θ₀ θ, 0 < Real.sin (2*x) := by
    intro x hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hθ])
  -- integrability of the pure weight `sin(2τ)^η` on the subinterval
  have hIntB : IntegrableOn (fun x : ℝ => (Real.sin (2*x))^η) (Ioc θ₀ θ) := by
    have hc : Continuous fun x : ℝ => Real.sin (2*x)^η :=
      (Real.continuous_rpow_const hη).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- nonnegativity of the two integral bounds
  have hA1 : 0 ≤ ∫ x in Ioc θ₀ θ, (Real.sin (2*x))^(-η) * (G x)^2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (hsinpos x hx)) _) (sq_nonneg _)
  have hB : 0 ≤ ∫ x in Ioc θ₀ θ, (Real.sin (2*x))^η := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg (le_of_lt (hsinpos x hx)) _
  -- the subinterval integral is dominated by the integral over all of `Iθ`
  have hA1A : (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^(-η) * (G x)^2)
      ≤ ∫ x in Work.Spaces.Iθ, (Real.sin (2*x))^(-η) * (G x)^2 := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem hIθ_meas] with x hx
      exact mul_nonneg
        (Real.rpow_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2])) _)
        (sq_nonneg _)
    · exact Eventually.of_forall (fun x hx => hsub hx)
  -- the parametrised pointwise bound, integrated
  have hmain : ∀ l : ℝ, 0 < l →
      (∫ x in Ioc θ₀ θ, |G x|) ≤
        l * (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^(-η) * (G x)^2) / 2
          + (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^η) / (2 * l) := by
    intro l hl
    have hpoint : (fun x => |G x|) ≤ᵐ[volume.restrict (Ioc θ₀ θ)]
        (fun x => l / 2 * ((Real.sin (2*x))^(-η) * (G x)^2)
          + (2*l)⁻¹ * (Real.sin (2*x))^η) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact amgmRpow hη hl (hsinpos x hx)
    have h2int : Integrable (fun x => l / 2 * ((Real.sin (2*x))^(-η) * (G x)^2)
        + (2*l)⁻¹ * (Real.sin (2*x))^η) (volume.restrict (Ioc θ₀ θ)) :=
      (hIntIoc.const_mul (l/2)).add (hIntB.const_mul ((2*l)⁻¹))
    have hmono : (∫ x, |G x| ∂(volume.restrict (Ioc θ₀ θ))) ≤
        ∫ x, (l / 2 * ((Real.sin (2*x))^(-η) * (G x)^2)
          + (2*l)⁻¹ * (Real.sin (2*x))^η) ∂(volume.restrict (Ioc θ₀ θ)) :=
      integral_mono_of_nonneg (Eventually.of_forall (fun x => abs_nonneg (G x))) h2int hpoint
    have hIntSum : (∫ x, (l / 2 * ((Real.sin (2*x))^(-η) * (G x)^2)
          + (2*l)⁻¹ * (Real.sin (2*x))^η) ∂(volume.restrict (Ioc θ₀ θ)))
        = l/2 * (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^(-η) * (G x)^2)
          + (2*l)⁻¹ * (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^η) := by
      rw [integral_add (hIntIoc.const_mul (l/2)) (hIntB.const_mul ((2*l)⁻¹)),
        integral_const_mul, integral_const_mul]
    calc (∫ x in Ioc θ₀ θ, |G x|) = ∫ x, |G x| ∂(volume.restrict (Ioc θ₀ θ)) := rfl
      _ ≤ _ := hmono
      _ = l/2 * (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^(-η) * (G x)^2)
            + (2*l)⁻¹ * (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^η) := hIntSum
      _ = l * (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^(-η) * (G x)^2) / 2
            + (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^η) / (2 * l) := by
          rw [inv_mul_eq_div]; ring
  have hkey := csNumeric hA1 hA1A hB hmain
  calc ∫ τ in θ₀..θ, |G τ| = ∫ x in Ioc θ₀ θ, |G x| :=
        intervalIntegral.integral_of_le hθ₀θ
    _ ≤ Real.sqrt (∫ x in Work.Spaces.Iθ, (Real.sin (2*x))^(-η) * (G x)^2)
          * Real.sqrt (∫ x in Ioc θ₀ θ, (Real.sin (2*x))^η) := hkey
    _ = Real.sqrt (∫ τ in Work.Spaces.Iθ, (Real.sin (2*τ))^(-η) * (G τ)^2)
          * Real.sqrt (∫ τ in θ₀..θ, (Real.sin (2*τ))^η) := by
        rw [intervalIntegral.integral_of_le hθ₀θ]

theorem thetaWeightedCS {η : ℝ} (hη : 0 ≤ η) {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun τ : ℝ => (Real.sin (2 * τ)) ^ (-η) * (deriv (deriv f) τ) ^ 2) Work.Spaces.Iθ)
    {θ₀ θ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀θ : θ₀ ≤ θ) (hθ : θ < Real.pi / 2) :
    ∫ τ in θ₀..θ, |deriv (deriv f) τ| ≤
      Real.sqrt (∫ τ in Work.Spaces.Iθ,
          (Real.sin (2 * τ)) ^ (-η) * (deriv (deriv f) τ) ^ 2)
        * Real.sqrt (∫ τ in θ₀..θ, (Real.sin (2 * τ)) ^ η) :=
  weighted_cs_abs hη hθ₀ hθ₀θ hθ hint

end Work.FTS.EllSol
