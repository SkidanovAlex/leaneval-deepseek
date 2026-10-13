import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The slice relation for the zero-mode identity

This file proves `ZM_slice_relation`, the first ingredient of the `L₁₂` zero-mode identity
`L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)` of the Elgindi project.  In the notation of
`Submission/Work/FTS/Apriori/ZeroMode/L12_ZMDefs.lean`:

* `Kpz f p = K(p.2) · ∂_z f(p.1, p.2)` is the joint (radial, angular) integrand whose
  integrability `H.hint` is the only measure-theoretic input;
* the hypotheses `H.hdiff` (radial differentiability), `H.hdec` (decay at `∞`) and `H.hvan`
  give, for almost every `θ ∈ Iθ`, the radial fundamental theorem of calculus
  `∫_{Ioi r} K θ ∂_z f(u,θ) du = -(K θ f(r,θ))` **for every** `r > 0`;
* combining that a.e. identity with Tonelli/Fubini gives, again for every `r > 0`,
  the integrability of `θ ↦ K θ f(r,θ)` on `Iθ` (the finiteness of the `θ`-integral needs
  the `∫⁻`-bound `‖∫‖ₑ ≤ ∫⁻ ‖·‖ₑ` and the swap of the two `lintegral`s; the a.e.-strong
  measurability is the `θ`-slice of the jointly integrable integrand), and finally
  `∫_{Iθ} K θ f(r,θ) dθ = -NOf f r`, where `NOf f r` is the *joint* integral
  `∫_{(Ioi r) × Iθ} K(θ) ∂_z f(z,θ)`.

The remaining hypotheses of `L12Hyp` (`hα`, `hα1`, `hcont`, `hvan`, `hintL`, `hintL2`,
`hint3`) are not needed here; they are kept because the statement is part of the requested
interface of the zero-mode chapter.
-/

/-- The joint integrand `K(θ) · ∂_z f(z,θ)` as a function on the product `ℝ × ℝ`. -/
private noncomputable def Kpz (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2

/-- The radial averaging identity for the integrand `K(θ) ∂_z f`.

For almost every `θ ∈ Iθ` the radial function `u ↦ K(θ) · f(u,θ)` has derivative
`K(θ) · ∂_z f(u,θ)` on `(0,∞)`, is continuous up to `0`, tends to `0` at `+∞` and its
derivative is integrable on `(0,∞)`; hence the fundamental theorem of calculus gives the
identity for every `r > 0` at once (the good `θ`-set does not depend on `r`). -/
private theorem slice_relation_ae {α : ℝ} {f : ℝ → ℝ → ℝ}
    (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ r : ℝ, 0 < r →
      ∫ u in Set.Ioi r, Kpz f (u, θ) = -(Work.Spaces.K θ * f r θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- `H.hint`, read as integrability for the product of the two restricted measures
  have hprod0 : Integrable (Kpz f)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Measure.prod_restrict]
    exact H.hint
  -- a.e. in `θ`, the radial slice of the integrand is integrable on `(0,∞)`
  have hslice : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      IntegrableOn (fun u => Kpz f (u, θ)) (Set.Ioi 0) := by
    simpa [IntegrableOn] using hprod0.prod_left_ae
  filter_upwards [hslice, self_mem_ae_restrict hIθ] with θ hInt hmem
  intro r hr
  have hderiv : ∀ x ∈ Set.Ioi r, HasDerivAt (fun u : ℝ => Work.Spaces.K θ * f u θ)
      (Work.Spaces.K θ * Work.Spaces.pz f x θ) x := fun x hx =>
    (H.hdiff θ hmem x (lt_trans hr hx)).const_mul (Work.Spaces.K θ)
  have hcont' : ContinuousWithinAt (fun u : ℝ => Work.Spaces.K θ * f u θ) (Set.Ici r) r :=
    ((H.hdiff θ hmem r hr).continuousAt.continuousWithinAt).const_mul (Work.Spaces.K θ)
  have hint' : IntegrableOn (fun u : ℝ => Work.Spaces.K θ * Work.Spaces.pz f u θ)
      (Set.Ioi r) :=
    hInt.mono_set (Set.Ioi_subset_Ioi (le_of_lt hr))
  have hlim' : Tendsto (fun u : ℝ => Work.Spaces.K θ * f u θ) atTop (𝓝 0) := by
    simpa using (H.hdec θ hmem).const_mul (Work.Spaces.K θ)
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont' hderiv hint' hlim'
  simpa [Kpz] using this

/-- Integrability of the angular slice `θ ↦ K(θ) f(r,θ)` on `Iθ`, for **every** `r > 0`.

The a.e.-strong measurability is `AEStronglyMeasurable.integral_prod_right'` applied to the
swapped jointly integrable integrand; the finiteness of the `∫⁻`-norm is the inequality
`‖∫‖ₑ ≤ ∫⁻ ‖·‖ₑ` together with the a.e. identity `slice_relation_ae` and Tonelli's theorem
for `lintegral`s. -/
private theorem slice_integrable {α : ℝ} {f : ℝ → ℝ → ℝ}
    (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ := by
  have hA := slice_relation_ae H
  -- integrability of the integrand over `(r,∞) × Iθ`
  have hprod : Integrable (Kpz f)
      ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h0 : IntegrableOn (Kpz f) (Set.Ioi r ×ˢ Work.Spaces.Iθ) :=
      H.hint.mono_set (Set.prod_mono (Set.Ioi_subset_Ioi (le_of_lt hr)) subset_rfl)
    rw [Measure.prod_restrict]
    exact h0
  refine ⟨?_, ?_⟩
  · -- a.e. strong measurability, as the `θ`-slice of a jointly integrable function
    have hswapM : AEStronglyMeasurable (fun z : ℝ × ℝ => Kpz f z.swap)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioi r))) :=
      hprod.1.prod_swap
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => ∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r)))
        (volume.restrict Work.Spaces.Iθ) := hswapM.integral_prod_right'
    refine (h1.neg).congr ?_
    filter_upwards [hA] with θ hθ
    simp only [Pi.neg_apply]
    rw [hθ r hr]
    ring
  · -- finiteness of the `θ`-integral of the norm
    change (∫⁻ θ, ‖Work.Spaces.K θ * f r θ‖ₑ ∂(volume.restrict Work.Spaces.Iθ)) < ⊤
    have hAEM : AEMeasurable (fun p : ℝ × ℝ => ‖Kpz f p‖ₑ)
        ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) :=
      hprod.1.aemeasurable.enorm
    have hcomp : ∫⁻ θ, ‖Work.Spaces.K θ * f r θ‖ₑ ∂(volume.restrict Work.Spaces.Iθ)
        ≤ ∫⁻ θ, (∫⁻ u, ‖Kpz f (u, θ)‖ₑ ∂(volume.restrict (Set.Ioi r)))
            ∂(volume.restrict Work.Spaces.Iθ) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hA] with θ hθ
      have heq : ‖Work.Spaces.K θ * f r θ‖ₑ
          = ‖∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r))‖ₑ := by
        rw [hθ r hr, enorm_neg]
      rw [heq]
      exact enorm_integral_le_lintegral_enorm _
    have hswap : (∫⁻ θ, (∫⁻ u, ‖Kpz f (u, θ)‖ₑ ∂(volume.restrict (Set.Ioi r)))
            ∂(volume.restrict Work.Spaces.Iθ))
        = ∫⁻ p, ‖Kpz f p‖ₑ
            ∂((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
      rw [← lintegral_prod_symm (fun p : ℝ × ℝ => ‖Kpz f p‖ₑ) hAEM]
    exact lt_of_le_of_lt (le_trans hcomp (le_of_eq hswap)) hprod.2

/-- The angular slice identity `∫_{Iθ} K(θ) f(r,θ) dθ = -NOf f r` for every `r > 0`.

`NOf f r` is the joint integral of `K ∂_z f` over `(r,∞) × Iθ`; Fubini turns it into the
iterated integral, `slice_relation_ae` identifies the inner integral with `-(K θ f(r,θ))`
for a.e. `θ`, and the outer integration is linear. -/
private theorem slice_value {α : ℝ} {f : ℝ → ℝ → ℝ}
    (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ)
      = - Work.FTS.Apriori.ZeroMode.NOf f r := by
  have hA := slice_relation_ae H
  have hprod : Integrable (Kpz f)
      ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h0 : IntegrableOn (Kpz f) (Set.Ioi r ×ˢ Work.Spaces.Iθ) :=
      H.hint.mono_set (Set.prod_mono (Set.Ioi_subset_Ioi (le_of_lt hr)) subset_rfl)
    rw [Measure.prod_restrict]
    exact h0
  -- `NOf f r` is the integral of the integrand against the product measure
  have hNof : Work.FTS.Apriori.ZeroMode.NOf f r
      = ∫ p, Kpz f p
          ∂((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
    show (∫ p in (Set.Ioi r) ×ˢ Work.Spaces.Iθ, Kpz f p) = _
    rw [show (volume : Measure (ℝ × ℝ))
        = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
    rw [Measure.prod_restrict]
  have hcurried : Integrable (Function.uncurry (fun u θ => Kpz f (u, θ)))
      ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := hprod
  have hswap : (∫ p, Kpz f p
        ∂((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, (∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r)))
          ∂(volume.restrict Work.Spaces.Iθ) := by
    rw [integral_prod _ hprod, integral_integral_swap hcurried]
  have hinner : (∫ θ, (∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r)))
        ∂(volume.restrict Work.Spaces.Iθ))
      = ∫ θ, -(Work.Spaces.K θ * f r θ) ∂(volume.restrict Work.Spaces.Iθ) := by
    refine integral_congr_ae ?_
    filter_upwards [hA] with θ hθ
    exact hθ r hr
  have hmain : Work.FTS.Apriori.ZeroMode.NOf f r
      = -(∫ θ, Work.Spaces.K θ * f r θ ∂(volume.restrict Work.Spaces.Iθ)) := by
    rw [hNof, hswap, hinner, integral_neg]
  linarith [hmain]

theorem ZM_slice_relation {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ r : ℝ, 0 < r →
      ∫ u in Set.Ioi r, Work.Spaces.K θ * Work.Spaces.pz f u θ
        = -(Work.Spaces.K θ * f r θ))
    ∧ (∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ)
    ∧ (∀ r : ℝ, 0 < r →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ) = - Work.FTS.Apriori.ZeroMode.NOf f r) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Kpz] using slice_relation_ae H
  · intro r hr
    exact slice_integrable H hr
  · intro r hr
    exact slice_value H hr

end Work.FTS.Apriori.ZeroMode
