/-
Copyright: work module for the Elgindi finite-time singularity project.

# The ENNReal mixed-slot (angular weight `sin(2θ)^{-γ}`) estimate, **with smoothness**

`Work.Spaces.Slots.lintegral_mixed_gamma_le_HkSq` asks for

  `∫⁻_θ ∫⁻_s ofReal ((D_z^j D_θ^i f s θ)² (w s)² sin(2θ)^{-γ}) ≤ ofReal (HkSq α 4 f)`

under `HkMem α 4 f` alone (`1 ≤ i`, `i + j ≤ 4`).  Pointwise the integrand is *exactly* the
`(D_z^j D_θ^i f · Wt)²` summand of `HkIntegrand α 4 f`
(`mixed_Wt_sq_eq` below: `Wt α s θ² = (w s)² sin(2θ)^{-γ}`, valid for every `θ ∈ Iθ`), so
by the pointwise domination of that summand by the whole integrand the left-hand side is at
most `∫⁻_θ ∫⁻_s ofReal (HkIntegrand α 4 f s θ)`.

Identifying that last double `∫⁻` with `ofReal (HkSq α 4 f)` requires the exchange of the two
iterated integrals, i.e. Tonelli for the uncurried integrand
`(s,θ) ↦ ofReal (HkIntegrand α 4 f s θ)`, hence its a.e. strong measurability for the product
of the two restricted measures.  `HkMem α 4 f` supplies only the measurability of the
*angular* slices `θ ↦ HkIntegrand α 4 f z θ` (for each `z ∈ Iz`) together with the
integrability of the partially integrated function `z ↦ ∫_θ HkIntegrand α 4 f z θ`; it says
nothing about the `s`-slices, and no "one-sided Tonelli" theorem exists (that statement is
false in general — see the diagnosis in `Work.Spaces.Slots.lintegral_DzIter_le_HkSq`).

This file therefore proves the statement in the form in which it is *used* in this
development, namely with the standing smoothness hypothesis `SmoothNbhd f` — the same
hypothesis carried by every other exchange of these two integrations
(`Work.FTS.H2.HkSqSwap`, `Work.Spaces.HkSqSwap`, `Work.Elliptic.L12Aux`,
`Work.Spaces.HardyZLin.hardyZ_lintegral`, `Submission/Work/Spaces/Slots/lintegral_DzIter_le_HkSq_smooth.lean`, …).
Under it the uncurried `(s,θ) ↦ HkIntegrand α 4 f s θ` is continuous on the open quadrant
(hence a.e. strongly measurable for the product measure), and the proof is:

* pointwise on `Iz × Iθ`, `ofReal` of the slot integrand is `≤ ofReal (HkIntegrand α 4 f ·)`
  (`sq_le_HkIntegrand_mixed` together with `mixed_Wt_sq_eq`);
* Tonelli swaps the two `∫⁻` (`Work.Coercivity.aesm_uncurry_HkIntegrand` plus
  `MeasureTheory.lintegral_lintegral_swap`);
* for every `s ∈ Iz` the angular slice is integrable by `hmem.1`, so
  `∫⁻_θ ofReal (HkIntegrand α 4 f s θ) = ofReal (∫_θ HkIntegrand α 4 f s θ)`;
* `∫⁻_s ofReal (∫_θ HkIntegrand α 4 f s θ) = ofReal (HkSq α 4 f)` by `hmem.2` and
  `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.HkMem_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Spaces.Slots

set_option autoImplicit false

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The pointwise identity `(D_z^j D_θ^i f · Wt)² = (D_z^j D_θ^i f)² (w s)² sin(2θ)^{-γ}`,
valid for every `θ ∈ Iθ` (where `sin (2θ) ≥ 0`; at the two endpoints both sides vanish). -/
theorem mixed_Wt_sq_eq (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (j i : ℕ) {s θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed j i f s θ * Work.Spaces.Wt α s θ) ^ 2
      = (Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hgam : Work.Spaces.gam α ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hα)
  have hhalf : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro h
    exact hgam (by linarith [neg_eq_zero.mp h])
  -- `(sin(2θ)^{-γ/2})² = sin(2θ)^{-γ}`
  have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rcases eq_or_lt_of_le (sin_two_nonneg_Iθ hθ) with h0 | hpos
    · rw [← h0, Real.zero_rpow hhalf, Real.zero_rpow (neg_ne_zero.mpr hgam)]
      ring
    · rw [sq, ← Real.rpow_add hpos]
      congr 1
      ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hsq]
  ring

/-- **ENNReal form of the mixed-slot estimate with the angular weight `sin(2θ)^{-γ}`,
with the standing smoothness hypothesis.**  For `f` smooth on a neighbourhood of the closed
quadrant with `HkMem α 4 f`, `0 < α`, `1 ≤ i`, `i + j ≤ 4`, the iterated ENNReal integral
`∫⁻_θ ∫⁻_s ofReal ((D_z^j D_θ^i f)² w² sin(2θ)^{-γ})` over the closed quadrant
(with respect to `dθ dz`) is bounded by `ofReal (HkSq α 4 f)`. -/
theorem lintegral_mixed_gamma_le_HkSq_of_smooth (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 4 f) := by
  -- Joint a.e. strong measurability of the uncurried `HkIntegrand` for the *swapped* product.
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Coercivity.aesm_uncurry_HkIntegrand α 4 hsm
  have hswap_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.2 p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    haesm.prod_swap
  have hmeas : AEMeasurable
      (Function.uncurry fun θ s : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) := by
    exact hswap_aesm.aemeasurable.ennreal_ofReal
  -- Pointwise domination of the slot integrand by the `HkIntegrand`.
  have hle : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.mixed j i f s θ) ^ 2
            * (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        ≤ ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      lintegral_mono_ae <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun s _ =>
          ENNReal.ofReal_le_ofReal <| by
            rw [← mixed_Wt_sq_eq α hα f j i hθ]
            exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ i j hi hij
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
      ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s θ))) :=
        lintegral_mono_ae hle
    _ = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s θ))) :=
        MeasureTheory.lintegral_lintegral_swap
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (ν := MeasureTheory.volume.restrict Work.Spaces.Iz) hmeas
    _ = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) := by
        refine lintegral_congr_ae <|
          MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun s hs =>
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 s hs)
              (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ)).symm
    _ = ENNReal.ofReal (Work.Spaces.HkSq α 4 f) := by
        rw [Work.Spaces.HkSq]
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
          (Eventually.of_forall fun s =>
            integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ)).symm

end Work.Spaces.Slots
