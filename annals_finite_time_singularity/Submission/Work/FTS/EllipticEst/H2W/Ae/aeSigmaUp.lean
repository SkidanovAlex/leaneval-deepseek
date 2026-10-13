import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-!
# `H2W.Ae.aeSigmaUp` — the `σ`-upgrade of the level-`0` `ℋ`-mass of `u`

```
∃ C > 0, ∀ α u G, AeData α u G →
    L2Mem (∂_θu · w) → HkSq α 0 u ≤ C · L2Sq (∂_θu · w) .
```

The right-hand side is the *unweighted* angular square integral of `∂_θu` (with the radial
weight `w` inside), while the left-hand side carries the singular angular weight
`σ θ = sin(2θ)^{-η}`.  The content is the slicewise `σ`-Poincaré inequality of
`Work.FTS.EllipticEst.Honest.SigmaPoincare`: for a fibre `u(z,·)` with vanishing moment
`∫_θ u(z,θ) sinθcos²θ dθ = 0` (which `AeData` supplies for almost every `z`)

  `∫_θ u(z,θ)² σ θ ≤ C ∫_θ (∂_θu(z,θ))²`,

valid for almost every `z > 0`.  That a.e. bound is exactly `H2W.AeProof.AeSigmaUpgradeU_ae`
(in `lintegral` form), and `H2W.AeProof.AeSliceMomentU_integrable` discharges its honesty
hypothesis.

The only work left here is bookkeeping: multiply by the *nonnegative* radial weight `w(z)²`
(so that the singular weight is restored on the left and the honest integrand `(∂_θu·w)²`
appears on the right), convert the two `lintegral`s into honest integrals of the actual
`HkSq`/`L2Sq` integrands and integrate in `z`.

Two points of care: since `w z` sits *inside* the square on the right, no division by `w z`
is ever needed; and honesty of `θ ↦ HkIntegrand α 0 u z θ` is *not* assumed — the
Bochner–`lintegral` conversion is done under a case split, the non-integrable case giving the
inequality trivially, because the totalised Bochner integral is then `0` (the same dichotomy
that `H2W.HkSq_le_of_ae_slice_le` uses at the level of the whole domain).
-/

/-- The pointwise normalisation of the level-`0` integrand, in terms of
`Work.FTS.EllipticEst.sEta` (a definitionally equal copy of the weight `AngSecond.sig`). -/
private theorem hkIntegrand_zero_sEta (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α g z hθ]
  ring

/-- **The a.e. slice inequality in honest-integral form.**  From the `σ`-upgrade of the fibre
`u(z,·)` (in `lintegral` form) and the honesty of `θ ↦ (∂_θu(z,θ)·w z)²`, we get the
comparison of the honest `θ`-integrals of the level-`0` integrand of `u` and of the square of
the weighted angular derivative. -/
private theorem aeSlice_le_Ioi {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {C : ℝ}
    (hC : 0 < C)
    (hE : Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z))
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal C * ∫⁻ θ in Iθ,
            ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ C * ∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2 := by
  filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
  have hzIz : z ∈ Iz := Set.mem_Ici.mpr (le_of_lt hzpos)
  -- the right-hand slice integrand is honest by hypothesis
  have hRint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) Iθ := hE.1 z hzIz
  have hRnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- the level-`0` integrand of `u`, as an `ofReal (w² · (u²σ))`
  have hL : (∫⁻ θ in Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    rw [show (∫⁻ θ in Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
        = ∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [hkIntegrand_zero_sEta α u hθ,
        ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]]
    exact MeasureTheory.lintegral_const_mul'
      (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (fun θ => ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ENNReal.ofReal_ne_top
  -- the same for the weighted angular derivative
  have hX : ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
      = ∫⁻ θ in Iθ,
          ENNReal.ofReal ((Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) := by
    rw [← MeasureTheory.lintegral_const_mul'
      (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (fun θ => ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_congr fun θ => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    exact congrArg ENNReal.ofReal (by ring)
  have hR : ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (ENNReal.ofReal C * ∫⁻ θ in Iθ,
            ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
      = ENNReal.ofReal C
        * (∫⁻ θ in Iθ,
            ENNReal.ofReal ((Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)) := by
    rw [show ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal C * ∫⁻ θ in Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
        = ENNReal.ofReal C * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ∫⁻ θ in Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) from by ring,
      hX]
  -- the scaled `lintegral` inequality
  have hz' : (∫⁻ θ in Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      ≤ ENNReal.ofReal C
        * (∫⁻ θ in Iθ,
            ENNReal.ofReal ((Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)) :=
    calc (∫⁻ θ in Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := hL
      _ ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal C * ∫⁻ θ in Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) :=
          mul_le_mul' (le_refl _) hz
      _ = ENNReal.ofReal C
          * (∫⁻ θ in Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)) := hR
  -- the right-hand side, as an honest integral
  have hq : 0 ≤ C * ∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2 :=
    mul_nonneg (le_of_lt hC) (MeasureTheory.integral_nonneg_of_ae hRnn)
  rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal hRint hRnn).symm,
    ← ENNReal.ofReal_mul (le_of_lt hC)] at hz'
  -- the left-hand side: honest, or totalised to `0`
  by_cases hint : MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Iθ)
  · have hLnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hLnn] at hz'
    exact (ENNReal.ofReal_le_ofReal_iff hq).mp hz'
  · rw [MeasureTheory.integral_undef hint]
    exact hq

theorem aeSigmaUp : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
      Work.Spaces.HkSq α 0 u
        ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_ae
  refine ⟨C, hCpos, ?_⟩
  intro α u G h hE
  -- the honesty hypothesis of the slicewise `σ`-upgrade
  have hmom : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2)) Iθ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentU_integrable α u G h hz
  -- the a.e. slice inequality, in the form of the two level-`0` integrands
  have hslice := aeSlice_le_Ioi h hCpos hE (hC α u G h hmom)
  -- transport it from `Ioi 0` to `Iz = Ici 0` (they differ by the null set `{0}`)
  have houter : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ C * ∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2 := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hslice
  by_cases hInt : MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Iz)
  · -- honest left-hand side: integrate the a.e. inequality
    have hmono := MeasureTheory.integral_mono_ae hInt (hE.2.const_mul C) houter
    rw [MeasureTheory.integral_const_mul] at hmono
    simpa only [Work.Spaces.HkSq, Work.Spaces.L2Sq] using hmono
  · -- non-honest left-hand side: the totalised integral is `0`
    change (∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ C * ∫ z in Iz, ∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2
    rw [MeasureTheory.integral_undef hInt]
    exact mul_nonneg (le_of_lt hCpos)
      (MeasureTheory.integral_nonneg fun z =>
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _)

end

end Work.FTS.EllipticEst.H2W.Ae
