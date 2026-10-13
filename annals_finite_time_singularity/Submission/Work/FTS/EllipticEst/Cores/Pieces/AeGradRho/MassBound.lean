import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.Honest.LzeroSelfFormHon
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AeU2.aeU2_bound
import Submission.Work.FTS.EllipticEst.AngAWeak.aeEnergyWAux
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSliceBdd
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.H2W.ESV.MassBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## Two elementary facts -/

/-- The restriction of Lebesgue measure to `Iz = [0,∞)` is that to `(0,∞)`: the two sets differ
by the null singleton `{0}`. -/
private lemma restrict_Iz_eq_restrict_Ioi :
    (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

/-- The angular weight `σ = sin(2θ)^{-η}` dominates `1` off the two endpoints. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : (-(Work.Spaces.eta) : ℝ) ≤ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs h1 hc
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `ofReal` of a nonnegative Bochner integral is dominated by the `lintegral` of its `ofReal`,
for any function (no measurability needed: a non-strongly-measurable function has integral `0`). -/
private lemma ofReal_integral_le_lintegral' {μ : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
    (hnn : ∀ θ, 0 ≤ f θ) :
    ENNReal.ofReal (∫ θ, f θ ∂μ) ≤ ∫⁻ θ, ENNReal.ofReal (f θ) ∂μ := by
  by_cases h : MeasureTheory.AEStronglyMeasurable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) h]
    exact ENNReal.ofReal_toReal_le
  · rw [MeasureTheory.integral_undef (fun hi => h hi.aestronglyMeasurable)]
    simp

/-! ## The `HkSq α 0`-mass of `u` against the `σ`-mass -/

/-- For `u` whatsoever, `ofReal (HkSq α 0 u)` is dominated by the `σ`-weighted angular mass
of `u`. -/
private theorem ofReal_HkSq_le_sigmaMass (α : ℝ) {u : ℝ → ℝ → ℝ} :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 u) ≤
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have step1 : ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) :=
    ofReal_integral_le_lintegral'
      (fun z => integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ) :=
    MeasureTheory.lintegral_mono
      (fun z => ofReal_integral_le_lintegral'
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ)
          = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α u hθ,
          ENNReal.ofReal_mul (sq_nonneg _)])
    rw [MeasureTheory.lintegral_congr_ae hae,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [Work.Spaces.HkSq]
    _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
private lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

end

/-! **The `u`-mass bound of Step 1 of `prop:H2` in the `AeData` class**, from the paper's
`w²`-weighted radial energy inequality (★) — the statement of
`Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl` / `Cores.Pieces.AeGradRho.ae_w2_energy` — taken
here as the hypothesis `hW2`.

Chain: (★) plus the constrained slice gap `9∫u² ≤ ∫(∂_θu)²` (a.e. in `z`) gives the bound.

The statement `Cores.Pieces.AeGradRho.ae_mass_bound_of` itself is provided elsewhere in the tree
(`Submission/Work/FTS/EllipticEst/H2W/ESV/MassBound.lean`, imported above) — the two copies were
identical duplicates (dedup of 2026-10-10, see `EllipticEst/NOTES_DEDUP_AUDIT.md`). -/

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
