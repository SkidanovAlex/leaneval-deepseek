import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseB1Cube.PortSmallB.kinFTEnergyLintegralOne
import Submission.Work.BoseB1Cube.PortSmallB.kinFTSqLintegralOne
import Submission.Work.BoseB1Cube.Winchk
import Submission.Work.BoseFixB1B.cutAmplitude_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.PortSmallB.cutAmplitudeIntegrableThree`

Integrability in `p` of the windowed amplitude forms

`p ↦ (L³)⁻¹ ∫_{abox (n+1) L} ‖tBamp χ p Φ i x‖²` and its `‖p‖²`-weighted version,

where the state `Φ = boxQ volA A i Ψ` is only *a.e. measurable* and *bounded* on the box, and
where — unlike `Work.BoseFixB1B.cutAmplitude_integrable` — the window `χ` and the windowed slot
fibres `z ↦ χ z·Φ(x_{i←z})` are only assumed to be of class `C³` (this is the regularity of the
cube window `chiSmallB M` with `M = 48`, i.e. `C^{47}`, in the applications).

## The argument

It is the same Tonelli/Plancherel argument as in `Work.BoseFixB1B.cutAmplitude_integrable_aux`,
with the two `C^∞` fibre Plancherel inputs replaced by their `C¹` versions:

* the amplitude is the `p`-convention Fourier transform of the windowed fibre `u_x`
  (`Work.BoseFixB1B.tBamp_eq_kinFT_update`), and `u_x` is `C³` with compact support;
* consequently the two `lintegral` bounds of the fibre — `∫⁻_p ofReal ‖kinFT u_x p‖² ≤
  ofReal((2π)³ ∫u_x²)` and `∫⁻_p ofReal (‖p‖²‖kinFT u_x p‖²) ≤ ofReal((2π)³ ∫Σ_k (∂_k u_x)²)` —
  are exactly `Work.BoseB1Cube.PortSmallB.kinFTSqLintegralOne` and
  `Work.BoseB1Cube.PortSmallB.kinFTEnergyLintegralOne` (both `C¹`-level facts: Plancherel for
  `L¹ ∩ L²`, and the low-regularity gradient Plancherel);
* the remaining bookkeeping (joint a.e. strong measurability of `tBamp`, Tonelli, the pointwise
  fibre bounds `hdir`/`hB`, and the `ofReal`/`lintegral` comparisons) is carried out in
  `cutAmplitudeIntegrableThree_aux`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseB1Cube.PortSmallB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- **The assembly of the target.**  Integrability of the two windowed amplitude forms for a
state `Φ` that is a.e. measurable on the box, given the two per-fibre `lintegral` bounds of the
slot amplitude (the `x`-pointwise Plancherel inputs, supplied at `C³` by
`kinFTSqLintegralOne`/`kinFTEnergyLintegralOne`).

This is the content of `Work.BoseFixB1B.cutAmplitude_integrable_aux` with the two `C^∞` fibre
Plancherel applications factored out as hypotheses. -/
theorem cutAmplitudeIntegrableThree_aux {n : ℕ} {L : ℝ} (hL : 0 < L)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    (hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) (hΦm : AEMeasurable Φ)
    {B C : ℝ}
    (hperx_w : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
      (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C))
    (hperx_s : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
      (∫⁻ p : E3, ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2)))) :
    (MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
    ∧ (MeasureTheory.Integrable (fun p : E3 =>
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))) := by
  classical
  have hLnn : 0 ≤ L := hL.le
  have hinv : (0 : ℝ) ≤ (L ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hLnn 3)
  have hboxvol : (MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X (n + 1))) (Submission.BoseGases.abox (n + 1) L)
      = ENNReal.ofReal ((L ^ 3) ^ (n + 1)) :=
    Submission.BoseGases.abox_volume (n + 1) L hLnn
  -- ### measurability
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    Work.BoseFixB1B.aesm_tBamp_joint hL hχc hχ0 (hΦm.mono_measure Measure.restrict_le_self) i
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    hjoint.norm.pow 2
  have hJsm : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 => ∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    h2.integral_prod_right'
  have hslice : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X (n + 1) =>
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)) :=
    h2.prodMk_left
  have hmeas_px : AEMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        ENNReal.ofReal (‖q.1‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((by fun_prop : Continuous (fun q : E3 × Submission.BoseGases.X (n + 1) =>
          ‖q.1‖ ^ 2)).aestronglyMeasurable).mul h2).aemeasurable
  have hmeas_px2 : AEMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable h2.aemeasurable
  -- ### the a.e. replacement of the real `x`-integral by its `lintegral`
  have hJbound : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
        ≤ ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
            ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
    filter_upwards [hslice] with p hp
    have h0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)]
        (fun x : Submission.BoseGases.X (n + 1) =>
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) :=
      Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    have hconv := MeasureTheory.integral_eq_lintegral_of_nonneg_ae h0 hp
    rw [hconv]
    exact ENNReal.ofReal_toReal_le
  -- ### the two fibre bounds (pointwise in `x`, hypotheses of this lemma)
  have hperx_w' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)),
      (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) L)]
    exact Filter.Eventually.of_forall (fun x hx => hperx_w x hx)
  have hperx_s' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)),
      (∫⁻ p : E3, ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) L)]
    exact Filter.Eventually.of_forall (fun x hx => hperx_s x hx)
  -- ### the `p`- and `x`-integrals exchanged
  have hswap_w : (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
        ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
        ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) :=
    MeasureTheory.lintegral_lintegral_swap hmeas_px
  have hswap_s : (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
        ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
        ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) :=
    MeasureTheory.lintegral_lintegral_swap hmeas_px2
  -- ### the weighted estimate
  have hweighted : (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))) < ⊤ := by
    have hbound : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
        ENNReal.ofReal (‖p‖ ^ 2 * ((L ^ 3)⁻¹ *
            (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
          ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
      filter_upwards [hJbound] with p hp
      calc ENNReal.ofReal (‖p‖ ^ 2 * ((L ^ 3)⁻¹ *
              (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
          = ENNReal.ofReal (‖p‖ ^ 2) * (ENNReal.ofReal ((L ^ 3)⁻¹) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
            rw [ENNReal.ofReal_mul (sq_nonneg (‖p‖)), ENNReal.ofReal_mul hinv]
        _ = ENNReal.ofReal ((L ^ 3)⁻¹) * (ENNReal.ofReal (‖p‖ ^ 2) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by ring
        _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) * (ENNReal.ofReal (‖p‖ ^ 2) *
              (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
                ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))) :=
            mul_le_mul_right (mul_le_mul_right hp _) _
        _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
              (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
                ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
            congr 1
            rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall
              (fun x => ENNReal.ofReal_mul (sq_nonneg (‖p‖))))]
            exact (MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (‖p‖ ^ 2))
              (fun x : Submission.BoseGases.X (n + 1) =>
                ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
              ENNReal.ofReal_ne_top).symm
    have hconst : (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
          ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) *
            ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
      calc (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
            ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          ≤ ∫⁻ _x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) :=
            MeasureTheory.lintegral_mono_ae hperx_w'
        _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, hboxvol]
    calc (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))))
        ≤ ∫⁻ p : E3, ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_mono_ae hbound
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
          rw [hswap_w]
      _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1))) := mul_le_mul_right hconst _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- ### the unweighted estimate
  have hunweighted : (∫⁻ p : E3, ENNReal.ofReal
        ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))) < ⊤ := by
    have hbound : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
        ENNReal.ofReal ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
      filter_upwards [hJbound] with p hp
      calc ENNReal.ofReal ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          = ENNReal.ofReal ((L ^ 3)⁻¹) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
            rw [ENNReal.ofReal_mul hinv]
        _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
              (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
                ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
            mul_le_mul_right hp _
    have hconst : (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
          ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) *
            ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
      calc (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
            ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          ≤ ∫⁻ _x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) :=
            MeasureTheory.lintegral_mono_ae hperx_s'
        _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, hboxvol]
    calc (∫⁻ p : E3, ENNReal.ofReal ((L ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
        ≤ ∫⁻ p : E3, ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_mono_ae hbound
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
          rw [hswap_s]
      _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1))) := mul_le_mul_right hconst _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- ### conclusion
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hfun : (fun p : E3 => ‖p‖ ^ 2 * ((L ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
        = fun p : E3 => (‖p‖ ^ 2 * (L ^ 3)⁻¹) *
            (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
      funext p; ring
    rw [hfun]
    exact (by fun_prop : Continuous (fun p : E3 => ‖p‖ ^ 2 * (L ^ 3)⁻¹)).aestronglyMeasurable.mul
      hJsm
  · refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun p => ?_))) hweighted
    exact Real.enorm_eq_ofReal (mul_nonneg (sq_nonneg _)
      (mul_nonneg hinv (MeasureTheory.integral_nonneg (fun x => sq_nonneg _))))
  · have hfun : (fun p : E3 => (L ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        = fun p : E3 => (L ^ 3)⁻¹ *
            (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := rfl
    rw [hfun]
    exact (continuous_const : Continuous (fun _p : E3 => (L ^ 3)⁻¹)).aestronglyMeasurable.mul hJsm
  · refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun p => ?_))) hunweighted
    exact Real.enorm_eq_ofReal (mul_nonneg hinv
      (MeasureTheory.integral_nonneg (fun x => sq_nonneg _)))

/-- **Integrability of the windowed amplitude forms** for a state that is a.e. measurable and
bounded on the box, with `C³` window and `C³` windowed slot fibres. -/
theorem cutAmplitudeIntegrableThree {n : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ContDiff ℝ 3 χ) (hχcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L)
    {Ψ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1))
    (hΦm : AEMeasurable (Work.SmallBoxTBWord.boxQ volA A i Ψ))
    {B : ℝ} (hB : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      |Work.SmallBoxTBWord.boxQ volA A i Ψ x| ≤ B)
    (hfib : ∀ x ∈ Submission.BoseGases.abox (n+1) L, ContDiff ℝ 3
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z)))
    {C : ℝ} (hC : 0 ≤ C)
    (hdir : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      (∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        χ y * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i y))
          z (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) :
    (MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2)))
    ∧ (MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2))) := by
  classical
  have hχc : Continuous χ := hχ.continuous
  have hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0 := by
    intro z hz
    by_contra h
    exact hz (htsupp (subset_tsupport χ h))
  -- the two per-fibre `lintegral` bounds, at `C³` regularity
  have hperx_w : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
      (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
    intro x hx
    have hu : ContDiff ℝ 1 (fun z : E3 =>
        χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z)) :=
      (hfib x hx).of_le (by norm_num)
    have hcs : HasCompactSupport (fun z : E3 =>
        χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z)) :=
      hχcs.mul_right (f' := fun z => Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z))
    have hcongr : (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2))
        = ∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT
            (fun z : E3 => ((χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ
              (Function.update x i z) : ℝ) : ℂ)) p‖ ^ 2) := by
      refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Work.BoseFixB1B.tBamp_eq_kinFT_update χ (Work.SmallBoxTBWord.boxQ volA A i Ψ)
        i p x]
    rw [hcongr]
    exact kinFTEnergyLintegralOne
      (u := fun z : E3 => χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z))
      hu hcs (C := C) (hdir x hx)
  have hperx_s : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
      (∫⁻ p : E3, ENNReal.ofReal
          (‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) := by
    intro x hx
    have hu : ContDiff ℝ 1 (fun z : E3 =>
        χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z)) :=
      (hfib x hx).of_le (by norm_num)
    have hcs : HasCompactSupport (fun z : E3 =>
        χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z)) :=
      hχcs.mul_right (f' := fun z => Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z))
    have hcongr : (∫⁻ p : E3, ENNReal.ofReal
          (‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2))
        = ∫⁻ p : E3, ENNReal.ofReal (‖Submission.BoseGases.kinFT
            (fun z : E3 => ((χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ
              (Function.update x i z) : ℝ) : ℂ)) p‖ ^ 2) := by
      refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Work.BoseFixB1B.tBamp_eq_kinFT_update χ (Work.SmallBoxTBWord.boxQ volA A i Ψ)
        i p x]
    rw [hcongr]
    exact kinFTSqLintegralOne
      (u := fun z : E3 => χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z))
      hu hcs (C := B ^ 2 * (∫ z : E3, χ z ^ 2))
      (Work.BoseFixB1B.fibre_sq_integral_le hχc hχcs hχ0 i hB x hx)
  exact cutAmplitudeIntegrableThree_aux (B := B) (C := C) hL hχc hχ0 i hΦm hperx_w hperx_s

end Work.BoseB1Cube.PortSmallB
