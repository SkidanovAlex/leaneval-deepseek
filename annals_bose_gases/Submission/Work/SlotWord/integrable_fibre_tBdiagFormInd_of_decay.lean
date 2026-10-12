import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.aestronglyMeasurable_fibre_tBdiagFormInd
import Submission.Work.SlotWord.fibreAmpEnergy_le_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay`

**(R3) integrability of the spectral fibre form `tBdiagFormInd`.**

If the `p`-diagonal kinetic amplitude of the fibre `slotFibreState S e (slotPiece B S Φ) y` decays
like `C·(1+‖p‖)⁻³` uniformly in the outside configuration `y ∈ slotOutside L B S` and in the
box configuration `ζ ∈ abox |S| L` (`B = dlBox L d u`), then the outside-configuration function

  `y ↦ tBdiagFormInd L B (boxMass L d u) (chiB L d u) (fsKinCoeff c) (fibre y)`

is Bochner-integrable against the volume restricted to `slotOutside L B S`.

## The argument

Unfolding `tBdiagFormInd` (the definitional identity `tBdiagFormInd_fibre_eq`), the function is

  `Σ_{j : Fin |S|} (2π)⁻³ ∫_p fsKinCoeff c ‖p‖ · ((L³)⁻¹ ∫_{abox |S| L} ‖tBamp χ_B p (Q_{B,j} fibre_y) j ζ‖²)`,

so it suffices to bound, uniformly in `y ∈ slotOutside`, the `p`-integrand

  `fsKinCoeff c ‖p‖ · (L³)⁻¹ · fibreAmpEnergy j p y`.

Two independent inputs:

* **the pointwise decay bound** (`Work.SlotWord.fibreAmpEnergy_le_of_decay`): the amplitude bound
  `‖…‖ ≤ C/(1+‖p‖)³` on the *whole* box `abox |S| L` gives
  `fibreAmpEnergy j p y ≤ (C/(1+‖p‖)³)² · |abox |S| L|`, i.e. `≤ D·V` with `D` the pointwise
  constant and `V` the (finite) box volume, *uniformly in `j, p, y`*;
* **the `p`-integrability of the decay profile** (`Work.SlotWord.integrable_fsKinCoeff_decay`):
  `fsKinCoeff c ‖p‖ ≤ (1+|c|)²(1+‖p‖)²` while `(C/(1+‖p‖)³)² = C²(1+‖p‖)⁻⁶`, so the dominating
  profile is `C²(1+|c|)²(1+‖p‖)⁻⁴`, integrable on `ℝ³` because `4 > 3`.

Hence `∫_p fsKinCoeff c ‖p‖ · ((L³)⁻¹ · fibreAmpEnergy j p y) ≤ (L³)⁻¹·V·∫_p G` with
`G := fsKinCoeff c ‖·‖ · (C/(1+‖·‖)³)²`, uniformly in `j, y`, and the whole sum is bounded by the
constant

  `M := |S| · (2π)⁻³ · (L³)⁻¹ · V · ∫_p G`.

The outside-configuration set `slotOutside L B S` has finite volume
(`Work.SlotWord.volume_slotOutside_lt_top`) and the fibre form is a.e.-strongly measurable
(`Work.SlotWord.aestronglyMeasurable_fibre_tBdiagFormInd`), so `IntegrableOn.of_bound` closes.
-/

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

noncomputable section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases BoseGases Work.PerSector Work.UBBInputs8 Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The `p`-space decay profile is integrable -/

/-- **The `fsKinCoeff`-weighted decay profile is integrable on `ℝ³`.**  For every `c, C : ℝ`,

    `p ↦ fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²`

is Bochner-integrable.  The bound `fsKinCoeff c r = (max (r−c) 0)² ≤ (1+|c|)²(1+r)²` turns the
profile into `C²(1+|c|)²(1+‖p‖)⁻⁴`, and `(1+‖·‖)⁻⁴` is integrable in dimension `3`. -/
theorem integrable_fsKinCoeff_decay (c C : ℝ) :
    Integrable (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (C / (1 + ‖p‖) ^ 3) ^ 2) := by
  have hbase : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (r := (4 : ℝ)) (by
      rw [finrank_euclideanSpace_fin]; norm_num)
  have hg : Integrable (fun p : ℝ³ => (C ^ 2 * (1 + |c|) ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    hbase.const_mul _
  refine hg.mono' ?_ ?_
  · have h1 : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp
        continuous_norm
    have h2 : Continuous (fun p : ℝ³ => (C / (1 + ‖p‖) ^ 3) ^ 2) := by
      refine ((continuous_const.div ((continuous_const.add continuous_norm).pow 3) ?_)).pow 2
      intro p
      exact pow_ne_zero 3 (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖p‖))
    exact (h1.mul h2).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _))]
    have hden : (0 : ℝ) < 1 + ‖p‖ := by positivity
    have hmax : (0 : ℝ) ≤ max (‖p‖ - c) 0 := le_max_right _ _
    have hle : max (‖p‖ - c) 0 ≤ (1 + |c|) * (1 + ‖p‖) := by
      have h2 : max (‖p‖ - c) 0 ≤ ‖p‖ + |c| := by
        refine max_le (by linarith [neg_le_abs c]) (by positivity)
      have h3 : ‖p‖ + |c| ≤ (1 + |c|) * (1 + ‖p‖) := by
        nlinarith [norm_nonneg p, abs_nonneg c, mul_nonneg (abs_nonneg c) (norm_nonneg p)]
      linarith
    have hsq : (max (‖p‖ - c) 0) ^ 2 ≤ ((1 + |c|) * (1 + ‖p‖)) ^ 2 :=
      pow_le_pow_left₀ hmax hle 2
    have hrpow : (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hden.le,
        Real.rpow_natCast]
    unfold Submission.BoseGases.fsKinCoeff
    rw [hrpow]
    calc (max (‖p‖ - c) 0) ^ 2 * (C / (1 + ‖p‖) ^ 3) ^ 2
        ≤ ((1 + |c|) * (1 + ‖p‖)) ^ 2 * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (C ^ 2 * (1 + |c|) ^ 2) * ((1 + ‖p‖) ^ 4)⁻¹ := by field_simp

/-! ## 2. The target -/

theorem integrable_fibre_tBdiagFormInd_of_decay {N : ℕ} (L d c : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    (hdec : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3) :
    MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c)
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) := by
  obtain ⟨C, _hC0, hdec⟩ := hdec
  -- the fibre amplitude energy is nonnegative
  have hfibnn : ∀ (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³),
      0 ≤ fibreAmpEnergy L d u S Φ e j p y := by
    intro j p y
    unfold fibreAmpEnergy
    exact integral_nonneg (fun z => sq_nonneg _)
  -- the dominating decay profile is integrable
  have hG : Integrable (fun p : ℝ³ => fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) :=
    integrable_fsKinCoeff_decay c C
  -- the box volume and the total `p`-mass
  set V : ℝ := (volume : Measure (X S.card)).real (abox S.card L) with hV
  set P : ℝ := ∫ p : ℝ³, fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2 with hP
  set M : ℝ := (S.card : ℝ) * (((2 * Real.pi) ^ 3)⁻¹ * ((L ^ 3)⁻¹ * (V * P))) with hM
  have hL3inv : (0 : ℝ) < (L ^ 3)⁻¹ := by positivity
  -- the pointwise decay bound on the fibre amplitude energy
  have hamp : ∀ (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³),
      y ∈ slotOutside L (dlBox L d u) S →
      fibreAmpEnergy L d u S Φ e j p y ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * V := by
    intro j p y hy
    rw [hV]
    exact fibreAmpEnergy_le_of_decay L d hL u S e hdec j p hy
  -- the `p`-integral is bounded, uniformly in the slot and the outside configuration
  have hkey : ∀ (j : Fin S.card) (y : SlotOut N S → ℝ³),
      y ∈ slotOutside L (dlBox L d u) S →
      (∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y))
        ≤ (L ^ 3)⁻¹ * (V * P) := by
    intro j y hy
    have hdom : Integrable (fun p : ℝ³ => ((L ^ 3)⁻¹ * V) *
        (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := hG.const_mul _
    have hle : (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y))
        ≤ᵐ[volume] (fun p : ℝ³ => ((L ^ 3)⁻¹ * V) *
          (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := by
      filter_upwards with p
      have h1 := hamp j p y hy
      calc fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y)
          ≤ fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 * V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (fsKinCoeff_nonneg c ‖p‖)
            exact mul_le_mul_of_nonneg_left h1 hL3inv.le
        _ = ((L ^ 3)⁻¹ * V) * (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring
    have hmono := integral_mono_of_nonneg
      (μ := volume)
      (f := fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y))
      (g := fun p : ℝ³ => ((L ^ 3)⁻¹ * V) *
        (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2))
      (Filter.Eventually.of_forall (fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg hL3inv.le (hfibnn j p y)))) hdom hle
    rw [integral_const_mul, ← hP] at hmono
    exact le_trans hmono (le_of_eq (by ring))
  -- the uniform bound on the fibre form
  have hpoint : ∀ (y : SlotOut N S → ℝ³),
      y ∈ slotOutside L (dlBox L d u) S →
      ‖tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) (fsKinCoeff c)
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)‖ ≤ M := by
    intro y hy
    have hdef : tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) (fsKinCoeff c)
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
        = ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
            fsKinCoeff c ‖p‖ *
              ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y) := rfl
    have hnn : (0 : ℝ) ≤ tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u)
        (fsKinCoeff c) (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
      rw [hdef]
      refine Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) ?_)
      exact integral_nonneg (fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg hL3inv.le (hfibnn j p y)))
    rw [Real.norm_of_nonneg hnn, hdef]
    calc ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
            fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y)
        ≤ ∑ _j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ * ((L ^ 3)⁻¹ * (V * P)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hkey j y hy) (by positivity)
      _ = M := by
          rw [hM, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- assembly
  refine IntegrableOn.of_bound
    (volume_slotOutside_lt_top L hL.le (dlBox L d u) S)
    (aestronglyMeasurable_fibre_tBdiagFormInd L d c u S hΦm e) M ?_
  exact ae_restrict_of_forall_mem
    (measurableSet_slotOutside L (measurableSet_dlBox L d u) S) hpoint

end

end Work.SlotWord
