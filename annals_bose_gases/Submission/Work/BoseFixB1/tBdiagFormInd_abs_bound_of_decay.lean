import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
import Submission.Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.tBdiagFormInd_abs_bound_of_decay`

**The `p`-diagonal kinetic form is bounded uniformly in the sliding parameter `u` as soon as its
amplitude decays.**

`Work.UBBInputs8.tBdiagFormInd ℓ B |B| χ F Φ` is the `p`-diagonal form

  `Σ_i (2π)⁻³ ∫_p F ‖p‖ · ((ℓ³)⁻¹ ∫_{abox n ℓ} ‖tBamp χ_B p (Q_{B,i}Φ) i x‖²)`

of the small box `B = B(u)` (the FS-faithful, box-projected kinetic form).  If the windowed
amplitude of `Q_{B,i}Φ` decays like `C (1+‖p‖)⁻³` on the ambient box `abox n ℓ`, uniformly in the
sliding parameter `u` and in the index `i`, then the whole form is bounded by the `u`-independent
constant

  `K := n · (2π)⁻³ · (ℓ³)⁻¹ · |abox n ℓ| · ∫_p fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²`.

The argument has three parts, none of which uses any regularity of the state `Φ`:

* the amplitude energy of one slot is dominated by the square of the pointwise decay times the
  *finite* volume of the box (`setIntegral_normSq_le`);
* the resulting `p`-profile `fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²` is integrable on Euclidean 3-space
  (`Work.SlotWord.integrable_fsKinCoeff_decay`: `fsKinCoeff c r = [r−c]₊² ≤ (1+|c|)²(1+r)²` while
  `4 > 3`), so the `p`-integral of every slot is bounded by `(ℓ³)⁻¹|abox n ℓ|·∫_p G`;
* every summand of the slot sum is a square, so the absolute value is the value itself.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "R3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **A bounded squared norm on a finite box.**  If `‖f z‖ ≤ K` for all `z` in a measurable set
`s` of finite measure, then the integral of the squared norm of `f` over `s` is at most `K ^ 2`
times the volume of `s`.  (Copy of the private auxiliary lemma of
`Work.SlotWord.fibreAmpEnergy_le_of_decay`.) -/
private lemma setIntegral_normSq_le {k : ℕ} {s : Set (Submission.BoseGases.X k)}
    {E : Type*} [SeminormedAddCommGroup E]
    (hs : MeasurableSet s)
    [IsFiniteMeasure ((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s)]
    {f : Submission.BoseGases.X k → E} {K : ℝ}
    (hb : ∀ z ∈ s, ‖f z‖ ≤ K) :
    ∫ z in s, ‖f z‖ ^ 2
      ≤ K ^ 2 * (volume : MeasureTheory.Measure (Submission.BoseGases.X k)).real s := by
  have hK : Integrable (fun _ : Submission.BoseGases.X k => K ^ 2)
      ((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr inferInstance
  have hae : ∀ᵐ z ∂((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s),
      ‖f z‖ ^ 2 ≤ K ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => sq_nonneg (‖f z‖)) hK hae
  calc ∫ z in s, ‖f z‖ ^ 2
      = ∫ z, ‖f z‖ ^ 2
          ∂((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s) := rfl
    _ ≤ ∫ z, K ^ 2
          ∂((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s) := hmono
    _ = ∫ z in s, K ^ 2 := rfl
    _ = K ^ 2 * (volume : MeasureTheory.Measure (Submission.BoseGases.X k)).real s := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

theorem tBdiagFormInd_abs_bound_of_decay {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n),
      x ∈ Submission.BoseGases.abox n ℓ → ∀ (i : Fin n) (p : EuclideanSpace ℝ (Fin 3)),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3)
    (c : ℝ) :
    ∃ K : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3),
      |Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
        (Submission.BoseGases.fsKinCoeff c) Φ| ≤ K := by
  -- the dominating `p`-profile is integrable
  have hG : Integrable (fun p : R3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (C / (1 + ‖p‖) ^ 3) ^ 2) := Work.SlotWord.integrable_fsKinCoeff_decay c C
  set V : ℝ := (volume : Measure (Submission.BoseGases.X n)).real
    (Submission.BoseGases.abox n ℓ) with hV
  set P : ℝ := ∫ p : R3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
    (C / (1 + ‖p‖) ^ 3) ^ 2 with hP
  refine ⟨(n : ℝ) * ((2 * Real.pi) ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * (V * P)), ?_⟩
  intro u
  have hℓ3inv : (0 : ℝ) < (ℓ ^ 3)⁻¹ := by positivity
  haveI hboxFin : IsFiniteMeasure
      ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    infer_instance
  -- the amplitude energy of a single slot is controlled by the pointwise decay and the box volume
  have hamp : ∀ (i : Fin n) (p : R3),
      (∫ x in Submission.BoseGases.abox n ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
      ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * V := by
    intro i p
    rw [hV]
    refine setIntegral_normSq_le (Submission.BoseGases.abox_measurable n ℓ) ?_
    intro z hz
    exact hdec u z hz i p
  -- the `p`-integral of a single slot is bounded, uniformly in the slot index
  have hkey : ∀ i : Fin n,
      (∫ p : R3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2))
      ≤ (ℓ ^ 3)⁻¹ * (V * P) := by
    intro i
    have hdom : Integrable (fun p : R3 => ((ℓ ^ 3)⁻¹ * V) *
        (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) :=
      hG.const_mul _
    have hle : (fun p : R3 => Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2))
        ≤ᵐ[volume] (fun p : R3 => ((ℓ ^ 3)⁻¹ * V) *
          (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := by
      filter_upwards with p
      have h1 := hamp i p
      calc Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox n ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
          ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 * V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
            exact mul_le_mul_of_nonneg_left h1 hℓ3inv.le
        _ = ((ℓ ^ 3)⁻¹ * V) *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (f := fun p : R3 => Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2))
      (g := fun p : R3 => ((ℓ ^ 3)⁻¹ * V) *
        (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2))
      (Filter.Eventually.of_forall (fun p => mul_nonneg
        (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg hℓ3inv.le (integral_nonneg (fun z => sq_nonneg _))))) hdom hle
    rw [integral_const_mul, ← hP] at hmono
    exact le_trans hmono (le_of_eq (by ring))
  -- unfold the form into its slot sum
  have hdef : Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
      (Submission.BoseGases.fsKinCoeff c) Φ
      = ∑ i : Fin n, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : R3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2) := rfl
  have hnn : 0 ≤ Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
      (Submission.BoseGases.fsKinCoeff c) Φ := by
    rw [hdef]
    refine Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) ?_)
    exact integral_nonneg (fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
      (mul_nonneg hℓ3inv.le (integral_nonneg (fun z => sq_nonneg _))))
  rw [abs_of_nonneg hnn, hdef]
  calc ∑ i : Fin n, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : R3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)
      ≤ ∑ _i : Fin n, ((2 * Real.pi) ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * (V * P)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hkey i) (by positivity))
    _ = (n : ℝ) * ((2 * Real.pi) ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * (V * P)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Work.BoseFixB1
