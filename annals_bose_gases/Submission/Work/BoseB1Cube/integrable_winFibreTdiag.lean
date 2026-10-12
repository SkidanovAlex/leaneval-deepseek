import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.integrable_winFibreTdiag`

Integrability of the `χ`-windowed spectral fibre form
`tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ (fsKinCoeff c) (fibre y)` against Lebesgue
measure restricted to the outside configurations `slotOutside L (dlBox L d u) S`.

This is the **variable-window** version of `Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay`
(which is the special case `χ = chiB L d u`, the concrete FS window).  Everything in that
development is *window-blind* except for two occurrences of `chiB`:

* the joint measurability of the windowed amplitude `Work.SlotWord.measurable_tBamp_fibre`, where
  `chiB` enters only through its continuity;
* the definition of `fibreAmpEnergy`, which is hard-wired to `chiB`.

Here we replace the first by measurability of the window (which is the hypothesis `hχm` of the
target) and the second by a local, `χ`-parametrised copy `fibreAmpEnergyGen`.  Nothing else changes:
the argument is

* `tBdiagFormInd` unfolds *definitionally* into
  `Σ_j (2π)⁻³ ∫_p fsKinCoeff c ‖p‖ · ((L³)⁻¹ ∫_{abox |S| L} ‖tBamp χ p (Q_{B,j} fibre_y) j ζ‖²)`;
* the decay hypothesis bounds the `z`-integrand pointwise by `(C/(1+‖p‖)³)²` on the box, hence
  (monotone integral, finite box measure) the inner `z`-integral by `(C/(1+‖p‖)³)² · V`;
* the `p`-integrand is therefore dominated by
  `((L³)⁻¹ V)·(fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²)`, and the profile
  `p ↦ fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²` is integrable (`Work.SlotWord.integrable_fsKinCoeff_decay`),
  giving the uniform bound `M = |S| · (2π)⁻³ · (L³)⁻¹ · V · P`;
* `slotOutside L B S` has finite volume and the fibre form is a.e.-strongly measurable, so
  `IntegrableOn.of_bound` closes.
-/

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

noncomputable section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8
open Work.SmallBoxSliding
open Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-- `fsKinCoeff c` is continuous. -/
private theorem continuous_fsKinCoeff_cube (c : ℝ) :
    Continuous (Submission.BoseGases.fsKinCoeff c) := by
  unfold Submission.BoseGases.fsKinCoeff
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-! ## 0. The window-parametrised fibre amplitude energy -/

/-- The `χ`-windowed amplitude energy of the `j`-th fibre slot.  This is
`Work.SlotWord.fibreAmpEnergy` with the concrete window `chiB L d u` replaced by an arbitrary
window `χ`. -/
noncomputable def fibreAmpEnergyGen (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (χ : ℝ³ → ℝ) (j : Fin S.card) (p : ℝ³)
    (y : SlotOut N S → ℝ³) : ℝ :=
  ∫ z in abox S.card L, ‖Work.SmallBoxTBWord.tBamp χ p
      (boxQInd (boxMass L d u) (dlBox L d u) j
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2

/-- The defining unfolding of the `χ`-windowed fibre form. -/
theorem tBdiagFormInd_fibre_eq_gen (L d c : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (χ : ℝ³ → ℝ) (y : SlotOut N S → ℝ³) :
    tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ (fsKinCoeff c)
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
      = ∑ j : Fin S.card,
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
            fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergyGen L d u S Φ e χ j p y) := by
  simp only [tBdiagFormInd, fibreAmpEnergyGen]

/-! ## 1. Joint measurability of the windowed fibre amplitude -/

theorem measurable_tBamp_fibre_gen {N : ℕ} (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) {χ : ℝ³ → ℝ} (hχ : Measurable χ) :
    Measurable (fun p : (ℝ³ × (SlotOut N S → ℝ³)) × X S.card =>
      Work.SmallBoxTBWord.tBamp χ p.1.1
        (boxQInd volA A j (slotFibreState S e Φ p.1.2)) j p.2) := by
  classical
  have hboxQ := Work.SlotWord.measurable_boxQInd_fibre volA A hA S e j hΦ
  -- joint measurability of the amplitude integrand
  have hupd2 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (q.1.2, q.2)) :=
    Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd
  have hupd : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      Function.update q.1.2 j q.2) :=
    (measurable_update' (X := fun _ : Fin S.card => ℝ³) (a := j)).comp hupd2
  have hboxQw : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      boxQInd volA A j (slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2)) :=
    hboxQ.comp (Measurable.prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst)) hupd)
  have hinner : Continuous (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (inner ℝ q.1.1.1 q.2 : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Continuous.inner (continuous_fst.comp (continuous_fst.comp continuous_fst)) continuous_snd)
  have h1 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (χ q.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hχ.comp measurable_snd)
  have h2 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner).neg)).measurable
  have h3 : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      ((boxQInd volA A j (slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hboxQw
  have hJ : Measurable (fun q : ((ℝ³ × (SlotOut N S → ℝ³)) × X S.card) × ℝ³ =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ))) *
        ((boxQInd volA A j (slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    (h1.mul h2).mul h3
  have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  convert hSM.measurable using 1
  funext p
  simp only [Work.SmallBoxTBWord.tBamp]

/-! ## 2. Strong measurability of the fibre amplitude energy -/

theorem stronglyMeasurable_fibreAmpEnergyGen {N : ℕ} (L d : ℝ) (u : ℝ³)
    (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : Measurable Φ)
    (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) {χ : ℝ³ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2) := by
  have hA : MeasurableSet (dlBox L d u) := measurableSet_dlBox L d u
  have hΨ : Measurable (slotPiece (dlBox L d u) S Φ) := slotPiece_measurable _ hA S hΦ
  have hamp := measurable_tBamp_fibre_gen (boxMass L d u) (dlBox L d u) hA S e j hΨ hχ
  have hnorm : Measurable (fun p : (ℝ³ × (SlotOut N S → ℝ³)) × X S.card =>
      ‖Work.SmallBoxTBWord.tBamp χ p.1.1
        (boxQInd (boxMass L d u) (dlBox L d u) j
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) p.1.2)) j p.2‖ ^ 2) :=
    hamp.norm.pow_const 2
  exact hnorm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (X S.card)).restrict (abox S.card L))

/-! ## 3. A.e.-strong measurability of the fibre form -/

theorem aestronglyMeasurable_fibre_tBdiagFormInd_gen {N : ℕ} (L d c : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχm : Measurable χ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) χ (Submission.BoseGases.fsKinCoeff c)
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) := by
  -- the box amplitude energy of the fibre, individually strongly measurable in `(p, y)`
  have hbox : ∀ j : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2) :=
    fun j => stronglyMeasurable_fibreAmpEnergyGen L d u S hΦm e j hχm
  -- the kinetic symbol
  have hkin : Measurable (fun q : ℝ³ × (SlotOut N S → ℝ³) => fsKinCoeff c ‖q.1‖) :=
    (continuous_fsKinCoeff_cube c).measurable.comp continuous_fst.norm.measurable
  -- the joint `(p, y)`-integrand of the `j`-th summand
  have hjoint : ∀ j : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => fsKinCoeff c ‖q.1‖ * ((L ^ 3)⁻¹ *
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2)) := by
    intro j
    exact hkin.stronglyMeasurable.mul ((hbox j).const_mul _)
  -- the Bochner partial integral over the momentum variable
  have hInt : ∀ j : Fin S.card, StronglyMeasurable
      (fun y : SlotOut N S → ℝ³ => ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2)) := by
    intro j
    exact (hjoint j).integral_prod_left' (μ := (volume : Measure ℝ³))
  -- the sum over the fibre slots
  have hSum : AEStronglyMeasurable
      (fun y : SlotOut N S → ℝ³ => ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
          ∫ z in abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (boxQInd (boxMass L d u) (dlBox L d u) j
                (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2))
      ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L (dlBox L d u) S)) := by
    have hsum : AEStronglyMeasurable
        (∑ j ∈ Finset.univ, fun y : SlotOut N S → ℝ³ => ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
            ∫ z in abox S.card L,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (boxQInd (boxMass L d u) (dlBox L d u) j
                  (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2))
        ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L (dlBox L d u) S)) :=
      Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => (hInt j).aestronglyMeasurable.const_mul _)
    convert hsum using 1
    funext y
    simp only [Finset.sum_apply]
  refine hSum.congr ?_
  filter_upwards with y
  simp only [tBdiagFormInd]

/-! ## 4. The decay bound on the box amplitude energy -/

/-- **A bounded squared norm on a finite box.**  (Local copy of the private helper of
`Work.SlotWord.fibreAmpEnergy_le_of_decay`, which is not exported.) -/
private lemma setIntegral_normSq_le' {k : ℕ} {s : Set (Submission.BoseGases.X k)}
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

theorem fibreAmpEnergyGen_le_of_decay {N : ℕ} (L d : ℝ) (hL : 0 < L)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ}
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) {χ : ℝ³ → ℝ} {C : ℝ}
    (hdec : ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3)
    (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
    {y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S) :
    fibreAmpEnergyGen L d u S Φ e χ j p y
      ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 *
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
            (Submission.BoseGases.abox S.card L) := by
  have hboxFin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card L)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    infer_instance
  rw [fibreAmpEnergyGen]
  refine setIntegral_normSq_le'
    (f := fun z => Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) j
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z)
    (Submission.BoseGases.abox_measurable S.card L) ?_
  intro z hz
  exact hdec j p y hy z hz

/-! ## 5. The target -/

theorem integrable_winFibreTdiag {N : ℕ} (L d c : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχm : Measurable χ)
    (hdec : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3) :
    MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) χ (Submission.BoseGases.fsKinCoeff c)
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)) := by
  obtain ⟨C, _hC0, hdec⟩ := hdec
  -- the fibre amplitude energy is nonnegative
  have hfibnn : ∀ (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³),
      0 ≤ fibreAmpEnergyGen L d u S Φ e χ j p y := by
    intro j p y
    unfold fibreAmpEnergyGen
    exact integral_nonneg (fun z => sq_nonneg _)
  -- the dominating decay profile is integrable
  have hG : Integrable (fun p : ℝ³ => fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) :=
    Work.SlotWord.integrable_fsKinCoeff_decay c C
  -- the box volume and the total `p`-mass
  set V : ℝ := (volume : Measure (X S.card)).real (abox S.card L) with hV
  set P : ℝ := ∫ p : ℝ³, fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2 with hP
  set M : ℝ := (S.card : ℝ) * (((2 * Real.pi) ^ 3)⁻¹ * ((L ^ 3)⁻¹ * (V * P))) with hM
  have hL3inv : (0 : ℝ) < (L ^ 3)⁻¹ := by positivity
  -- the pointwise decay bound on the fibre amplitude energy
  have hamp : ∀ (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³),
      y ∈ slotOutside L (dlBox L d u) S →
      fibreAmpEnergyGen L d u S Φ e χ j p y ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * V := by
    intro j p y hy
    rw [hV]
    exact fibreAmpEnergyGen_le_of_decay L d hL u S e hdec j p hy
  -- the `p`-integral is bounded, uniformly in the slot and the outside configuration
  have hkey : ∀ (j : Fin S.card) (y : SlotOut N S → ℝ³),
      y ∈ slotOutside L (dlBox L d u) S →
      (∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergyGen L d u S Φ e χ j p y))
        ≤ (L ^ 3)⁻¹ * (V * P) := by
    intro j y hy
    have hdom : Integrable (fun p : ℝ³ => ((L ^ 3)⁻¹ * V) *
        (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := hG.const_mul _
    have hle : (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * fibreAmpEnergyGen L d u S Φ e χ j p y))
        ≤ᵐ[volume] (fun p : ℝ³ => ((L ^ 3)⁻¹ * V) *
          (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := by
      filter_upwards with p
      have h1 := hamp j p y hy
      calc fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergyGen L d u S Φ e χ j p y)
          ≤ fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 * V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (fsKinCoeff_nonneg c ‖p‖)
            exact mul_le_mul_of_nonneg_left h1 hL3inv.le
        _ = ((L ^ 3)⁻¹ * V) * (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring
    have hmono := integral_mono_of_nonneg
      (μ := volume)
      (f := fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * fibreAmpEnergyGen L d u S Φ e χ j p y))
      (g := fun p : ℝ³ => ((L ^ 3)⁻¹ * V) *
        (fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2))
      (Filter.Eventually.of_forall (fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg hL3inv.le (hfibnn j p y)))) hdom hle
    rw [integral_const_mul, ← hP] at hmono
    exact le_trans hmono (le_of_eq (by ring))
  -- the uniform bound on the fibre form
  have hpoint : ∀ (y : SlotOut N S → ℝ³),
      y ∈ slotOutside L (dlBox L d u) S →
      ‖tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ (fsKinCoeff c)
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)‖ ≤ M := by
    intro y hy
    have hdef := tBdiagFormInd_fibre_eq_gen L d c u S Φ e χ y
    have hnn : (0 : ℝ) ≤ tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ
        (fsKinCoeff c) (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
      rw [hdef]
      refine Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) ?_)
      exact integral_nonneg (fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg hL3inv.le (hfibnn j p y)))
    rw [Real.norm_of_nonneg hnn, hdef]
    calc ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
            fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergyGen L d u S Φ e χ j p y)
        ≤ ∑ _j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ * ((L ^ 3)⁻¹ * (V * P)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hkey j y hy) (by positivity)
      _ = M := by
          rw [hM, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- assembly
  refine IntegrableOn.of_bound
    (volume_slotOutside_lt_top L hL.le (dlBox L d u) S)
    (aestronglyMeasurable_fibre_tBdiagFormInd_gen L d c u S hΦm e hχm) M ?_
  exact ae_restrict_of_forall_mem
    (measurableSet_slotOutside L (measurableSet_dlBox L d u) S) hpoint

end

end Work.BoseB1Cube
