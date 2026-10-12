import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.integrable_tBdiagFibreJoint_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.integrable_winFibreJoint`

**(R3) joint `(p,y)`-integrability of the windowed fibre integrand of the slot word.**

The *joint* `(p, y)`-integrand of the windowed kinetic fibre form of the slot word is

    q ↦ ∑_{j : Fin |S|} fsKinCoeff c ‖q.1‖ ·
            ((L³)⁻¹ · ∫_{z ∈ abox |S| L} ‖tBamp χ q.1 (Q_{B,j}(fibre of the slot piece at q.2)) j z‖²),

and the claim is that it is Bochner integrable for the product of Lebesgue measure on the sliding
centre `p ∈ ℝ³` with Lebesgue measure on the outside configurations `y`, restricted to the outside
set `slotOutside L (dlBox L d u) S`.

## The argument

`hdec` assumes precisely that the amplitude of every fibre slot is dominated by `C·(1+‖p‖)⁻³`
uniformly in `j`, in the outside configuration `y ∈ slotOutside` and in the box configuration
`ζ ∈ abox |S| L`.

1. **Pointwise bound.**  On the (finite-measure) box `abox |S| L` the squared amplitude is
   dominated by the constant `(C/(1+‖p‖)³)²`, so each slot integral is at most
   `(C/(1+‖p‖)³)² · |abox |S| L|` (`setIntegral_normSq_le`).  Every summand is nonnegative
   (`fsKinCoeff c = [·−c]₊² ≥ 0`, `(L³)⁻¹ > 0` and the integral of a square), so the triangle
   inequality gives

   `‖∑_j …‖ ≤ (|S| · ((L³)⁻¹·|abox|S|L|)) · (fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²)`.

2. **The dominating function is integrable.**  `p ↦ fsKinCoeff c ‖p‖·(C/(1+‖p‖)³)²` is integrable on
   `ℝ³` (`Work.SlotWord.integrable_fsKinCoeff_decayLeb`), and the outside factor carries the
   *finite* measure `volume ↾ slotOutside` (`Work.SlotWord.volume_slotOutside_lt_top`), so
   `Integrable.comp_fst` makes `M·g(q.1)` integrable for the product measure.

3. **Joint a.e.-strong measurability.**  The windowed amplitude of the fibre
   `(q, z) ↦ tBamp χ q.1 (Q_{B,j}(slotFibreState S e (slotPiece · S Φ) q.2)) j z` is measurable for
   a *measurable* window `χ` (the `χ`-factor enters only through
   `Complex.continuous_ofReal.measurable.comp (hχm.comp measurable_snd)`; everything else is the
   measurable reassembly `measurable_slotFibreState_pair` / `measurable_boxQInd_fibre` plus the two
   parametric Bochner integrals), the `z`-integral is again strongly measurable
   (`StronglyMeasurable.integral_prod_right'`), and the finite sum of the slot summands —
   `fsKinCoeff c ‖·‖` is continuous — is strongly measurable.

`Integrable.mono'` then closes: a.e. (w.r.t. `volume ↾ slotOutside`, hence a.e. for the product
measure) the outside configuration lies in `slotOutside`, where the pointwise bound of step 1
applies.
-/

namespace Work.BoseB1Cube

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. A bounded squared norm on a finite box -/

/-- **A bounded squared norm on a finite box.**  If `‖f z‖ ≤ K` for all `z` in a measurable set `s`
of finite measure, then the integral of the squared norm of `f` over `s` is at most `K ^ 2` times the
volume of `s`. -/
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

/-! ## 2. Joint measurability at a general measurable window -/

/-- **Joint measurability of the windowed amplitude of the fibre** at an arbitrary *measurable*
window `χ`.  This is the general-window version of `Work.SlotWord.measurable_tBamp_fibre` (which
hard-wires the continuous window `chiB L d u`) and of
`Work.BoseFixB1.measurable_tBamp_boxQInd_pair` (which assumes `Continuous χ` and a fixed state). -/
private theorem measurable_tBamp_fibre_gen (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card) (j : Fin S.card)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ)
    {χ : ℝ³ → ℝ} (hχm : Measurable χ) :
    Measurable (fun p : (ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
        Submission.BoseGases.X S.card =>
      Work.SmallBoxTBWord.tBamp χ p.1.1
        (Work.UBBInputs8.boxQInd volA A j (Work.PerSector.slotFibreState S e Φ p.1.2)) j p.2) := by
  classical
  have hboxQ := Work.SlotWord.measurable_boxQInd_fibre volA A hA S e j hΦ
  -- joint measurability of the amplitude integrand
  have hupd2 : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ => (q.1.2, q.2)) :=
    Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd
  have hupd : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ => Function.update q.1.2 j q.2) :=
    (measurable_update' (X := fun _ : Fin S.card => ℝ³) (a := j)).comp hupd2
  have hboxQw : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ =>
      Work.UBBInputs8.boxQInd volA A j
        (Work.PerSector.slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2)) :=
    hboxQ.comp (Measurable.prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst)) hupd)
  have hinner : Continuous (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ => (inner ℝ q.1.1.1 q.2 : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Continuous.inner (continuous_fst.comp (continuous_fst.comp continuous_fst)) continuous_snd)
  have h1 : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ => (χ q.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hχm.comp measurable_snd)
  have h2 : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner).neg)).measurable
  have h3 : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ =>
      ((Work.UBBInputs8.boxQInd volA A j (Work.PerSector.slotFibreState S e Φ q.1.1.2)
        (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hboxQw
  have hJ : Measurable (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) ×
      Submission.BoseGases.X S.card) × ℝ³ =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ))) *
        ((Work.UBBInputs8.boxQInd volA A j (Work.PerSector.slotFibreState S e Φ q.1.1.2)
          (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    (h1.mul h2).mul h3
  have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  convert hSM.measurable using 1
  funext p
  simp only [Work.SmallBoxTBWord.tBamp]

/-! ## 3. The joint integrand is a.e.-strongly-measurable -/

/-- The joint `(p,y)`-integrand of the windowed fibre form is a.e.-strongly-measurable for the
product of Lebesgue measure on the centre and (the restriction of) Lebesgue measure on the outside
configurations, for every measurable window `χ` and every measurable state `Φ`. -/
private theorem aestronglyMeasurable_winFibreJoint (L d c : ℝ)
    (u : ℝ³) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {χ : ℝ³ → ℝ} (hχm : Measurable χ) :
    AEStronglyMeasurable
      (fun q : ℝ³ × (Work.PerSector.SlotOut N S → ℝ³) =>
        ∑ j : Fin S.card, Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) j
                (Work.PerSector.slotFibreState S e
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) j z‖ ^ 2))
      ((volume : Measure ℝ³).prod
        ((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hΨ : Measurable (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) :=
    Work.PerSector.slotPiece_measurable _ hA S hΦm
  -- the box amplitude energy of the fibre is strongly measurable in `(p, y)`
  have hbox : ∀ i : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (Work.PerSector.SlotOut N S → ℝ³) =>
        ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) i z‖ ^ 2) := by
    intro i
    have hamp := measurable_tBamp_fibre_gen (Work.SmallBoxSliding.boxMass L d u)
      (Submission.BoseGases.dlBox L d u) hA S e i hΨ hχm
    exact (hamp.norm.pow_const 2).stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card L))
  -- the kinetic symbol
  have hkin : StronglyMeasurable
      (fun q : ℝ³ × (Work.PerSector.SlotOut N S → ℝ³) =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖) := by
    have hcf : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
    exact (hcf.comp continuous_fst.norm).stronglyMeasurable
  -- the joint `(p, y)`-integrand of the `i`-th summand
  have hjoint : ∀ i : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (Work.PerSector.SlotOut N S → ℝ³) =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((L ^ 3)⁻¹ *
          ∫ z in Submission.BoseGases.abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i
                (Work.PerSector.slotFibreState S e
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) i z‖ ^ 2)) :=
    fun i => hkin.mul ((hbox i).const_mul _)
  -- the sum over the fibre slots
  have hsum : StronglyMeasurable
      (∑ i : Fin S.card, (fun q : ℝ³ × (Work.PerSector.SlotOut N S → ℝ³) =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((L ^ 3)⁻¹ *
          ∫ z in Submission.BoseGases.abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i
                (Work.PerSector.slotFibreState S e
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) i z‖ ^ 2))) :=
    Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hjoint i)
  convert hsum.aestronglyMeasurable using 1
  funext q
  simp only [Finset.sum_apply]

/-! ## 4. The pointwise `(p,y)`-bound on the joint integrand -/

/-- The **pointwise bound on the joint windowed fibre integrand**: if the amplitude of every fibre
slot decays like `C·(1+‖p‖)⁻³` uniformly on `slotOutside × abox`, then the joint integrand is
bounded by `(|S|·(L³)⁻¹·|abox |S| L|)` times `fsKinCoeff c ‖p‖·(C/(1+‖p‖)³)²`. -/
private theorem norm_winFibreJoint_le_of_decay (L d c : ℝ) (hL : 0 < L)
    (u : ℝ³) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) {χ : ℝ³ → ℝ} {C : ℝ}
    (hdec : ∀ (j : Fin S.card) (p : ℝ³) (y : Work.PerSector.SlotOut N S → ℝ³),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3)
    (p : ℝ³) {y : Work.PerSector.SlotOut N S → ℝ³}
    (hy : y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S) :
    ‖∑ j : Fin S.card, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) j
                (Work.PerSector.slotFibreState S e
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2)‖
      ≤ ((S.card : ℝ) * ((L ^ 3)⁻¹ *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L)))
          * (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by
  have hL3 : 0 < (L ^ 3)⁻¹ := by rw [inv_pos]; positivity
  have hF0 : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ :=
    Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
  haveI hboxFin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card L)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    infer_instance
  -- the pointwise bound on one summand
  have hterm : ∀ j : Fin S.card,
      ‖Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2)‖
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by
    intro j
    have hEj : ∫ z in Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) j
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2
        ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 *
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
            (Submission.BoseGases.abox S.card L) :=
      setIntegral_normSq_le (Submission.BoseGases.abox_measurable S.card L)
        (fun z hz => hdec j p y hy z hz)
    have hE0 : 0 ≤ ∫ z in Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) j
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2 :=
      integral_nonneg (fun z => sq_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg hF0 (mul_nonneg hL3.le hE0))]
    have h1 : Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2)
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEj hL3.le) hF0
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) j
                (Work.PerSector.slotFibreState S e
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2)
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L))) := h1
      _ = (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring
  -- triangle inequality for the finite slot sum
  calc ‖∑ j : Fin S.card, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2)‖
      ≤ ∑ j : Fin S.card, ‖Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z‖ ^ 2)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin S.card,
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = (S.card : ℝ) *
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    _ = ((S.card : ℝ) * ((L ^ 3)⁻¹ *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L)))
          * (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring

/-! ## 5. The target -/

theorem integrable_winFibreJoint {N : ℕ} (L d c : ℝ) (hL : 0 < L) (hd : 0 < d)
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
      (fun q : EuclideanSpace ℝ (Fin 3) ×
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        ∑ j : Fin S.card, Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((L ^ 3)⁻¹ * ∫ z in Submission.BoseGases.abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) j
                (Work.PerSector.slotFibreState S e
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) j z‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) := by
  obtain ⟨C, _hC0, hdec⟩ := hdec
  set s : Set (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :=
    Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S with hs
  have hsmeas : MeasurableSet s :=
    Work.SlotWord.measurableSet_slotOutside L
      (Work.SmallBoxSliding.measurableSet_dlBox L d u) S
  haveI hνfin : IsFiniteMeasure
      ((MeasureTheory.volume :
          MeasureTheory.Measure (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        s) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
        exact Work.SlotWord.volume_slotOutside_lt_top L hL.le
          (Submission.BoseGases.dlBox L d u) S⟩
  -- the dominating profile is integrable on `ℝ³`
  have hG : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) :=
    Work.SlotWord.integrable_fsKinCoeff_decayLeb c C
  have hdom : Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) ×
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        ((S.card : ℝ) * ((L ^ 3)⁻¹ *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L)))
          * (Submission.BoseGases.fsKinCoeff c ‖q.1‖ * (C / (1 + ‖q.1‖) ^ 3) ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) :=
    (hG.const_mul ((S.card : ℝ) * ((L ^ 3)⁻¹ *
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
          (Submission.BoseGases.abox S.card L)))).comp_fst _
  refine hdom.mono' (aestronglyMeasurable_winFibreJoint L d c u S hΦm e hχm) ?_
  have hae : ∀ᵐ q ∂((MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
      ((MeasureTheory.volume :
          MeasureTheory.Measure (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))),
      q.2 ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (hsmeas.preimage measurable_snd)]
    filter_upwards with a
    exact MeasureTheory.ae_restrict_mem hsmeas
  filter_upwards [hae] with q hq
  exact norm_winFibreJoint_le_of_decay L d c hL u S e hdec q.1 hq

end

end Work.BoseB1Cube
