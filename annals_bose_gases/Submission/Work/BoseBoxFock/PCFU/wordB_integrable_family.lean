import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.aP_integrable_of_integrable
import Submission.Work.BoseBoxFock.PCFU.integrableOn_pair_pullback_abox
import Submission.Work.BoseBoxFock.PCFU.lowSlot_aQ_aP_measurable_bounded
import Submission.Work.BoseBoxFock.PCFU.wordSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The windowed pair kernel `p ↦ wPair ℓ (g₀ v h) p.1 p.2` is integrable for the product of
the two restricted cube measures.  This is `chiW1_integrable` (integrability over
`volume × volume`) restricted to `acube ℓ ×ˢ acube ℓ`, with the definitions unfolded. -/
theorem integrable_wPair_kernel {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable
      (fun p : E3 × E3 => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
  have h0 := (Work.BoseBoxFock.PCFU.chiW1_integrable h hℓ).mono_measure
    (Measure.restrict_le_self (μ := (volume : Measure E3).prod (volume : Measure E3))
      (s := Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
  rw [← Measure.prod_restrict (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
    (s := Submission.BoseGases.acube ℓ) (t := Submission.BoseGases.acube ℓ)] at h0
  refine h0.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Submission.BoseGases.wPair, Submission.BoseGases.wScaled, Work.BoseFixR.W1fun]

theorem wordB_integrable_family {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut}
    {ℓ κ Cθ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∀ y, |Θ y| ≤ Cθ) (hCθ : 0 ≤ Cθ) :
    MeasureTheory.IntegrableOn (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)
        (Submission.BoseGases.abox n ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ) x)
        (Submission.BoseGases.abox n ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i
            (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)) x)
        (Submission.BoseGases.abox n ℓ) MeasureTheory.volume
      ∧ (∀ x : Submission.BoseGases.X n,
          MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
              (Function.update (Function.update x i p.1) j p.2))
          (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)))) := by
  -- the low-slot factor `A = lowSlot fc κ ℓ j (Q_j P_i Θ)` is measurable and bounded
  obtain ⟨hAmeas, D, _hD0, hAbnd⟩ :=
    lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := 0) (ℓ := ℓ) (κ := κ) (Cθ := Cθ)
      (i := i) (j := j) hℓ hκ hCθ hΘm hΘb
  -- the product decomposition `wordB = (low-slot factor) · (windowed pair kernel)`
  have hpt : ∀ y : Submission.BoseGases.X n,
      Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ y
        = Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) y
            * Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (y i) (y j) := by
    intro y
    simp only [Work.BoseBoxFock.PCFU.wordB, Submission.BoseGases.wLoc, Submission.BoseGases.wPair,
      Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]
  -- the windowed pair kernel in the two slots is `L¹` over the box
  have hKbox : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (x i) (x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume :=
    integrableOn_pair_pullback_abox hℓ hij (integrable_wPair_kernel h hℓ)
  -- (1) `wordB` itself
  have h1 : MeasureTheory.IntegrableOn (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
    show MeasureTheory.Integrable (fun y : Submission.BoseGases.X n =>
      Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))
    rw [funext hpt]
    refine MeasureTheory.Integrable.mono'
      (g := fun y : Submission.BoseGases.X n =>
        D * |Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (y i) (y j)|)
      (hKbox.integrable.abs.const_mul D) ?_ ?_
    · exact hAmeas.aestronglyMeasurable.mul hKbox.integrable.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hAbnd y) (abs_nonneg _)
  -- (2) and (3): the slot means
  have h2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ) x)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume :=
    (aP_integrable_of_integrable (ℓ := ℓ) hℓ i h1).2
  have h3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)) x)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume :=
    (aP_integrable_of_integrable (ℓ := ℓ) hℓ j h2).2
  refine ⟨h1, h2, h3, ?_⟩
  -- (4) the pointwise two-slot integrability
  intro x
  have hyi : ∀ p : E3 × E3, (Function.update (Function.update x i p.1) j p.2) i = p.1 := by
    intro p
    simp [hij]
  have hyj : ∀ p : E3 × E3, (Function.update (Function.update x i p.1) j p.2) j = p.2 := by
    intro p
    simp
  have hmain : MeasureTheory.Integrable
      (fun p : E3 × E3 =>
        Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
              (Function.update (Function.update x i p.1) j p.2)
            * Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
    refine (integrable_wPair_kernel h hℓ).bdd_mul (c := D)
      ((hAmeas.comp (by fun_prop : Measurable fun p : E3 × E3 =>
        Function.update (Function.update x i p.1) j p.2)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs]
    exact hAbnd _
  refine hmain.congr (Filter.Eventually.of_forall fun p => ?_)
  show Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update (Function.update x i p.1) j p.2)
      * Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) p.1 p.2
    = Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
        (Function.update (Function.update x i p.1) j p.2)
  rw [hpt (Function.update (Function.update x i p.1) j p.2), hyi p, hyj p]

end Work.BoseBoxFock.PCFU
