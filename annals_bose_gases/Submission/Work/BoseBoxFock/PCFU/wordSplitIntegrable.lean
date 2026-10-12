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

/-!
# `Work.BoseBoxFock.PCFU.wordSplitIntegrable`

Integrability of the word integrand of the `d = 0` word split (`PCFU/wordSplitDefs.lean`)

    `wordB v h fc κ ℓ i j Θ y
       = lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Θ)) y · wLoc ℓ (g₀ v h) 0 (y i) (y j)`,

for a state `Θ` which is only assumed **measurable and globally bounded** by `Cθ ≥ 0`.

Every ingredient is a product of the low-slot factor `A` with the *windowed pair kernel*
`p ↦ χ_ℓ(p.1)·wScaled ℓ (g₀ v h)(p.1 − p.2)·χ_ℓ(p.2)`:

* `A` is measurable and bounded by a constant `D` — this is
  `lowSlot_aQ_aP_measurable_bounded` (no continuity of `Θ` is available);
* the windowed pair kernel is `L¹` for `volume × volume` — this is `chiW1_integrable`, whose
  analytic content is the exact cancellation `χ_ℓ ⋆ χ_ℓ = ℓ³·convScale ℓ`, so that only the
  *local* integrability of `g₀ = v(1−ω)` (the `rhs_integrable` field of `ScatSol v`) and the
  support of the bump are used, **not** any support or size bound on `v`;
* its pullback to the box along the two distinct slots `i ≠ j` is `L¹(abox n ℓ)`
  (`integrableOn_pair_pullback_abox`, the finite-factor pair peel).

The four conjuncts are then: the product bound (conjunct 1), two applications of the `L¹`
statement for the slot mean `aP` (`aP_integrable_of_integrable`), and the transversal
integrability at fixed `x`, where both slots of `wordB` are frozen to `p.1` and `p.2`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem wordSplitIntegrable {n : ℕ} {i j : Fin n} (hij : i ≠ j)
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
  -- (0) the low-slot factor `A = lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Θ))` is measurable and
  -- uniformly bounded by `D ≥ 0` on all of `X n` (in particular on the box)
  obtain ⟨hAmeas, D, hD0, hAbnd⟩ :=
    lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := 0) (ℓ := ℓ) (κ := κ) (Cθ := Cθ)
      (i := i) (j := j) hℓ hκ hCθ hΘm hΘb
  -- (1) the windowed pair kernel `wPair ℓ (g₀ v h)` is `L¹` on `acube ℓ × acube ℓ`
  have hKpair : MeasureTheory.Integrable
      (fun p : E3 × E3 => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
    -- restrict the global `L¹` statement of `chiW1_integrable` to the product of the two cubes
    have h0 := (Work.BoseBoxFock.PCFU.chiW1_integrable h hℓ).mono_measure
      (Measure.restrict_le_self (μ := (MeasureTheory.volume : MeasureTheory.Measure E3).prod
          (MeasureTheory.volume : MeasureTheory.Measure E3))
        (s := Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
    rw [← Measure.prod_restrict (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (s := Submission.BoseGases.acube ℓ) (t := Submission.BoseGases.acube ℓ)] at h0
    refine h0.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Submission.BoseGases.wPair, Submission.BoseGases.wScaled, Work.BoseFixR.W1fun]
  -- (2) the pointwise product decomposition of `wordB`: the `wLoc` factor is exactly
  -- `χ_ℓ(y_i)·wScaled ℓ (g₀ v h)(y_i − y_j)·χ_ℓ(y_j) = wPair ℓ (g₀ v h) (y_i) (y_j)`
  have hpt : ∀ y : Submission.BoseGases.X n,
      Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ y
        = Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) y
            * Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (y i) (y j) := by
    intro y
    simp only [Work.BoseBoxFock.PCFU.wordB, Submission.BoseGases.wLoc, Submission.BoseGases.wPair,
      Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]
  -- (3) the pullback of the pair kernel along the two distinct slots `i ≠ j` is `L¹` on the box
  have hKbox : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) (x i) (x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume :=
    Work.BoseBoxFock.PCFU.integrableOn_pair_pullback_abox hℓ hij hKpair
  -- conjunct 1: the product `wordB` is dominated by `D·|wPair|`
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
  -- conjuncts 2 and 3: the slot means `aP ℓ i`, `aP ℓ j` preserve `L¹` on the box
  have h2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ) x)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume :=
    (Work.BoseBoxFock.PCFU.aP_integrable_of_integrable (ℓ := ℓ) hℓ i h1).2
  have h3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)) x)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume :=
    (Work.BoseBoxFock.PCFU.aP_integrable_of_integrable (ℓ := ℓ) hℓ j h2).2
  refine ⟨h1, h2, h3, ?_⟩
  -- conjunct 4: at fixed `x`, the two slots of `wordB` are exactly `p.1` and `p.2`
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
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
    refine hKpair.bdd_mul (c := D)
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
