import ChallengeDeps
import Submission.Work.BoseFixB1.q1CrossW1csLocalised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- **Integrability of the localised one-body fibre on the sliding box `B(u) = dlBox ℓ d u`.**

The fibre `z ↦ ∫_{acube ℓ} w_{1,B(u)}(z,y) dy` is *uniformly* bounded in `z`
(`Work.BoseFixB1.wSmall1Pair_fibre_abs_le`) and a.e. strongly measurable
(`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`, transported from `acube ℓ` to the
smaller box `dlBox ℓ d u`), and `dlBox ℓ d u` has finite Lebesgue measure, so
`MeasureTheory.Integrable.of_bound` applies. -/
private theorem integrableOn_w1Fibre_dlBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      (Submission.BoseGases.dlBox ℓ d u) := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hfin : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.dlBox ℓ d u)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.dlBox ℓ d u)) := by
    have h0 := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      hg0.aemeasurable
    refine (h0.mono_measure (MeasureTheory.Measure.restrict_mono
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) le_rfl)).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair])
  refine MeasureTheory.Integrable.of_bound hmeas
    ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M)
        * (8 * Real.pi * _root_.BoseGases.a v)))
    (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, Submission.BoseGases.w1Fibre]
  simpa only [Submission.BoseGases.wSmall1Pair] using
    Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z

theorem boxPIndFibreMassB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * (Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
      = (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          / Work.SmallBoxSliding.boxMass ℓ d u)
        * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hw1 : MeasureTheory.IntegrableOn
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Submission.BoseGases.dlBox ℓ d u) :=
    integrableOn_w1Fibre_dlBox hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u
  have hone : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        = (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) :=
    fun i => Work.BoseFixB1S.Q0C.one_value hℓ hvol hA hvolA hAc i hw1 hΦc
  rw [Work.BoseFixB1S.boxFlatCount, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hone i)

end Work.BoseFixB1
