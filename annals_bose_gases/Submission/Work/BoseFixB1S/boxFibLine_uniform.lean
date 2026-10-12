import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxFibLine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

noncomputable section

theorem boxFibLine_uniform {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {N : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
      (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ),
      (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        ≤ ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v)))
          * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ := by
  intro N ℓ d hℓ hd hR hRχ u Φ hΦc
  set Kf : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            / Work.SmallBoxSliding.smallConvLower M)
          * (8 * Real.pi * _root_.BoseGases.a v)) with hKf
  have hle : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z ≤ Kf :=
    fun z => by
      rw [hKf]
      exact boxFibLine_fibre_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hfi_nn : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  have hKf_nn : 0 ≤ Kf := le_trans (hfi_nn 0) (hle 0)
  have hvolnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [Work.SmallBoxSliding.boxMass]
    refine integral_nonneg (fun x => ?_)
    simp only [Work.SmallBoxSliding.boxInd]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    fun x hx => hx.1
  rw [boxQCount, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 * Kf)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const hℓ hvolnn hA hvolA hAc i hΦc
  calc ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 * Kf :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hfi_nn (x i))))
          hint
          (Filter.Eventually.of_forall
            (fun x => mul_le_mul_of_nonneg_left (hle (x i)) (sq_nonneg _)))
    _ = Kf * ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 := by
        rw [MeasureTheory.integral_mul_const, mul_comm]

end

end Work.BoseFixB1S
