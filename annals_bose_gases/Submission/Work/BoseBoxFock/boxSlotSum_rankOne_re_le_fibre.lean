import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_self_re_le_fibre
import Submission.Work.BoseBoxFock.frkDictMain
import Submission.Work.BoseBoxFock.integrableOn_kinFT_winState_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem boxSlotSum_rankOne_re_le_fibre {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {f : Work.BoseBoxFock.Lab N → Fin m → ℝ}
    (hq : ∀ k : Work.BoseBoxFock.Lab N,
      Work.BoseK15.corpusBox.qVec ℓ (Work.BoseBoxFock.kmomLab ℓ N k)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))] fun x =>
          ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e (f k) x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (k : Work.BoseBoxFock.Lab N) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        star (Work.BoseBoxFock.boxRestrictC ℓ Φ x)
          * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (f k))
              (Work.BoseBoxFock.boxRestrictC ℓ Φ) x).re
      ≤ ∑ j : Fin n, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j)
            * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
                (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
                (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2) := by
  classical
  -- ## 0. The box restriction is measurable and everywhere bounded
  have hboxm : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hΘm : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
    have h : Work.BoseBoxFock.boxRestrictC ℓ Φ = fun x : Submission.BoseGases.X n =>
        ((Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
      funext x
      simp only [Work.BoseBoxFock.boxRestrictC]
      push_cast
      ring
    rw [h]
    exact Complex.continuous_ofReal.measurable.comp
      (hΦ.continuous.measurable.mul (measurable_const.indicator hboxm))
  have hΘb : ∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.boxRestrictC ℓ Φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (f := fun x : Submission.BoseGases.X n => (Φ x : ℝ)) hΦ.continuous.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · have hval : Work.BoseBoxFock.boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
        simp only [Work.BoseBoxFock.boxRestrictC]
        rw [Set.indicator_of_mem hx (fun _ => (1 : ℝ))]
        simp
      rw [hval, Complex.norm_real, Real.norm_eq_abs]
      exact (hC x hx).trans (le_max_left _ _)
    · have hval : Work.BoseBoxFock.boxRestrictC ℓ Φ x = 0 := by
        simp only [Work.BoseBoxFock.boxRestrictC]
        rw [Set.indicator_of_notMem hx (fun _ => (1 : ℝ))]
        simp
      rw [hval, norm_zero]
      exact le_max_right _ _
  -- ## 1. The rank-one slot sum is the sum of the single slots
  have hexp := Work.BoseBoxFock.boxSlotSum_rankOne_eq_sum_slotOf hmeas hbdd hsupp (f k)
    (Work.BoseBoxFock.boxRestrictC ℓ Φ) hΘm hΘb
  -- ## 2. Integrability of each slot-integrand on the box
  have hInt : ∀ j : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) *
        Work.BoseDict.boxSlotOf e (f k) (f k) j (Work.BoseBoxFock.boxRestrictC ℓ Φ) x)
      (Submission.BoseGases.abox n ℓ) := by
    intro j
    obtain ⟨hmj, hbj⟩ := Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
      (f k) (f k) j (Work.BoseBoxFock.boxRestrictC ℓ Φ) hΘm hΘb
    obtain ⟨B, hB⟩ := hbj
    obtain ⟨C, hC⟩ := hΘb
    have hstarm : Measurable fun x : Submission.BoseGases.X n =>
        star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) := by
      have h : (fun x : Submission.BoseGases.X n => star (Work.BoseBoxFock.boxRestrictC ℓ Φ x))
          = fun x => (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC ℓ Φ x) := by
        funext x; rw [Complex.star_def]
      rw [h]
      exact Complex.continuous_conj.measurable.comp hΘm
    refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hstarm.mul hmj).aestronglyMeasurable (max C 0 * max B 0) ?_
    filter_upwards with x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hC x).trans (le_max_left _ _)) ((hB x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  -- ## 3. Split the integral of the slot sum into the sum of the slot integrals
  have hstep : (∫ x in Submission.BoseGases.abox n ℓ, star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) *
        (∑ j : Fin n, Work.BoseDict.boxSlotOf e (f k) (f k) j
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ∑ j : Fin n, star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) *
            Work.BoseDict.boxSlotOf e (f k) (f k) j (Work.BoseBoxFock.boxRestrictC ℓ Φ) x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Finset.sum_apply, Finset.mul_sum]
  rw [hexp, hstep, MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hInt j),
    Complex.re_sum]
  -- ## 4. The per-slot dictionary bound, summed over the slots
  exact Finset.sum_le_sum (fun j _ =>
    Work.BoseBoxFock.boxSlotOf_self_re_le_fibre (hℓ := hℓ) (e := e) (f := f) (hq := hq)
      (hΦ := hΦ) j k)

end Work.BoseBoxFock
