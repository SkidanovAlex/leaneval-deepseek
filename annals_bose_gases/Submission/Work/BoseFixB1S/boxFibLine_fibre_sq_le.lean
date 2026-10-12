import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1S.boxFibLine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option linter.style.haveILetI false

/-- **The `L²`-fibre line of the localised one-body kernel.**

With `fib z := w1Fibre ℓ (wSmall1Pair h M ℓ d u) z` the two pointwise inputs
`0 ≤ fib` (`boxFibLine_fibre_nonneg`) and `fib ≤ Kf` (`boxFibLine_fibre_le`,
`Kf` the constant of the statement) give, on the finite-measure box `dlBox ℓ d u`:

* `fib²` is integrable (bounded on a finite-measure set, after the a.e. strong
  measurability `Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`);
* `∫ fib² ≤ Kf · ∫ fib` (pointwise `fib² ≤ Kf·fib`, monotonicity of the integral);
* `0 ≤ ∫ fib` (integral of a pointwise nonnegative function). -/
theorem boxFibLine_fibre_sq_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) ^ 2)
        (Submission.BoseGases.dlBox ℓ d u)
      ∧ (∫ z in Submission.BoseGases.dlBox ℓ d u,
          (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) ^ 2)
        ≤ ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v)))
          * (∫ z in Submission.BoseGases.dlBox ℓ d u,
              Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ∧ 0 ≤ ∫ z in Submission.BoseGases.dlBox ℓ d u,
              Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z := by
  -- ## the two pointwise inputs: sign and size of the fibre
  have hnn : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  have hle : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z ≤
        ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v))) :=
    fun z => boxFibLine_fibre_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hKf_nn := le_trans (hnn 0) (hle 0)
  -- ## the box `dlBox ℓ d u` has finite measure, and the fibre is a.e. strongly measurable
  haveI hfin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.dlBox ℓ d u)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u⟩
  have hmeas : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.dlBox ℓ d u)) := by
    have hg0 : AEMeasurable (Submission.BoseGases.g0 v h)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
    have h0 := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
    refine (h0.mono_measure (MeasureTheory.Measure.restrict_mono
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) le_rfl)).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair])
  -- ## integrability of `fib²` (bounded on a finite-measure set)
  have hInt_sq : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) ^ 2)
      (Submission.BoseGases.dlBox ℓ d u) := by
    refine MeasureTheory.Integrable.of_bound (hmeas.pow 2)
      (((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v))) ^ 2)
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hnn z) (hle z) 2
  -- ## integrability of the dominating function `Kf · fib`
  have hInt_f : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v)))
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      (Submission.BoseGases.dlBox ℓ d u) := by
    have hb : MeasureTheory.Integrable
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.dlBox ℓ d u)) :=
      MeasureTheory.Integrable.of_bound hmeas _
        (Filter.Eventually.of_forall (fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]; exact hle z))
    simpa only [MeasureTheory.IntegrableOn] using hb.const_mul _
  -- ## the inequality `∫ fib² ≤ Kf · ∫ fib`
  have hineq : (∫ z in Submission.BoseGases.dlBox ℓ d u,
          (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) ^ 2)
        ≤ ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v)))
          * (∫ z in Submission.BoseGases.dlBox ℓ d u,
              Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) := by
    calc (∫ z in Submission.BoseGases.dlBox ℓ d u,
          (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) ^ 2)
        ≤ ∫ z in Submission.BoseGases.dlBox ℓ d u,
            ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v)))
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hInt_f
            (Filter.Eventually.of_forall (fun z => by
              simpa only [pow_two] using mul_le_mul_of_nonneg_right (hle z) (hnn z)))
      _ = ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M)
              * (8 * Real.pi * _root_.BoseGases.a v)))
          * ∫ z in Submission.BoseGases.dlBox ℓ d u,
              Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z := by
          rw [MeasureTheory.integral_const_mul]
  -- ## nonnegativity of the fibre integral
  have hnonneg : (0:ℝ) ≤ ∫ z in Submission.BoseGases.dlBox ℓ d u,
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall hnn)
  exact ⟨hInt_sq, hineq, hnonneg⟩

end Work.BoseFixB1S
