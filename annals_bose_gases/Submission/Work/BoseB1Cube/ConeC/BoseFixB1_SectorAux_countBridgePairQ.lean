import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_a0A2QJointPairQCountLe
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_boxPairQCountMeas
import Submission.Work.BoseFixB1.SectorAux.pairSetSumProdMeas
import Submission.Work.BoseFixB1.boxQInd_selfAdjoint_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem countBridgePairQ {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
    {c : ℝ} (hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      (Work.FockBridge.boxCount A x) * (Φ x) ^ 2 = c * (Φ x) ^ 2)
    (hcS2 : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ) :
    (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * (p.2.card : ℝ) *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  -- the two operator-applied states
  let Xf : Submission.BoseGases.X N → ℝ :=
    fun x => ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x
  let Yf : Submission.BoseGases.X N → ℝ :=
    fun x => ∑ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ x
  -- **measurability** of the two sums
  have hXm : Measurable Xf := by
    show Measurable (fun x : Submission.BoseGases.X N =>
      ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
    exact Finset.measurable_sum Finset.univ
      (fun i _ => Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm)
  have hYm : Measurable Yf := by
    show Measurable (fun x : Submission.BoseGases.X N =>
      ∑ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ x)
    exact Finset.measurable_sum Finset.univ
      (fun i _ => Work.SlotWord.measurable_boxQInd volA A hA i hΦm)
  -- **boundedness** on the analysis box
  have hXb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Xf x| ≤ (N : ℝ) * |Cb| := by
    intro x hx
    show |∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x| ≤ (N : ℝ) * |Cb|
    calc |∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x|
        ≤ ∑ i : Fin N, |Work.UBBInputs8.boxPInd volA A i Φ x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, |Cb| := Finset.sum_le_sum (fun i _ =>
            le_trans (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb x hx)
              (le_abs_self Cb))
      _ = (N : ℝ) * |Cb| := by simp
  have hYb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Yf x| ≤ (N : ℝ) * (2 * |Cb|) := by
    intro x hx
    show |∑ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ x| ≤ (N : ℝ) * (2 * |Cb|)
    calc |∑ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ x|
        ≤ ∑ i : Fin N, |Work.UBBInputs8.boxQInd volA A i Φ x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, 2 * |Cb| := Finset.sum_le_sum (fun i _ =>
            Work.BoseFixB1.abs_boxQInd_le_two hℓ hvol hA hvolA hAc i hΦb x hx)
      _ = (N : ℝ) * (2 * |Cb|) := by simp
  -- **integrability** of the products we integrate
  have hIΦX : IntegrableOn (fun x : Submission.BoseGases.X N => Φ x * Xf x)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm hXm hΦb hXb
  have hIΦY : IntegrableOn (fun x : Submission.BoseGases.X N => Φ x * Yf x)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm hYm hΦb hYb
  have hIYY : IntegrableOn (fun x : Submission.BoseGases.X N => Yf x * Yf x)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hYm hYm hYb hYb
  -- **the pointwise operator identity** `Pᵢ + Qᵢ = 1_A(xᵢ)·id`
  have hPQ : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      Work.UBBInputs8.boxPInd volA A i Φ x + Work.UBBInputs8.boxQInd volA A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
    intro i x
    simp only [Work.UBBInputs8.boxQInd]
    ring
  -- hence `Xf + Yf = n_A·Φ`
  have hXY : ∀ x : Submission.BoseGases.X N,
      Xf x + Yf x = Work.FockBridge.boxCount A x * Φ x := by
    intro x
    show (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
        + (∑ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ x)
      = Work.FockBridge.boxCount A x * Φ x
    have hstep : (∑ i : Fin N, (Work.UBBInputs8.boxPInd volA A i Φ x
          + Work.UBBInputs8.boxQInd volA A i Φ x))
        = ∑ i : Fin N, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
      Finset.sum_congr rfl (fun i _ => hPQ i x)
    rw [← Finset.sum_add_distrib, hstep, ← Finset.sum_mul,
      Work.FockBridge.boxCount_eq_sum_indicator]
  -- the sector hypothesis, in the form `n_A·Φ = c·Φ` a.e.
  have hcount' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Work.FockBridge.boxCount A x * Φ x = c * Φ x := by
    filter_upwards [hcount] with x hx
    by_cases h0 : Φ x = 0
    · rw [h0]; ring
    · have h2 : (Work.FockBridge.boxCount A x - c) * (Φ x) ^ 2 = 0 := by nlinarith [hx]
      have h3 : (Φ x) ^ 2 ≠ 0 := pow_ne_zero 2 h0
      have h4 : Work.FockBridge.boxCount A x - c = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h h3
      rw [sub_eq_zero.mp h4]
  have hXYae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Xf x + Yf x = c * Φ x := by
    filter_upwards [hcount'] with x hx
    rw [hXY x]
    exact hx
  -- **the flat count is `⟨Φ, Xf⟩`**
  have htermP : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := by
    intro i
    have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm
    have hPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ Cb :=
      Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
    have hsa := Work.BoseFixB1S.boxPIndSelfAdjoint (N := N) (ℓ := ℓ) (volA := volA)
      hℓ hvol hA hvolA hAc i hΦm hΦb hPm hPb
    have hidem : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ)
        = Work.UBBInputs8.boxPInd volA A i Φ :=
      Work.BoseFixB1S.boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i Φ
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          ring
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ) x :=
          hsa
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hidem]
  have hSint : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Xf x := by
    have hI : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
        Φ x * Work.UBBInputs8.boxPInd volA A i Φ x) (Submission.BoseGases.abox N ℓ) volume :=
      fun i => Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm) hΦb
        (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb)
    calc Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := rfl
      _ = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A i Φ x :=
          Finset.sum_congr rfl (fun i _ => htermP i)
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            ∑ i : Fin N, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x :=
          (MeasureTheory.integral_finsetSum (μ := MeasureTheory.volume.restrict
            (Submission.BoseGases.abox N ℓ)) Finset.univ (fun i _ => hI i)).symm
      _ = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Xf x := by
          apply integral_congr_ae
          filter_upwards with x
          show (∑ i : Fin N, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
              = Φ x * ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x
          rw [Finset.mul_sum]
  -- **the excited count is `⟨Φ, Yf⟩`**
  have htermQ : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxQInd volA A i Φ x := by
    intro i
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
      Work.SlotWord.measurable_boxQInd volA A hA i hΦm
    have hQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * |Cb| :=
      Work.BoseFixB1.abs_boxQInd_le_two hℓ hvol hA hvolA hAc i hΦb
    have hsa := Work.BoseFixB1S.boxQIndSelfAdjoint (N := N) (ℓ := ℓ) (volA := volA)
      hℓ hvol hA hvolA hAc i hΦm hΦb hQm hQb
    have hidem : Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ)
        = Work.UBBInputs8.boxQInd volA A i Φ :=
      Work.BoseFixB1.boxQInd_self_idem hvol hA hvolA i Φ
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          ring
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ) x :=
          hsa
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxQInd volA A i Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hidem]
  have hQint : Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Yf x := by
    have hI : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
        Φ x * Work.UBBInputs8.boxQInd volA A i Φ x) (Submission.BoseGases.abox N ℓ) volume :=
      fun i => Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm
        (Work.SlotWord.measurable_boxQInd volA A hA i hΦm) hΦb
        (Work.BoseFixB1.abs_boxQInd_le_two hℓ hvol hA hvolA hAc i hΦb)
    calc Work.BoseFixB1S.boxQCount volA ℓ A Φ
        = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := rfl
      _ = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxQInd volA A i Φ x :=
          Finset.sum_congr rfl (fun i _ => htermQ i)
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            ∑ i : Fin N, Φ x * Work.UBBInputs8.boxQInd volA A i Φ x :=
          (MeasureTheory.integral_finsetSum (μ := MeasureTheory.volume.restrict
            (Submission.BoseGases.abox N ℓ)) Finset.univ (fun i _ => hI i)).symm
      _ = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Yf x := by
          apply integral_congr_ae
          filter_upwards with x
          show (∑ i : Fin N, Φ x * Work.UBBInputs8.boxQInd volA A i Φ x)
              = Φ x * ∑ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ x
          rw [Finset.mul_sum]
  -- **`boxFlatCount + boxQCount = c`**
  have hSplusN : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      + Work.BoseFixB1S.boxQCount volA ℓ A Φ = c := by
    rw [hSint, hQint]
    rw [(MeasureTheory.integral_add hIΦX hIΦY).symm]
    have h2 : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x * Xf x + Φ x * Yf x))
        = ∫ x in Submission.BoseGases.abox N ℓ, c * (Φ x * Φ x) := by
      apply integral_congr_ae
      filter_upwards [hXYae] with x hx
      have hx' : Xf x = c * Φ x - Yf x := by linarith [hx]
      rw [hx']; ring
    rw [h2, MeasureTheory.integral_const_mul]
    have h3 : (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Φ x) = 1 := by
      rw [← hnorm]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h3]; ring
  -- **`Σ|S||T|∫ψ² = ⟨Xf, Yf⟩`**
  have hLHS : (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * (p.2.card : ℝ) *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, Xf x * Yf x := by
    rw [show Work.BoseFixB1.disjPairs N = Work.BoseFixB1S.disjPairs N from rfl]
    rw [boxPairQCountMeas (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc hΦm hΦb,
      pairSetSumProdMeas (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc hΦm hΦb]
  -- **`⟨Xf, Yf⟩ = c·boxQCount − ⟨Yf, Yf⟩`**
  have hXY2 : (∫ x in Submission.BoseGases.abox N ℓ, Xf x * Yf x)
      = c * Work.BoseFixB1S.boxQCount volA ℓ A Φ
        - ∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x := by
    have h1 : (∫ x in Submission.BoseGases.abox N ℓ, Xf x * Yf x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (c * (Φ x * Yf x) - Yf x * Yf x) := by
      apply integral_congr_ae
      filter_upwards [hXYae] with x hx
      have hx' : Xf x = c * Φ x - Yf x := by linarith [hx]
      rw [hx']; ring
    rw [h1, MeasureTheory.integral_sub (hIΦY.const_mul c) hIYY,
      MeasureTheory.integral_const_mul, ← hQint]
  -- **Cauchy–Schwarz**: `boxQCount² ≤ ⟨Yf, Yf⟩`
  have hCS : (Work.BoseFixB1S.boxQCount volA ℓ A Φ) ^ 2
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x := by
    have : IsFiniteMeasure
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.abox_lt_top N ℓ hℓ.le))
    have hΦLp : MemLp Φ 2
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      refine MemLp.of_bound hΦm.aestronglyMeasurable Cb ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable N ℓ)] with x hx
      rw [Real.norm_eq_abs]
      exact hΦb x hx
    have hYLp : MemLp Yf 2
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      refine MemLp.of_bound hYm.aestronglyMeasurable ((N : ℝ) * (2 * |Cb|)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable N ℓ)] with x hx
      rw [Real.norm_eq_abs]
      exact hYb x hx
    have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt
      (μ := MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) hΦLp hYLp
    rw [← hQint, hnorm, Real.sqrt_one, one_mul] at hcs
    have hnn : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x := by
      apply integral_nonneg
      intro x
      exact mul_self_nonneg _
    have hsq : (∫ x in Submission.BoseGases.abox N ℓ, Yf x ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hsq] at hcs
    calc (Work.BoseFixB1S.boxQCount volA ℓ A Φ) ^ 2
        = |Work.BoseFixB1S.boxQCount volA ℓ A Φ| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = ∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x := Real.sq_sqrt hnn
  -- **assembly**
  rw [hLHS]
  calc (∫ x in Submission.BoseGases.abox N ℓ, Xf x * Yf x)
      = c * Work.BoseFixB1S.boxQCount volA ℓ A Φ
        - ∫ x in Submission.BoseGases.abox N ℓ, Yf x * Yf x := hXY2
    _ ≤ c * Work.BoseFixB1S.boxQCount volA ℓ A Φ
        - (Work.BoseFixB1S.boxQCount volA ℓ A Φ) ^ 2 := by linarith [hCS]
    _ = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
        have hc : c = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
            + Work.BoseFixB1S.boxQCount volA ℓ A Φ := by linarith [hSplusN]
        rw [hc]; ring

end Work.BoseFixB1.SectorAux
