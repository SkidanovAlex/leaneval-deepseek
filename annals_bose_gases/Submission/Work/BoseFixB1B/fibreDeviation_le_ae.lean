import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.perBoxF_flat
import Submission.Work.BoseFixB1B.fibreDeviation_aux
import Submission.Work.BoseFixB1S.boxAbsIntegralMulMulLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real BigOperators

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. Integrability of a bounded measurable slot factor against the deviation

This is the a.e. replacement of `Work.BoseFixB1B.integrableOn_slot_mul_delta`: the only thing the
original uses `Measurable δ` for is the a.e. strong measurability of the slot map, which is exactly
the hypothesis here. -/

theorem integrableOn_mul_delta_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {δ : E3 → ℝ} (i : Fin N)
    (hδae : MeasureTheory.AEStronglyMeasurable (fun x : X N => δ (x i))
      ((volume : Measure (X N)).restrict (abox N ℓ)))
    {D : ℝ} (hD : ∀ z, |δ z| ≤ D)
    {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    MeasureTheory.IntegrableOn (fun x : X N => f x * δ (x i)) (abox N ℓ) volume := by
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
    ((hfm.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul hδae)
    (|C| * |D|) ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hfb x hx) (le_abs_self C)) (le_trans (hD (x i)) (le_abs_self D))
    (abs_nonneg _) (abs_nonneg _)

/-! ## 1. The vanishing of the `P`-part, with a.e. measurability

`∫_{abox} (PᵢΦ)²·δ(xᵢ) = 0`.  The support hypothesis `δ = 0` off `A` is **not** used here: only
`∫_A δ = 0` and the collapse `∫_{acube ℓ} 1_A·δ = ∫_A δ`. -/

theorem pPartZero_ae {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {δ : E3 → ℝ}
    (hδae : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable
      (fun x : X N => δ (x i))
      ((volume : Measure (X N)).restrict (abox N ℓ)))
    (hδmean : ∫ z in A, δ z = 0)
    {D : ℝ} (hD : ∀ z, |δ z| ≤ D)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) = 0 := by
  classical
  rcases N with _ | n
  · exact Fin.elim0 i
  obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
  have hint : MeasureTheory.IntegrableOn (fun x : X (n + 1) =>
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) (abox (n + 1) ℓ) volume := by
    refine integrableOn_mul_delta_ae (N := n + 1) (ℓ := ℓ) hℓ i (hδae i) hD
      ((Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable).pow_const 2)
      (C := Cp ^ 2) ?_
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Work.UBBInputs8.boxPInd V A i Φ x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCpb x hx) 2
  rw [Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
    (F := fun x : X (n + 1) =>
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) hint]
  have hinner : ∀ r : X n, (∫ y : E3 in acube ℓ,
      (Work.UBBInputs8.boxPInd V A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
        * δ ((Submission.BoseGases.kcInsN n i (y, r)) i)) = 0 := by
    intro r
    have hpoint : ∀ y : E3,
        (Work.UBBInputs8.boxPInd V A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
          * δ ((Submission.BoseGases.kcInsN n i (y, r)) i)
        = ((1 / V) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2
            * (A.indicator (fun _ => (1 : ℝ)) y * δ y) := by
      intro y
      rw [Work.BoseFixB1S.boxPInd_kcInsN, Submission.BoseGases.kc_insN_apply_same]
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy]
        ring
      · simp only [Set.indicator_of_notMem hy]
        ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
      MeasureTheory.integral_const_mul,
      Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc δ, hδmean, mul_zero]
  simp only [hinner, MeasureTheory.integral_zero]

/-! ## 2. The `q`-part, with a.e. measurability

The Cauchy–Schwarz step is the corpus's `boxAbsIntegralMulMulLe` (no measurability of the weight),
applied to the two pieces `QP` and `QQ` of the expansion `Q(2P+Q) = 2QP + Q²`. -/

theorem qPart_le_ae {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {δ : E3 → ℝ}
    (hδae : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable
      (fun x : X N => δ (x i))
      ((volume : Measure (X N)).restrict (abox N ℓ)))
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ z, |δ z| ≤ D)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in abox N ℓ,
        ((Work.UBBInputs8.boxQInd V A i Φ x)
            * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
          * δ (x i))
      ≤ D * ((∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
              + 2 * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                  * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
  classical
  obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
  obtain ⟨Cq, hCq0, hCqb⟩ := exists_boxQInd_bound hℓ hV hA hAc hΦc i
  set P : X N → ℝ := Work.UBBInputs8.boxPInd V A i Φ with hP
  set Q : X N → ℝ := Work.UBBInputs8.boxQInd V A i Φ with hQ
  have hPm : Measurable P := Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable
  have hQm : Measurable Q := by
    have hfun : Q = fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x := by
      funext x
      rw [hQ, Work.UBBInputs8.boxQInd, hP]
    rw [hfun]
    exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul
      hΦc.measurable).sub hPm
  have hI1 : MeasureTheory.IntegrableOn (fun x : X N => Q x * P x * δ (x i))
      (abox N ℓ) volume := by
    refine integrableOn_mul_delta_ae hℓ i (hδae i) hD (hQm.mul hPm) (C := Cq * Cp) ?_
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hCqb x hx) (hCpb x hx) (abs_nonneg _) hCq0
  have hI2 : MeasureTheory.IntegrableOn (fun x : X N => Q x * Q x * δ (x i))
      (abox N ℓ) volume := by
    refine integrableOn_mul_delta_ae hℓ i (hδae i) hD (hQm.mul hQm) (C := Cq * Cq) ?_
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hCqb x hx) (hCqb x hx) (abs_nonneg _) hCq0
  have hsplit : (∫ x in abox N ℓ, (Q x * (2 * P x + Q x)) * δ (x i))
      = 2 * (∫ x in abox N ℓ, Q x * P x * δ (x i))
        + ∫ x in abox N ℓ, Q x * Q x * δ (x i) := by
    have hcongr : (fun x : X N => (Q x * (2 * P x + Q x)) * δ (x i))
        = fun x : X N => 2 * (Q x * P x * δ (x i)) + (Q x * Q x * δ (x i)) := by
      funext x
      ring
    rw [hcongr, MeasureTheory.integral_add (hI1.const_mul 2) hI2,
      MeasureTheory.integral_const_mul]
  have hb1 := Work.BoseFixB1S.boxAbsIntegralMulMulLe (N := N) (ℓ := ℓ) hℓ
    (f := Q) (g := P) (w := fun x : X N => δ (x i))
    (Cf := Cq) (Cg := Cp) (sw := D) hQm hPm hCqb hCpb (fun x => hD (x i))
  have hb2 := Work.BoseFixB1S.boxAbsIntegralMulMulLe (N := N) (ℓ := ℓ) hℓ
    (f := Q) (g := Q) (w := fun x : X N => δ (x i))
    (Cf := Cq) (Cg := Cq) (sw := D) hQm hQm hCqb hCqb (fun x => hD (x i))
  have hsq : Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
        * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
      = ∫ x in abox N ℓ, (Q x) ^ 2 := by
    rw [← sq, Real.sq_sqrt (MeasureTheory.integral_nonneg (fun x => sq_nonneg (Q x)))]
  calc (∫ x in abox N ℓ, (Q x * (2 * P x + Q x)) * δ (x i))
      = 2 * (∫ x in abox N ℓ, Q x * P x * δ (x i))
        + ∫ x in abox N ℓ, Q x * Q x * δ (x i) := hsplit
    _ ≤ |2 * (∫ x in abox N ℓ, Q x * P x * δ (x i))
        + ∫ x in abox N ℓ, Q x * Q x * δ (x i)| := le_abs_self _
    _ ≤ |2 * (∫ x in abox N ℓ, Q x * P x * δ (x i))|
        + |∫ x in abox N ℓ, Q x * Q x * δ (x i)| := abs_add_le _ _
    _ = 2 * |∫ x in abox N ℓ, Q x * P x * δ (x i)|
        + |∫ x in abox N ℓ, Q x * Q x * δ (x i)| := by
        rw [abs_mul, abs_two]
    _ ≤ 2 * (D * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
            * Real.sqrt (∫ x in abox N ℓ, (P x) ^ 2))
        + D * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
            * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
    _ = D * ((∫ x in abox N ℓ, (Q x) ^ 2)
          + 2 * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
              * Real.sqrt (∫ x in abox N ℓ, (P x) ^ 2)) := by
        have hsqD : D * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
              * Real.sqrt (∫ x in abox N ℓ, (Q x) ^ 2)
            = D * ∫ x in abox N ℓ, (Q x) ^ 2 := by
          rw [mul_assoc, hsq]
        rw [hsqD]
        ring

/-! ## 3. The target -/

theorem fibreDeviation_le_ae {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {δ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hδmeas : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => δ (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)))
    (hδsupp : ∀ z, z ∉ A → δ z = 0)
    (hδmean : ∫ z in A, δ z = 0)
    {D : ℝ} (hD : ∀ z, |δ z| ≤ D)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, δ (x i)))
      ≤ D * (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
              + 2 * Real.sqrt (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ)
                  * Real.sqrt (Work.BoseFixB1S.boxFlatCount V ℓ A Φ)) := by
  classical
  have hD0 : 0 ≤ D := le_trans (abs_nonneg (δ 0)) (hD 0)
  obtain ⟨Cb, hCb0, hCbb⟩ := exists_abox_bound' hℓ hΦc
  -- integrability of the three slot integrands, from the a.e. measurability of the slots
  have hintPhi : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : X N => (Φ x) ^ 2 * δ (x i)) (abox N ℓ) volume := by
    intro i
    refine integrableOn_mul_delta_ae hℓ i (hδmeas i) hD (hΦc.measurable.pow_const 2)
      (C := Cb ^ 2) ?_
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Φ x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg (Φ x)) (hCbb x hx) 2
  have hintP : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : X N => (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i))
      (abox N ℓ) volume := by
    intro i
    obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
    refine integrableOn_mul_delta_ae hℓ i (hδmeas i) hD
      ((Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable).pow_const 2)
      (C := Cp ^ 2) ?_
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Work.UBBInputs8.boxPInd V A i Φ x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCpb x hx) 2
  have hintQ : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : X N => ((Work.UBBInputs8.boxQInd V A i Φ x)
        * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
        * δ (x i)) (abox N ℓ) volume := by
    intro i
    obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
    obtain ⟨Cq, hCq0, hCqb⟩ := exists_boxQInd_bound hℓ hV hA hAc hΦc i
    have hPm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
      Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable
    have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) := by
      have h1 : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
        ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦc.measurable
      have h2 : Work.UBBInputs8.boxQInd V A i Φ
          = fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd V A i Φ x := rfl
      rw [h2]
      exact h1.sub hPm
    refine integrableOn_mul_delta_ae hℓ i (hδmeas i) hD
      (hQm.mul ((hPm.const_mul 2).add hQm)) (C := Cq * (2 * Cp + Cq)) ?_
    intro x hx
    show |Work.UBBInputs8.boxQInd V A i Φ x
        * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x)|
      ≤ Cq * (2 * Cp + Cq)
    rw [abs_mul]
    refine mul_le_mul (hCqb x hx) ?_ (abs_nonneg _) hCq0
    calc |2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x|
        ≤ |2 * Work.UBBInputs8.boxPInd V A i Φ x| + |Work.UBBInputs8.boxQInd V A i Φ x| :=
          abs_add_le _ _
      _ = 2 * |Work.UBBInputs8.boxPInd V A i Φ x| + |Work.UBBInputs8.boxQInd V A i Φ x| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Cp + Cq := add_le_add (mul_le_mul_of_nonneg_left (hCpb x hx) (by norm_num))
          (hCqb x hx)
  -- the sum/integral interchange
  have hsum : (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, δ (x i)))
      = ∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * δ (x i) := by
    rw [← MeasureTheory.integral_finsetSum Finset.univ
      (f := fun i : Fin N => fun x : X N => (Φ x) ^ 2 * δ (x i))]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
    · intro i _
      exact hintPhi i
  rw [hsum]
  -- slotwise the identity `Φ²δ = P²δ + Q(2P+Q)δ`
  have hsplit : ∀ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * δ (x i))
      = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i))
        + ∫ x in abox N ℓ,
            ((Work.UBBInputs8.boxQInd V A i Φ x)
              * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
              * δ (x i) := by
    intro i
    rw [← MeasureTheory.integral_add (hintP i) (hintQ i)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact fibreDeviation_pointwise V hδsupp i Φ x
  -- the finite Cauchy–Schwarz and the final arithmetic
  have ha : ∀ i : Fin N, 0 ≤ ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 :=
    fun i => MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hb : ∀ i : Fin N, 0 ≤ ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 :=
    fun i => MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hcs := fibreDeviation_sum_sqrt_le
    (fun i : Fin N => ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
    (fun i : Fin N => ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2) ha hb
  have hident1 : (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      = Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ := rfl
  have hident2 : (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
      = Work.BoseFixB1S.boxFlatCount V ℓ A Φ := rfl
  calc ∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * δ (x i)
      = ∑ i : Fin N, ((∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i))
          + ∫ x in abox N ℓ,
              ((Work.UBBInputs8.boxQInd V A i Φ x)
                * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
                * δ (x i)) :=
        Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i : Fin N, ((0 : ℝ) + ∫ x in abox N ℓ,
              ((Work.UBBInputs8.boxQInd V A i Φ x)
                * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
                * δ (x i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [pPartZero_ae (N := N) (ℓ := ℓ) (V := V) hℓ hV hA hAc hδmeas hδmean hD hΦc i]
    _ ≤ ∑ i : Fin N, D * ((∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
              + 2 * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                  * Real.sqrt (∫ x in abox N ℓ,
                      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        simpa using qPart_le_ae (N := N) (ℓ := ℓ) (V := V) hℓ hV hA hAc hδmeas hD0 hD hΦc i
    _ = D * ∑ i : Fin N, ((∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
              + 2 * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                  * Real.sqrt (∫ x in abox N ℓ,
                      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ D * (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
              + 2 * Real.sqrt (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ)
                  * Real.sqrt (Work.BoseFixB1S.boxFlatCount V ℓ A Φ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD0
        rw [hident1, hident2] at hcs
        simpa using hcs

end Work.BoseFixB1B
