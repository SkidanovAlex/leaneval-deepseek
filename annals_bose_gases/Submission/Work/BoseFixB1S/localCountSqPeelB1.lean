import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_fib_collapse
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The two-factor small-box bump `chiSmallB M ℓ d u = χ(x/ℓ)·χ_M(x/(ℓd) - u)` is measurable for
*every* `M`, `ℓ`, `d`: the `ℓ`-scale factor is the continuous corpus bump, and the `ℓd`-scale
factor is `chiSmallBase` divided by the constant `√(chiSmallNormSq M)`. -/
theorem measurable_chiSmallB (M : ℕ) (ℓ d : ℝ) (u : E3) :
    Measurable (Submission.BoseGases.chiSmallB M ℓ d u) := by
  have hcs : Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) := by
    have h := Submission.BoseGases.chiSmallBase_continuous M
    simpa only [Submission.BoseGases.chiSmall] using
      h.div_const (Real.sqrt (Submission.BoseGases.chiSmallNormSq M))
  have h1 : Continuous (fun x : E3 => ((ℓ * d)⁻¹ : ℝ) • x - u) := by fun_prop
  exact ((Submission.BoseGases.chiScale_continuous ℓ).mul (hcs.comp h1)).measurable

/-- `QᵢΨ = 1_A(xᵢ)Ψ − PᵢΨ` is measurable when `Ψ` is. -/
theorem measurable_boxQInd {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (i : Fin N) {Ψ : X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) := by
  have h1 : Measurable (fun x : X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) :=
    (measurable_sigAt A hA i).mul hΨ
  have h2 : Measurable (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i Ψ x) :=
    measurable_boxPInd volA A hA i hΨ
  have hsub := h1.sub h2
  have heq : ((fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x)
      - (fun x : X N => Work.UBBInputs8.boxPInd volA A i Ψ x))
      = fun x : X N => Work.UBBInputs8.boxQInd volA A i Ψ x := by
    funext x
    simp only [Pi.sub_apply, Work.UBBInputs8.boxQInd]
  rwa [heq] at hsub

/-- **Auxiliary form of the local count peel, with an abstract fibre `χ`.**  Under the fibre
hypotheses `χ² ≤ κ·1_A` and `IntegrableOn (χ²) A`, the squared local count at `χ` is controlled by
the flat count `S` (with the fibre average `volA⁻¹∫_A χ²`) and the mean-free count `n₊`. -/
theorem localCountSqPeelAux {N : ℕ} {ℓ volA κ : ℝ}
    {A : Set E3} {χ : E3 → ℝ}
    (hℓ : 0 < ℓ) (hvol : 0 < volA) (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (hκ : 0 ≤ κ)
    (hχm : Measurable χ)
    (hχle : ∀ z : E3, χ z ^ 2 ≤ κ * A.indicator (fun _ => (1 : ℝ)) z)
    (hfib : IntegrableOn (fun z : E3 => χ z ^ 2) A)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2)
      ≤ 2 * ((1 / volA) * ∫ z in A, χ z ^ 2) * boxFlatCount volA ℓ A Φ
        + 2 * κ * boxQCount volA ℓ A Φ := by
  classical
  have hvolA' : volA = ((MeasureTheory.volume : MeasureTheory.Measure E3) A).toReal := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  obtain ⟨C, hC0, hΦb, hPb, hQb⟩ :=
    boxBounds (N := N) (ℓ := ℓ) (volA := volA) (A := A) hℓ hvol hA hvolA' hAc hΦc
  -- the flat-slot fibre collapse for the fibre `χ²`
  have hpeel : (∑ i : Fin N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
      = ((1 / volA) * ∫ z in A, χ z ^ 2) * boxFlatCount volA ℓ A Φ :=
    (boxPInd_fib_collapse (N := N) (ℓ := ℓ) (volA := volA) (A := A)
      hℓ hvol hA hAc hvolA hΦc (fib := fun z : E3 => χ z ^ 2) hfib).1
  -- the pointwise AM–GM, slot by slot
  have hpt : ∀ (i : Fin N) (x : X N),
      (Φ x) ^ 2 * (χ (x i)) ^ 2
        ≤ 2 * ((Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := by
    intro i x
    by_cases hxA : x i ∈ A
    · -- on `A` the decomposition `1_A(xᵢ)Φ = PᵢΦ + QᵢΦ` holds
      have hQ : Work.UBBInputs8.boxQInd volA A i Φ x
          = Φ x - Work.UBBInputs8.boxPInd volA A i Φ x := by
        simp only [Work.UBBInputs8.boxQInd, Set.indicator_of_mem hxA, one_mul]
      have hc : (χ (x i)) ^ 2 ≤ κ := by
        have h := hχle (x i)
        rw [Set.indicator_of_mem hxA, mul_one] at h
        exact h
      have hc0 : 0 ≤ (χ (x i)) ^ 2 := sq_nonneg _
      have hsq : (Φ x) ^ 2 ≤ 2 * (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := by
        rw [hQ]
        nlinarith [sq_nonneg (2 * Work.UBBInputs8.boxPInd volA A i Φ x - Φ x)]
      have h1 : (χ (x i)) ^ 2 * (Φ x) ^ 2
          ≤ (χ (x i)) ^ 2 * (2 * (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
              + 2 * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hc0
      have h2 : (χ (x i)) ^ 2 * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
          ≤ κ * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      nlinarith [h1, h2]
    · -- off `A` the fibre vanishes
      have hcz : (χ (x i)) ^ 2 = 0 := by
        have h := hχle (x i)
        rw [Set.indicator_of_notMem hxA, mul_zero] at h
        exact le_antisymm h (sq_nonneg _)
      rw [hcz, mul_zero, mul_zero, mul_zero, zero_add]
      positivity
  -- slot-by-slot integral inequality
  have hstep : ∀ i : Fin N,
      (∫ x in abox N ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2)
        ≤ 2 * (∫ x in abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
    intro i
    have hPm : Measurable (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) :=
      (measurable_boxPInd volA A hA i hΦc.measurable).pow_const 2
    have hcim : Measurable (fun x : X N => (χ (x i)) ^ 2) :=
      (hχm.comp (measurable_pi_apply i)).pow_const 2
    have hPbd : ∀ x ∈ abox N ℓ, |(Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2| ≤ C ^ 2 := by
      intro x hx
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hPb i x hx) 2
    have hcbd : ∀ x ∈ abox N ℓ, |(χ (x i)) ^ 2| ≤ κ := by
      intro x hx
      rw [abs_of_nonneg (sq_nonneg _)]
      by_cases hxA : x i ∈ A
      · have h := hχle (x i)
        rwa [Set.indicator_of_mem hxA, mul_one] at h
      · have h := hχle (x i)
        rw [Set.indicator_of_notMem hxA, mul_zero] at h
        exact le_trans h hκ
    have hIntP : IntegrableOn (fun x : X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2) (abox N ℓ) :=
      integrableOn_mul_of_bound hℓ hPm hcim hPbd hcbd
    have hQm : Measurable (fun x : X N => Work.UBBInputs8.boxQInd volA A i Φ x) :=
      measurable_boxQInd volA A hA i hΦc.measurable
    have hIntQ : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        (abox N ℓ) :=
      integrableOn_sq_of_bound hℓ hQm (hQb i)
    have hdom : IntegrableOn (fun x : X N =>
        2 * ((Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) (abox N ℓ) :=
      (hIntP.const_mul 2).add (hIntQ.const_mul (2 * κ))
    have hmono : (∫ x in abox N ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2)
        ≤ ∫ x in abox N ℓ, (2 * ((Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
            + 2 * κ * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => by positivity))
        hdom
        (Filter.Eventually.of_forall (fun x => hpt i x))
    have hsplit : (∫ x in abox N ℓ,
          (2 * ((Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
            + 2 * κ * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2))
        = 2 * (∫ x in abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
      rw [MeasureTheory.integral_add
            (f := fun x : X N =>
              2 * ((Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2))
            (g := fun x : X N => 2 * κ * (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            (hIntP.const_mul 2) (hIntQ.const_mul (2 * κ)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    linarith [hmono, hsplit]
  -- sum over the slots
  have hsum : (∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2)
      ≤ ∑ i : Fin N, (2 * (∫ x in abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)) :=
    Finset.sum_le_sum (fun i _ => hstep i)
  have hsplit2 : (∑ i : Fin N, (2 * (∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
        + 2 * κ * (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)))
      = 2 * (∑ i : Fin N, ∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
        + 2 * κ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  calc (∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2)
      ≤ ∑ i : Fin N, (2 * (∫ x in abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)) := hsum
    _ = 2 * (∑ i : Fin N, ∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * (χ (x i)) ^ 2)
          + 2 * κ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := hsplit2
    _ = 2 * (((1 / volA) * ∫ z in A, χ z ^ 2) * boxFlatCount volA ℓ A Φ)
          + 2 * κ * boxQCount volA ℓ A Φ := by
        rw [hpeel, boxQCount]
    _ = 2 * ((1 / volA) * ∫ z in A, χ z ^ 2) * boxFlatCount volA ℓ A Φ
          + 2 * κ * boxQCount volA ℓ A Φ := by ring

theorem localCountSqPeelB1 {N : ℕ} {ℓ volA κ : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {M : ℕ} {d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < ℓ) (hvol : 0 < volA) (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure
      (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hκ : 0 ≤ κ)
    (hχle : ∀ z : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
        ≤ κ * A.indicator (fun _ => (1 : ℝ)) z)
    (hfib : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      ≤ 2 * ((1 / volA) * ∫ z in A, (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
          * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        + 2 * κ * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  exact localCountSqPeelAux (χ := Submission.BoseGases.chiSmallB M ℓ d u)
    hℓ hvol hA hvolA hAc hκ (measurable_chiSmallB M ℓ d u) hχle hfib hΦc

end Work.BoseFixB1S
