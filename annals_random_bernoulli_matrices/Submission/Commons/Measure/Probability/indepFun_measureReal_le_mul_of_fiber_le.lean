import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Measure Set
open scoped ENNReal

namespace Commons.Measure.Probability

/-- If `A` and `B` are independent, then the probability that `(A, B) ∈ S` while `A ∈ H`
is bounded by `c` times the probability of `A ∈ H`, provided that, conditionally on every
`a ∈ H`, the `B`-fiber of `S` over `a` has probability at most `c`. -/
theorem indepFun_measureReal_le_mul_of_fiber_le {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : Ω → α) (B : Ω → β)
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hind : ProbabilityTheory.IndepFun A B P)
    (S : Set (α × β)) (hS : MeasurableSet S) (H : Set α) (hH : MeasurableSet H)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hbound : ∀ a : α, a ∈ H → (P.map B).real {b : β | (a, b) ∈ S} ≤ c) :
    P.real {x : Ω | (A x, B x) ∈ S ∧ A x ∈ H} ≤ c * P.real {x : Ω | A x ∈ H} := by
  let μ : Measure α := P.map A
  let ν : Measure β := P.map B
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hB
  let T : Set (α × β) := S ∩ (H ×ˢ Set.univ)
  have hTm : MeasurableSet T := hS.inter (hH.prod MeasurableSet.univ)
  let cₑ : ℝ≥0∞ := ENNReal.ofReal c
  -- the event of interest is the preimage of T under the pair (A, B)
  have hE : {x : Ω | (A x, B x) ∈ S ∧ A x ∈ H} = (fun x : Ω => (A x, B x)) ⁻¹' T := by
    ext x
    simp [T]
  -- independence: the law of the pair is the product of the laws
  have hπ : P.map (fun x : Ω => (A x, B x)) = μ.prod ν := by
    dsimp [μ, ν]
    exact hind.map_prod_eq_prod_map_map hA hB
  -- pointwise bound on the fibers over T
  have hsec : ∀ a : α, ν (Prod.mk a ⁻¹' T) ≤ cₑ * (H.indicator (fun _ : α => (1 : ℝ≥0∞)) a) := by
    intro a
    by_cases ha : a ∈ H
    · have hfiber : Prod.mk a ⁻¹' T = {b : β | (a, b) ∈ S} := by
        ext b
        simp [T, ha]
      calc
        ν (Prod.mk a ⁻¹' T) = ν {b : β | (a, b) ∈ S} := by rw [hfiber]
        _ = ENNReal.ofReal (ν.real {b : β | (a, b) ∈ S}) := by
          rw [ofReal_measureReal]
        _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (hbound a ha)
        _ = cₑ * (H.indicator (fun _ : α => (1 : ℝ≥0∞)) a) := by simp [cₑ, ha]
    · have hfiber : Prod.mk a ⁻¹' T = ∅ := by
        ext b
        simp [T, ha]
      calc
        ν (Prod.mk a ⁻¹' T) = ν ∅ := by rw [hfiber]
        _ = 0 := by simp
        _ ≤ cₑ * (H.indicator (fun _ : α => (1 : ℝ≥0∞)) a) := by simp [ha]
  -- integrate the fiber bound
  have hlin : (∫⁻ a, ν (Prod.mk a ⁻¹' T) ∂μ) ≤ cₑ * μ H := by
    calc
      (∫⁻ a, ν (Prod.mk a ⁻¹' T) ∂μ) ≤
          (∫⁻ a, cₑ * (H.indicator (fun _ : α => (1 : ℝ≥0∞)) a) ∂μ) := by
        exact lintegral_mono hsec
      _ = cₑ * μ H := by
        have hg : (fun a : α => cₑ * (H.indicator (fun _ : α => (1 : ℝ≥0∞)) a)) =
            H.indicator (fun _ : α => cₑ) := by
          funext a
          by_cases h : a ∈ H <;> simp [h]
        rw [hg]
        exact lintegral_indicator_const hH cₑ
  -- bound the product measure of T
  have hprod : μ.prod ν T ≤ cₑ * μ H := (Measure.prod_apply_le hTm).trans hlin
  -- convert the ENNReal inequality to a real one
  have hRHSne : cₑ * μ H ≠ ∞ := by
    have hc : cₑ < ∞ := ENNReal.ofReal_lt_top
    have hμ : μ H < ∞ := by
      haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hA
      exact measure_lt_top μ H
    exact ne_of_lt (ENNReal.mul_lt_top hc hμ)
  have htoReal : ((μ.prod ν) T).toReal ≤ (cₑ * μ H).toReal := ENNReal.toReal_mono hRHSne hprod
  -- reassemble the desired real inequality
  have hmain : P.real {x : Ω | (A x, B x) ∈ S ∧ A x ∈ H} ≤ c * μ.real H := by
    calc
      P.real {x : Ω | (A x, B x) ∈ S ∧ A x ∈ H}
          = ((μ.prod ν) T).toReal := by
            rw [hE]
            rw [← map_measureReal_apply_of_aemeasurable (hA.prodMk hB) hTm]
            rw [hπ]
            rfl
      _ ≤ (cₑ * μ H).toReal := htoReal
      _ = c * μ.real H := by
        rw [ENNReal.toReal_ofReal_mul c (μ H) hc0]
        rw [measureReal_def]
  -- μ.real H is the probability of the event {A ∈ H}
  have hm : μ.real H = P.real {x : Ω | A x ∈ H} := by
    dsimp [μ]
    rw [map_measureReal_apply_of_aemeasurable hA hH]
    rfl
  simpa [hm] using hmain

end Commons.Measure.Probability