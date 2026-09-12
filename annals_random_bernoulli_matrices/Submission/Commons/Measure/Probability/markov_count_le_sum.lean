import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
noncomputable section
open Classical
attribute [local instance] Classical.propDecidable

namespace Commons.Measure.Probability

/-- Markov bound for a finite counting random variable: if `c(ω) := # {i | ω ∈ A i}`
and `m ≥ 1`, then `P{c ≥ m} ≤ (1/m) · Σ_i P(A i)` (real measures). -/
lemma markov_count_le_sum {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (A : ι → Set Ω)
    (hA : ∀ i : ι, MeasurableSet (A i)) {m : ℕ} (hm : 1 ≤ m) :
    P.real {ω : Ω | m ≤ (Finset.univ.filter (fun i : ι => ω ∈ A i)).card} ≤
      ((1 : ℝ) / (m : ℝ)) * ∑ i : ι, P.real (A i) := by
  classical
  let c : Ω → ℕ := fun ω => (Finset.univ.filter (fun i : ι => ω ∈ A i)).card
  let χ : ι → Ω → ℝ≥0∞ := fun i => (A i).indicator (fun _ : Ω => (1 : ℝ≥0∞))
  let E : Set Ω := {ω : Ω | m ≤ c ω}
  change P.real E ≤ ((1 : ℝ) / (m : ℝ)) * ∑ i : ι, P.real (A i)

  -- measurability of each indicator
  have hχ_meas : ∀ i : ι, Measurable (χ i) := by
    intro i
    change Measurable ((A i).indicator (fun _ : Ω => (1 : ℝ≥0∞)))
    exact Measurable.indicator (f := fun _ : Ω => (1 : ℝ≥0∞)) measurable_const (hA i)

  -- measurability of the ENNReal counting function
  have hf_meas : Measurable (fun ω : Ω => ∑ i ∈ (Finset.univ : Finset ι), χ i ω) := by
    refine Finset.measurable_sum (s := (Finset.univ : Finset ι)) ?_
    intro i hi
    exact hχ_meas i

  -- identity between nat count and ENNReal sum
  have hcount : ∀ ω : Ω, (c ω : ℝ≥0∞) = ∑ i ∈ (Finset.univ : Finset ι), χ i ω := by
    intro ω
    change ((Finset.univ.filter (fun i : ι => ω ∈ A i)).card : ℝ≥0∞) =
      ∑ i ∈ (Finset.univ : Finset ι), ((A i).indicator (fun _ : Ω => (1 : ℝ≥0∞))) ω
    simp only [Set.indicator]
    rw [Finset.sum_boole]

  -- E is measurable
  have hE_meas : MeasurableSet E := by
    have hE_eq : E = {ω : Ω | (m : ℝ≥0∞) ≤ (c ω : ℝ≥0∞)} := by
      ext ω
      constructor
      · intro hω
        exact_mod_cast hω
      · intro hω
        exact_mod_cast hω
    rw [hE_eq]
    change MeasurableSet ((fun ω : Ω => (c ω : ℝ≥0∞)) ⁻¹' Set.Ici (m : ℝ≥0∞))
    refine MeasurableSet.preimage measurableSet_Ici ?_
    convert hf_meas using 1
    funext ω
    exact hcount ω

  -- pointwise inequality (m : ℝ≥0∞) * 1_E ≤ counting function (ENNReal)
  have hpoint : ∀ ω : Ω, (m : ℝ≥0∞) * (E.indicator (fun _ => (1 : ℝ≥0∞))) ω ≤
      ∑ i ∈ (Finset.univ : Finset ι), χ i ω := by
    intro ω
    by_cases hω : ω ∈ E
    · have hmc : m ≤ c ω := hω
      have hcast : (m : ℝ≥0∞) ≤ (c ω : ℝ≥0∞) := by exact_mod_cast hmc
      have hgoal2 : (m : ℝ≥0∞) ≤ ∑ i ∈ (Finset.univ : Finset ι), χ i ω := by
        calc
          (m : ℝ≥0∞) ≤ (c ω : ℝ≥0∞) := hcast
          _ = ∑ i ∈ (Finset.univ : Finset ι), χ i ω := hcount ω
      simpa [E, hω] using hgoal2
    · simp [E, hω]

  -- lintegral of (m · 1_E) equals m * P E
  have hLHS_lin : (∫⁻ ω : Ω, (m : ℝ≥0∞) * (E.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂P) =
      (m : ℝ≥0∞) * P E := by
    calc
      (∫⁻ ω : Ω, (m : ℝ≥0∞) * (E.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂P)
          = (m : ℝ≥0∞) * (∫⁻ ω : Ω, E.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) := by
            refine lintegral_const_mul (r := (m : ℝ≥0∞)) ?_
            exact Measurable.indicator (f := fun _ : Ω => (1 : ℝ≥0∞)) measurable_const hE_meas
      _ = (m : ℝ≥0∞) * P E := by
            rw [lintegral_indicator_const hE_meas (1 : ℝ≥0∞)]
            simp

  -- lintegral of counting function equals sum of measures
  have hRHS_lin : (∫⁻ ω : Ω, (∑ i ∈ (Finset.univ : Finset ι), χ i ω) ∂P) =
      ∑ i ∈ (Finset.univ : Finset ι), P (A i) := by
    calc
      (∫⁻ ω : Ω, (∑ i ∈ (Finset.univ : Finset ι), χ i ω) ∂P)
          = ∑ i ∈ (Finset.univ : Finset ι), (∫⁻ ω : Ω, χ i ω ∂P) := by
            refine lintegral_finsetSum (s := (Finset.univ : Finset ι)) (f := χ) ?_
            intro i hi
            exact hχ_meas i
      _ = ∑ i ∈ (Finset.univ : Finset ι), P (A i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hχi : χ i = (A i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) := rfl
            rw [hχi]
            rw [lintegral_indicator_const (hA i) (1 : ℝ≥0∞)]
            simp

  -- integrate the pointwise inequality
  have hENN : (m : ℝ≥0∞) * P E ≤ ∑ i ∈ (Finset.univ : Finset ι), P (A i) := by
    calc
      (m : ℝ≥0∞) * P E = ∫⁻ ω : Ω, (m : ℝ≥0∞) * (E.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂P := hLHS_lin.symm
      _ ≤ ∫⁻ ω : Ω, (∑ i ∈ (Finset.univ : Finset ι), χ i ω) ∂P := by
            exact lintegral_mono hpoint
      _ = ∑ i ∈ (Finset.univ : Finset ι), P (A i) := hRHS_lin

  -- everything is finite (probability space)
  have hPuniv : P Set.univ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  have hP_le_one : ∀ s : Set Ω, P s ≤ 1 := by
    intro s
    simpa [hPuniv] using (measure_mono (μ := P) (s := s) (t := Set.univ) (Set.subset_univ s))
  have hP_E_fin : P E ≠ ∞ := ne_of_lt (lt_of_le_of_lt (hP_le_one E) ENNReal.one_lt_top)
  have hP_Ai_fin : ∀ i : ι, P (A i) ≠ ∞ := by
    intro i
    exact ne_of_lt (lt_of_le_of_lt (hP_le_one (A i)) ENNReal.one_lt_top)
  have hsum_fin : (∑ i ∈ (Finset.univ : Finset ι), P (A i)) ≠ ∞ := by
    have hlt : (∑ i ∈ (Finset.univ : Finset ι), P (A i)) < ∞ := by
      rw [ENNReal.sum_lt_top]
      intro i hi
      exact lt_of_le_of_lt (hP_le_one (A i)) ENNReal.one_lt_top
    exact ne_of_lt hlt
  have hm_fin : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  have hLHS_fin : (m : ℝ≥0∞) * P E ≠ ∞ := ENNReal.mul_ne_top hm_fin hP_E_fin

  -- toReal both sides
  have hReal : (m : ℝ) * P.real E ≤ ∑ i ∈ (Finset.univ : Finset ι), P.real (A i) := by
    have htr := (ENNReal.toReal_le_toReal hLHS_fin hsum_fin).2 hENN
    rw [ENNReal.toReal_mul] at htr
    rw [ENNReal.toReal_natCast] at htr
    rw [ENNReal.toReal_sum (fun i hi => hP_Ai_fin i)] at htr
    simpa [Measure.real] using htr

  -- arithmetic: 0 < (m : ℝ)
  have hmp : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) hm)
  have hgoal : P.real E ≤ ((1 : ℝ) / (m : ℝ)) * ∑ i : ι, P.real (A i) := by
    calc
      P.real E = ((1 : ℝ) / (m : ℝ)) * ((m : ℝ) * P.real E) := by
        field_simp [ne_of_gt hmp]
      _ ≤ ((1 : ℝ) / (m : ℝ)) * (∑ i ∈ (Finset.univ : Finset ι), P.real (A i)) := by
            exact mul_le_mul_of_nonneg_left hReal (le_of_lt (div_pos zero_lt_one hmp))
  simpa using hgoal

end Commons.Measure.Probability