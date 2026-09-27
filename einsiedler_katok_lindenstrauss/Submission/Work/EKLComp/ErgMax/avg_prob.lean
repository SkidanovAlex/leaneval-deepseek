import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic

/-!
# The `A⁺`-average of a probability measure

For a probability measure `ν` concentrated on the forward-invariant set `Drho ρ`, every pushforward
`(act g)_* ν` along a grid element `g = aDiag (shift N i j)` (with `i, j ≥ 0`, `N ≥ 1`) is again a
probability measure concentrated on `Drho ρ`.  Hence so is their average `avg ν N`.
-/

open MeasureTheory
open scoped ENNReal BigOperators
open Work.EKLContract

namespace Work.EKLComp.ErgMax

/-- A finite sum of measures, evaluated on an arbitrary set (no measurability needed). -/
private theorem finset_sum_measure_apply {α : Type*} [MeasurableSpace α] {ι : Type*}
    (s : Finset ι) (μ : ι → Measure α) (t : Set α) :
    (∑ i ∈ s, μ i) t = ∑ i ∈ s, μ i t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_apply, ih]

/-- Pushforward of a probability measure concentrated on an `f`-forward-invariant set. -/
private theorem map_apply_eq_one {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f : α → α} (hf : Measurable f) {s : Set α}
    (hfs : ∀ x ∈ s, f x ∈ s) (hν : ν s = 1) : ν.map f s = 1 := by
  have hpre : ν (f ⁻¹' s) = 1 := by
    refine le_antisymm ?_ ?_
    · calc ν (f ⁻¹' s) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · rw [← hν]
      exact measure_mono fun x hx => hfs x hx
  refine le_antisymm ?_ ?_
  · calc ν.map f s ≤ ν.map f Set.univ := measure_mono (Set.subset_univ _)
      _ = ν (f ⁻¹' Set.univ) := Measure.map_apply hf MeasurableSet.univ
      _ = 1 := by rw [Set.preimage_univ, measure_univ]
  · rw [← hpre]
    exact Measure.le_map_apply hf.aemeasurable s

theorem avg_prob (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure ν] {ρ : ℝ} (hν : ν (Work.EKLContract.Drho ρ) = 1)
    {N : ℕ} (hN : 1 ≤ N) :
    MeasureTheory.IsProbabilityMeasure (Work.EKLComp.ErgMax.avg ν N) ∧
      Work.EKLComp.ErgMax.avg ν N (Work.EKLContract.Drho ρ) = 1 := by
  have hN0 : N ≠ 0 := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- Each grid element is a non-negative `aPlus`, hence keeps `Drho ρ` invariant.
  have hterm : ∀ (i j : Fin (n N)), ν.map (act (aDiag (shift N i j))) (Drho ρ) = 1 := by
    intro i j
    have hr : 0 ≤ (i : ℝ) / N := div_nonneg (Nat.cast_nonneg (i : ℕ)) hNr.le
    have hs : 0 ≤ (j : ℝ) / N := div_nonneg (Nat.cast_nonneg (j : ℕ)) hNr.le
    refine map_apply_eq_one ν (measurable_act _) ?_ hν
    intro x hx
    rw [act_apply, aDiag_shift]
    exact aPlus_maps_Drho hr hs hx
  have hnum : ((n N * n N : ℕ) : ℝ≥0∞) ≠ 0 := by
    have h : n N * n N ≠ 0 := by
      simp only [n]
      exact Nat.mul_ne_zero (Nat.mul_ne_zero hN0 hN0) (Nat.mul_ne_zero hN0 hN0)
    exact_mod_cast h
  have htop : ((n N * n N : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hinv : (((n N * n N : ℕ) : ℝ≥0∞))⁻¹ * ((n N * n N : ℕ) : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel hnum htop
  have hcard : (∑ _i : Fin (n N), ∑ _j : Fin (n N), (1 : ℝ≥0∞))
      = ((n N * n N : ℕ) : ℝ≥0∞) := by
    simp [Finset.sum_const, Nat.cast_mul, nsmul_eq_mul]
  have hSuniv :
      (∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j)))) Set.univ
        = ((n N * n N : ℕ) : ℝ≥0∞) := by
    rw [finset_sum_measure_apply]
    trans ∑ _i : Fin (n N), ∑ _j : Fin (n N), (1 : ℝ≥0∞)
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [finset_sum_measure_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Measure.map_apply (measurable_act _) MeasurableSet.univ, Set.preimage_univ, measure_univ]
    · exact hcard
  have hSrho :
      (∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j)))) (Drho ρ)
        = ((n N * n N : ℕ) : ℝ≥0∞) := by
    rw [finset_sum_measure_apply]
    trans ∑ _i : Fin (n N), ∑ _j : Fin (n N), (1 : ℝ≥0∞)
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [finset_sum_measure_apply]
      exact Finset.sum_congr rfl fun j _ => hterm i j
    · exact hcard
  constructor
  · refine ⟨?_⟩
    rw [avg_def, Measure.smul_apply, hSuniv, smul_eq_mul, hinv]
  · rw [avg_def, Measure.smul_apply, hSrho, smul_eq_mul, hinv]

end Work.EKLComp.ErgMax
