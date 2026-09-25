import Mathlib

open MeasureTheory ENNReal

namespace Work.BourgainPlan.IonescuWainger

/-- Chebyshev's inequality in the `(2,2)` Bernstein/almost-orthogonality form, stated for a
finite measure space (here the counting measure on a finite type).

If an operator `L` satisfies the `ℓ² → ℓ²` bound `√(∑ ‖L g x‖²) ≤ A₀ √(∑ ‖g x‖²)` (for every
`g`), then it is of weak type `(2,2)` with constant `A₀`:  for every `f` and every `lam > 0`,
`#{x | lam < ‖L f x‖} ≤ (A₀/lam)² · ‖f‖_{L²(count)}²`. -/
theorem weak_type_two_of_finset_l2_sqrt {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {A₀ : ℝ} (hA₀ : 0 ≤ A₀) (L : (α → ℂ) → (α → ℂ))
    (hL : ∀ g : α → ℂ,
      Real.sqrt (∑ x, ‖L g x‖ ^ (2:ℝ)) ≤ A₀ * Real.sqrt (∑ x, ‖g x‖ ^ (2:ℝ))) :
    ∀ (f : α → ℂ) (lam : ℝ), 0 < lam →
      MeasureTheory.Measure.count {x : α | lam < ‖L f x‖}
        ≤ ENNReal.ofReal (A₀ / lam) ^ (2:ℝ)
          * (MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
              (MeasureTheory.Measure.count : MeasureTheory.Measure α)) ^ (2:ℝ) := by
  intro f lam hlam
  -- The level set is the underlying set of a `Finset`, so its counting measure is its cardinality.
  set T : Finset α := Finset.univ.filter (fun x => lam < ‖L f x‖) with hT
  have hS : ({x : α | lam < ‖L f x‖} : Set α) = ↑T := by
    ext x; simp [T]
  have hcount : MeasureTheory.Measure.count {x : α | lam < ‖L f x‖} = (T.card : ENNReal) := by
    rw [hS, MeasureTheory.Measure.count_apply_finset]
  -- Abbreviate the two `ℓ²` sums.
  set D : ℝ := ∑ x, ‖f x‖ ^ (2:ℝ) with hDdef
  set E : ℝ := ∑ x, ‖L f x‖ ^ (2:ℝ) with hEdef
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hEnn : 0 ≤ E := by rw [hEdef]; positivity
  have hL' : Real.sqrt E ≤ A₀ * Real.sqrt D := by rw [hEdef, hDdef]; exact hL f
  -- Squaring the hypothesis: `E ≤ A₀² D`.
  have hE_le : E ≤ A₀^2 * D := by
    have hsq : (Real.sqrt E)^2 ≤ (A₀ * Real.sqrt D)^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg E) hL' 2
    rwa [Real.sq_sqrt hEnn, mul_pow, Real.sq_sqrt hDnn] at hsq
  -- Chebyshev on `T`: `#T · lam² ≤ E`.
  have hstep1 : (T.card : ℝ) * lam ^ (2:ℝ) ≤ E := by
    have hsum : ∑ x ∈ T, lam ^ (2:ℝ) ≤ ∑ x ∈ T, ‖L f x‖ ^ (2:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' : lam < ‖L f x‖ := by simpa [T] using hx
      exact Real.rpow_le_rpow (le_of_lt hlam) (le_of_lt hx') (by norm_num)
    have hconst : ∑ x ∈ T, lam ^ (2:ℝ) = (T.card : ℝ) * lam ^ (2:ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst, hEdef]
    exact le_trans hsum
      (Finset.sum_le_sum_of_subset_of_nonneg (hT ▸ Finset.filter_subset _ _)
        (fun i _ _ => by positivity))
  have hcard : (T.card : ℝ) * lam ^ (2:ℝ) ≤ A₀^2 * D := le_trans hstep1 hE_le
  -- Divide by `lam²`.
  have hlam2 : (0:ℝ) < lam ^ (2:ℝ) := Real.rpow_pos_of_pos hlam 2
  have hmain : (T.card : ℝ) ≤ (A₀ / lam) ^ (2:ℝ) * D := by
    have h1 : (T.card : ℝ) ≤ (A₀^2 * D) / lam ^ (2:ℝ) := (le_div_iff₀ hlam2).mpr hcard
    have heq : (A₀^2 * D) / lam ^ (2:ℝ) = (A₀ / lam) ^ (2:ℝ) * D := by
      rw [Real.rpow_two, Real.rpow_two, div_pow, div_mul_eq_mul_div]
    rwa [heq] at h1
  -- The `L²(count)` seminorm of `f` is the square root of the finite sum `D`.
  have hB0 : (MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
        (MeasureTheory.Measure.count : MeasureTheory.Measure α)) ^ (2:ℝ)
      = ENNReal.ofReal (∑ x, ‖f x‖ ^ (2:ℝ)) := by
    have hterm : ∀ x, ‖f x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖f x‖ ^ (2:ℝ)) := by
      intro x
      rw [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0:ℝ) ≤ 2)]
      rw [← ENNReal.ofReal_coe_nnreal (p := ‖f x‖₊ ^ (2:ℝ))]
      congr 1
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by norm_num : (ENNReal.ofReal 2) ≠ 0) (by norm_num : (ENNReal.ofReal 2) ≠ ⊤)
          (Measurable.of_discrete (f := f)).aestronglyMeasurable]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)]
    rw [← ENNReal.rpow_mul, show ((1:ℝ)/(2:ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rw [MeasureTheory.lintegral_count, tsum_fintype]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (f := fun x => ‖f x‖ ^ (2:ℝ)) (fun x _ => by positivity)]
  have hB : (MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
        (MeasureTheory.Measure.count : MeasureTheory.Measure α)) ^ (2:ℝ) = ENNReal.ofReal D := by
    rw [hDdef]; exact hB0
  have hA0lam : 0 ≤ A₀ / lam := div_nonneg hA₀ (le_of_lt hlam)
  have hprod : 0 ≤ (A₀ / lam) ^ (2:ℝ) := Real.rpow_nonneg hA0lam 2
  -- Put the right-hand side into the single `ofReal`.
  have hRHS : ENNReal.ofReal (A₀ / lam) ^ (2:ℝ)
      * (MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
          (MeasureTheory.Measure.count : MeasureTheory.Measure α)) ^ (2:ℝ)
      = ENNReal.ofReal ((A₀ / lam) ^ (2:ℝ) * D) := by
    rw [hB, ENNReal.ofReal_rpow_of_nonneg hA0lam (by norm_num), ← ENNReal.ofReal_mul hprod]
  rw [hcount, hRHS, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hmain

end Work.BourgainPlan.IonescuWainger
