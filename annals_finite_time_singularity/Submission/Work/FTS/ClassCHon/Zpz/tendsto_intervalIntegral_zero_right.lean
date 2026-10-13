import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Filter

/-- **The primitive of an `L¹` function vanishes at `0⁺`.**  If `f` is integrable on `(0,1)`, then
the indefinite integral `t ↦ ∫ x in (0)..t, f x` tends to `0` at `0⁺`.

Route: `∫ x in (0)..t, f x = ∫ x in Set.Ioc 0 t, f x` for `t ≥ 0`
(`intervalIntegral.integral_of_le`), and the sets `Set.Ioo 0 (1/(n+1))` decrease to `∅`, so
`MeasureTheory.tendsto_setIntegral_of_antitone` applied to `‖f‖` gives
`∫⁻ x in Set.Ioo 0 (1/(n+1)), ‖f x‖ → 0`; then squeeze via
`‖∫ x in s, f x‖ ≤ ∫⁻ x in s, ‖f x‖` and `MeasureTheory.lintegral_mono_set`
(for `0 < t < 1/(n+1)`, `Set.Ioc 0 t ⊆ Set.Ioo 0 (1/(n+1))`). -/
theorem tendsto_intervalIntegral_zero_right {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo 0 1)) :
    Filter.Tendsto (fun t => ∫ x in (0)..t, f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- The decreasing family `s n = (0, 1/(n+1))` of test intervals.
  set s : ℕ → Set ℝ := fun n => Set.Ioo 0 (1 / ((n : ℝ) + 1)) with hs
  have hsanti : Antitone s := by
    intro m n hmn x hx
    refine ⟨hx.1, ?_⟩
    have hle : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    exact lt_of_lt_of_le hx.2 (one_div_le_one_div_of_le (by positivity) hle)
  -- The family decreases to the empty set.
  have hInter : (⋂ n, s n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_iInter] at hx
    by_cases hx0 : 0 < x
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx0
      exact absurd (hx n).2 (not_lt.mpr hn.le)
    · exact hx0 (hx 0).1
  have hs0 : s 0 = Set.Ioo 0 1 := by simp [hs]
  -- Convergence of the integrals over the decreasing family.
  have hmain : Filter.Tendsto (fun n : ℕ => ∫ x in s n, ‖f x‖) Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone (μ := MeasureTheory.volume)
      (f := fun x => ‖f x‖) (s := s) (fun n => measurableSet_Ioo) hsanti
        ⟨0, by rw [hs0]; exact hf.norm⟩
    simpa [hInter] using h
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmain ε hε
  have hNε : (∫ x in s N, ‖f x‖) < ε := by
    have h1 : dist (∫ x in s N, ‖f x‖) 0 < ε := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at h1
    exact lt_of_le_of_lt (le_abs_self _) h1
  refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
  intro t ht htd
  rw [Real.dist_eq, sub_zero] at htd ⊢
  have ht0 : 0 < t := ht
  have ht_lt : t < 1 / ((N : ℝ) + 1) := by rwa [abs_of_pos ht0] at htd
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hle1 : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith)
    simpa using h
  have hsN : s N = Set.Ioo 0 (1 / ((N : ℝ) + 1)) := by simp [hs]
  have hintN : MeasureTheory.IntegrableOn (fun x => ‖f x‖) (s N) := by
    rw [hsN]
    exact (hf.mono_set (Set.Ioo_subset_Ioo_right hle1)).norm
  calc |∫ x in (0)..t, f x|
      = ‖∫ x in (0)..t, f x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x in (0)..t, ‖f x‖ := intervalIntegral.norm_integral_le_integral_norm ht0.le
    _ = ∫ x in Set.Ioc 0 t, ‖f x‖ := intervalIntegral.integral_of_le ht0.le
    _ ≤ ∫ x in s N, ‖f x‖ := by
        refine MeasureTheory.setIntegral_mono_set (s := Set.Ioc 0 t) (t := s N) hintN
          (Filter.Eventually.of_forall fun x => norm_nonneg (f x)) ?_
        exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht_lt⟩
    _ < ε := hNε

end Work.FTS.ClassCHon.Zpz
