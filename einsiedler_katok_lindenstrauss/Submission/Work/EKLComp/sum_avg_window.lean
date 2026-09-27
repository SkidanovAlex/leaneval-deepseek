import Mathlib


open MeasureTheory
namespace Work.EKLComp

-- Riemann-sum identity for window averages: the sum over k < n of the average of g over the
-- window [k*d, (k+1)*d] equals the average of g over the whole interval [0, n*d].
-- Proof: ∫_0^d g (τ + k*d) dτ = ∫_{k*d}^{(k+1)*d} g (translation invariance of the interval
-- integral, `intervalIntegral.integral_comp_add_right`), then sum over k < n with
-- `intervalIntegral.sum_integral_adjacent_intervals_Ico` (telescoping), using that
-- IntegrableOn on Ioc 0 (n*d) restricts to each subinterval.
theorem sum_avg_window (g : ℝ → ℝ) (d : ℝ) (hd : 0 < d) (n : ℕ)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioc (0:ℝ) ((n:ℝ) * d)) volume) :
    ∑ k ∈ Finset.range n, d⁻¹ * (∫ τ in (0:ℝ)..d, g (τ + (k:ℝ) * d))
      = d⁻¹ * ∫ τ in (0:ℝ)..((n:ℝ) * d), g τ := by
  -- Integrability restricts from the whole interval to each window [k*d, (k+1)*d].
  have hInt : ∀ (k : ℕ), k < n → IntervalIntegrable g volume ((k:ℝ)*d) (((k+1:ℕ):ℝ)*d) := by
    intro k hk
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; nlinarith [hd])]
    refine hint.mono_set ?_
    intro x hx
    refine ⟨lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg k) hd.le) hx.1, ?_⟩
    calc x ≤ (((k+1:ℕ)):ℝ)*d := hx.2
      _ ≤ (n:ℝ)*d := by
            apply mul_le_mul_of_nonneg_right _ hd.le
            exact_mod_cast Nat.succ_le_of_lt hk
  -- Translation invariance rewrites each window average into an integral over the window.
  have hkey : ∀ (k : ℕ),
      (∫ τ in (0:ℝ)..d, g (τ + (k:ℝ)*d)) = ∫ τ in ((k:ℝ)*d)..(((k+1:ℕ):ℝ)*d), g τ := by
    intro k
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> push_cast <;> ring
  rw [← Finset.mul_sum]
  simp only [hkey]
  rw [intervalIntegral.sum_integral_adjacent_intervals hInt]
  simp

end Work.EKLComp
