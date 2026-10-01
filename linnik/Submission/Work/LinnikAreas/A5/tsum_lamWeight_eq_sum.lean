import Mathlib
import Submission.Work.LinnikAreas.A5.lambert_defs

namespace Work.LinnikAreas.A5

theorem tsum_lamWeight_eq_sum {x₀ q lam : ℝ} (hx₀ : 0 < x₀) (hq : 1 < q) {f : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 - lam / Real.log q)) *
        f (Real.log n / Real.log q))
      = ∑ n ∈ Finset.Icc 1 ⌊q ^ x₀⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 - lam / Real.log q)) *
            f (Real.log n / Real.log q) := by
  have _hx₀_pos : (0 : ℝ) < x₀ := hx₀
  -- Only the terms with `1 ≤ n ≤ ⌊q ^ x₀⌋₊` can be nonzero: for larger `n`
  -- we have `n > q ^ x₀`, hence `log n / log q > x₀` and `f` vanishes there.
  refine tsum_eq_sum (s := Finset.Icc 1 ⌊q ^ x₀⌋₊) ?_
  intro n hn
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
    simp
  · have hmn : ⌊q ^ x₀⌋₊ < n := by
      have h1 : 1 ≤ n → ⌊q ^ x₀⌋₊ < n := by
        simpa [Finset.mem_Icc, not_and, not_le] using hn
      exact h1 (by omega)
    have hqpos : 0 < q := lt_trans zero_lt_one hq
    have hkey : q ^ x₀ < (n : ℝ) := by
      have h1 := Nat.lt_floor_add_one (q ^ x₀)
      have h2 : ((⌊q ^ x₀⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (by omega : ⌊q ^ x₀⌋₊ + 1 ≤ n)
      linarith
    have hlogq : 0 < Real.log q := Real.log_pos hq
    have hlog : x₀ < Real.log n / Real.log q := by
      have h1 : Real.log (q ^ x₀) < Real.log n :=
        Real.log_lt_log (Real.rpow_pos_of_pos hqpos x₀) hkey
      rw [Real.log_rpow hqpos] at h1
      rw [lt_div_iff₀ hlogq]
      exact h1
    rw [hsupp (Real.log n / Real.log q) (le_of_lt hlog)]
    simp

end Work.LinnikAreas.A5
