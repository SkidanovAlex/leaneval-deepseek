import Mathlib
set_option linter.unusedVariables false

namespace Work.OddVolterra.Existence

/-- Leibniz bound: if the first `m+1` iterated derivatives of `f` at `v` are bounded by `a ≥ 0`
and those of `g` by `D ≥ 0`, then the `m`-th iterated derivative of the pointwise product
`f * g` at `v` is bounded by `2^m * a * D`. -/
theorem iteratedDeriv_mul_abs_bound (m : ℕ) (f g : ℝ → ℝ) (v a D : ℝ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f v) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g v)
    (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hfb : ∀ i : ℕ, i ≤ m → |iteratedDeriv i f v| ≤ a)
    (hgb : ∀ k : ℕ, k ≤ m → |iteratedDeriv k g v| ≤ D) :
    |iteratedDeriv m (f * g) v| ≤ 2 ^ m * a * D := by
  have hle : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  rw [iteratedDeriv_mul (hf.of_le hle) (hg.of_le hle)]
  calc |∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * iteratedDeriv i f v * iteratedDeriv (m - i) g v|
      ≤ ∑ i ∈ Finset.range (m + 1),
          |(m.choose i : ℝ) * iteratedDeriv i f v * iteratedDeriv (m - i) g v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * a * D := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hmi : m - i ≤ m := Nat.sub_le m i
        have hc : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
        have hfi := hfb i hi_le
        have hgi := hgb (m - i) hmi
        have h1 : |iteratedDeriv i f v| * |iteratedDeriv (m - i) g v| ≤ a * D :=
          mul_le_mul hfi hgi (abs_nonneg _) ha
        simp only [abs_mul, abs_of_nonneg hc]
        calc (m.choose i : ℝ) * |iteratedDeriv i f v| * |iteratedDeriv (m - i) g v|
            = (m.choose i : ℝ) * (|iteratedDeriv i f v| * |iteratedDeriv (m - i) g v|) := by
              ring
          _ ≤ (m.choose i : ℝ) * (a * D) := mul_le_mul_of_nonneg_left h1 hc
          _ = (m.choose i : ℝ) * a * D := by ring
    _ = 2 ^ m * a * D := by
        have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
          exact_mod_cast Nat.sum_range_choose m
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

end Work.OddVolterra.Existence
