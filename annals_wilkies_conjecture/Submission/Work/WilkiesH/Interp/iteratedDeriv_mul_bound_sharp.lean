import Mathlib

namespace Work.WilkiesH.Interp

/-- **Sharp Leibniz bound.**  If `f` and `g` are `C^m` at `s₀` and their iterated derivatives at
`s₀` up to order `j ≥ m` are dominated by the geometric sequences `A ^ k` and `c ^ k`, then the
`m`-th iterated derivative of the product `f * g` at `s₀` satisfies the binomial-sharp bound
`|(f * g)^{(m)}(s₀)| ≤ (A + c) ^ m`.

The proof is the general Leibniz rule `iteratedDeriv_mul`, termwise estimating each summand and
recognising the resulting sum `∑ i, m.choose i * A ^ i * c ^ (m - i)` as the binomial expansion
`(A + c) ^ m`. -/
theorem iteratedDeriv_mul_bound_sharp {j m : ℕ} (hm : m ≤ j) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    {f g : ℝ → ℝ} {s₀ : ℝ} (hf : ContDiffAt ℝ (m : ℕ) f s₀) (hg : ContDiffAt ℝ (m : ℕ) g s₀)
    (hfd : ∀ k, k ≤ j → |iteratedDeriv k f s₀| ≤ A ^ k)
    (hgd : ∀ k, k ≤ j → |iteratedDeriv k g s₀| ≤ c ^ k) :
    |iteratedDeriv m (f * g) s₀| ≤ (A + c) ^ m := by
  -- General Leibniz rule.
  rw [iteratedDeriv_mul hf hg]
  -- Termwise bound on every summand of the Leibniz sum.
  have hterm : ∀ i ∈ Finset.range (m + 1),
      |(m.choose i : ℝ) * iteratedDeriv i f s₀ * iteratedDeriv (m - i) g s₀|
        ≤ (m.choose i : ℝ) * A ^ i * c ^ (m - i) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hfd i (le_trans him hm)
    have h2 := hgd (m - i) (le_trans (Nat.sub_le m i) hm)
    have hci : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    have hAi : (0 : ℝ) ≤ A ^ i := pow_nonneg hA i
    rw [abs_mul, abs_mul, abs_of_nonneg hci]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hci) h2 (abs_nonneg _) (mul_nonneg hci hAi)
  calc |∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * iteratedDeriv i f s₀ * iteratedDeriv (m - i) g s₀|
      ≤ ∑ i ∈ Finset.range (m + 1),
          |(m.choose i : ℝ) * iteratedDeriv i f s₀ * iteratedDeriv (m - i) g s₀| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A ^ i * c ^ (m - i) :=
        Finset.sum_le_sum hterm
    _ = (A + c) ^ m := by
        rw [add_pow]
        exact Finset.sum_congr rfl (fun i _ => by ring)

end Work.WilkiesH.Interp
