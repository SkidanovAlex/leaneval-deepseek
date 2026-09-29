import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- Arithmetic behind the Neumann truncation `n = ⌈ps/(α²(t-s))⌉` (`buNeumann`).

With `θ = t/s - 1 ≥ p/α⁴` and `α² < p`:
* `α²θ ≥ α²·p/α⁴ = p/α² > 1`, so the geometric tail decays;
* `n = (ps-1)/(α²(t-s)) + 1 ≥ ps/(α²(t-s))`, hence `α²θ·n = α²(t-s)/s·n ≥ p`,
  so the truncation error `(1/2)·2^{-α²θn}/(1-2^{-α²θ}) ≤ 2^{-p}`. -/
theorem buNeumannArith (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) ∧
    (p : ℝ) ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) * (Work.Resample.egN p α s t : ℝ) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hα2pos : (0 : ℝ) < (α : ℝ) ^ 2 := by positivity
  constructor
  · -- `α²θ ≥ α²·(p/α⁴) = p/α² > 1`
    have h1 : (α : ℝ) ^ 2 * ((p : ℝ) / (α : ℝ) ^ 4) ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) :=
      mul_le_mul_of_nonneg_left hθ (le_of_lt hα2pos)
    have h2 : (α : ℝ) ^ 2 * ((p : ℝ) / (α : ℝ) ^ 4) = (p : ℝ) / (α : ℝ) ^ 2 := by
      have h4 : (α : ℝ) ^ 4 = (α : ℝ) ^ 2 * (α : ℝ) ^ 2 := by ring
      rw [h4, ← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hα2pos)]
    have h3 : (1 : ℝ) < (p : ℝ) / (α : ℝ) ^ 2 := by
      rw [one_lt_div hα2pos]
      exact_mod_cast hαp
    rw [← h2] at h3
    exact le_of_lt (lt_of_lt_of_le h3 h1)
  · -- `α²θ = α²(t-s)/s` and `n·(α²(t-s)) ≥ ps`
    set d : ℕ := α ^ 2 * (t - s) with hd
    set N : ℕ := Work.Resample.egN p α s t with hNdef
    have hdpos : 0 < d := by
      have : 0 < t - s := by omega
      rw [hd]; positivity
    have hNval : N = (p * s - 1) / d + 1 := by
      rw [hNdef]; simp only [Work.Resample.egN, hd]
    have hkey : p * s ≤ N * d := by
      have hmod : (p * s - 1) % d < d := Nat.mod_lt _ hdpos
      have hdiv : d * ((p * s - 1) / d) + (p * s - 1) % d = p * s - 1 := Nat.div_add_mod _ _
      have hlt : p * s - 1 < ((p * s - 1) / d + 1) * d := by
        calc p * s - 1 = d * ((p * s - 1) / d) + (p * s - 1) % d := hdiv.symm
          _ < d * ((p * s - 1) / d) + d := by omega
          _ = ((p * s - 1) / d + 1) * d := by ring
      have hps1 : 1 ≤ p * s := by
        have hppos : 0 < p := by omega
        have hspos : 0 < s := by omega
        have := Nat.mul_pos hppos hspos
        omega
      have hslt := Nat.succ_le_of_lt hlt
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hps1] at hslt
      rwa [hNval]
    have hA : (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) = ((d : ℕ) : ℝ) / (s : ℝ) := by
      rw [hd]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (le_of_lt hst)]
      field_simp
    have hkeyR : (p : ℝ) * (s : ℝ) ≤ (N : ℝ) * ((d : ℕ) : ℝ) := by
      exact_mod_cast hkey
    have hmain : (p : ℝ) ≤ ((N : ℝ) * ((d : ℕ) : ℝ)) / (s : ℝ) := by
      rw [le_div_iff₀ hs0]
      exact hkeyR
    rw [hA]
    calc (p : ℝ) ≤ ((N : ℝ) * ((d : ℕ) : ℝ)) / (s : ℝ) := hmain
      _ = (((d : ℕ) : ℝ) / (s : ℝ)) * (N : ℝ) := by ring

end Work.Resample
