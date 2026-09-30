import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A quantitative comparison of `n ^ (-s)` and `(n + 1) ^ (-s)`

For `s > 0` and `n : ℕ`,

`n * (n ^ (-s) - (n + 1) ^ (-s)) ≤ s * n ^ (-s)`.

The proof uses the mean value theorem applied to `t ↦ t ^ (-s)` on `[n, n + 1]`:
the resulting intermediate point `c` lies strictly to the right of `n`, and since
`t ↦ t ^ (-s - 1)` is decreasing (negative exponent) on `(0, ∞)`, the derivative at
`c` is bounded above by the derivative at `n`. This is the discrete
"summation by parts"/integral-comparison estimate used to control the difference
between consecutive values of `n ↦ n ^ (-s)`.
-/

open Set

namespace Work.BMF

/-- For `s > 0` and `n : ℕ`, the drop of `t ↦ t ^ (-s)` from `n` to `n + 1`, scaled by
`n`, is at most `s` times the value at `n`. -/
lemma nat_mul_rpow_sub_le (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (n : ℝ) * ((n : ℝ) ^ (-s) - ((n : ℝ) + 1) ^ (-s)) ≤ s * (n : ℝ) ^ (-s) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Real.zero_rpow (show (-s) ≠ 0 by linarith)]
  · set N : ℝ := (n : ℝ) with hNdef
    have hN1 : (1 : ℝ) ≤ N := by
      rw [hNdef]; exact_mod_cast hn
    have hNpos : 0 < N := by linarith
    -- mean value theorem for `t ↦ t ^ (-s)` on `[N, N + 1]`
    have hcont : ContinuousOn (fun t : ℝ => t ^ (-s)) (Icc N (N + 1)) := by
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      exact Or.inl (ne_of_gt (show (0 : ℝ) < x by linarith [hx.1, hNpos]))
    have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ (-s)) (Ioo N (N + 1)) := by
      apply DifferentiableOn.rpow_const differentiableOn_id
      intro x hx
      exact Or.inl (ne_of_gt (show (0 : ℝ) < x by linarith [hx.1, hNpos]))
    obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope (f := fun t : ℝ => t ^ (-s))
      (show N < N + 1 by linarith) hcont hdiff
    have hcpos : 0 < c := by linarith [hc.1, hNpos]
    -- the derivative `t ↦ -s * t ^ (-s - 1)` is increasing in `t`, and `c > N`
    have hcle : c ^ (-s - 1) ≤ N ^ (-s - 1) := by
      have h1 : 1 / c ^ (s + 1) ≤ 1 / N ^ (s + 1) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNpos _)
          (Real.rpow_le_rpow hNpos.le (le_of_lt hc.1) (by linarith))
      rw [show -s - 1 = -(s + 1) by ring, Real.rpow_neg hcpos.le, ← one_div,
          Real.rpow_neg hNpos.le, ← one_div]
      exact h1
    -- rewrite the mean value theorem into the required form
    have hDeq : s * c ^ (-s - 1) = N ^ (-s) - (N + 1) ^ (-s) := by
      have h := hderiv
      rw [Real.deriv_rpow_const, show (N + 1) - N = 1 by ring, div_one] at h
      have : -((-s) * c ^ (-s - 1)) = -((N + 1) ^ (-s) - N ^ (-s)) := by rw [h]
      simpa [neg_mul, neg_neg, neg_sub] using this
    have hmul : N * N ^ (-s - 1) = N ^ (-s) := by
      have h := Real.rpow_add hNpos (-s - 1) 1
      rw [show -s - 1 + 1 = -s by ring, Real.rpow_one] at h
      rw [h]; ring
    calc N * (N ^ (-s) - (N + 1) ^ (-s))
        = N * (s * c ^ (-s - 1)) := by rw [hDeq]
      _ ≤ N * (s * N ^ (-s - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hNpos.le
            exact mul_le_mul_of_nonneg_left hcle hs.le
      _ = s * N ^ (-s) := by rw [← hmul]; ring

end Work.BMF
