import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- One-step logarithmic comparison: for `0 < x` and `0 < s`,
`1/(x+s) ≤ (1/s) * (log (x+s) - log x)`.  Equivalently, writing `u = x/(x+s) ∈ (0,1)`,
it is the inequality `log u ≤ u - 1` multiplied by `-1/s`. -/
private lemma inv_le_log_step (x s : ℝ) (hx : 0 < x) (hs : 0 < s) :
    1 / (x + s) ≤ (1 / s) * (Real.log (x + s) - Real.log x) := by
  have hxs : 0 < x + s := by linarith
  have h1 : 0 < (x + s) / x := div_pos hxs hx
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : ((x + s) / x)⁻¹ = x / (x + s) := by rw [inv_div]
  rw [h3] at h2
  have h4 : 1 - x / (x + s) = s / (x + s) := by
    field_simp
    ring
  rw [h4] at h2
  rw [Real.log_div (ne_of_gt hxs) (ne_of_gt hx)] at h2
  calc 1 / (x + s) = (1 / s) * (s / (x + s)) := by field_simp
    _ ≤ (1 / s) * (Real.log (x + s) - Real.log x) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- For `0 < a`, `0 < s` and `n : ℕ`,
`∑_{j<n} 1/(a + j s) ≤ 1/a + (1/s) log((a + n s)/a)`.
The `j = 0` term is kept as is, and each remaining term is bounded by the
increment of `(1/s) log (a + j s)`, which telescopes. -/
theorem sumInvLeLog (a s : ℝ) (n : ℕ) (ha : 0 < a) (hs : 0 < s) :
    (∑ j ∈ Finset.range n, 1 / (a + (j : ℝ) * s))
      ≤ 1 / a + (1 / s) * Real.log ((a + (n : ℝ) * s) / a) := by
  rcases n with _ | m
  · rw [Finset.range_zero, Finset.sum_empty]
    have h1 : (a + ((0:ℕ):ℝ) * s) / a = 1 := by
      rw [Nat.cast_zero, zero_mul, add_zero, div_self (ne_of_gt ha)]
    rw [h1, Real.log_one, mul_zero, add_zero]
    positivity
  · rw [Finset.sum_range_succ']
    have hf0 : (1:ℝ) / (a + ((0:ℕ):ℝ) * s) = 1 / a := by
      rw [Nat.cast_zero, zero_mul, add_zero]
    rw [hf0]
    have htail : (∑ k ∈ Finset.range m, 1/(a + ((k+1:ℕ):ℝ)*s))
        ≤ (1/s) * Real.log (a + (m:ℝ)*s) - (1/s) * Real.log (a + ((0:ℕ):ℝ)*s) := by
      have hstep : ∀ k ∈ Finset.range m,
          1/(a + ((k+1:ℕ):ℝ)*s)
            ≤ (1/s) * Real.log (a + ((k+1:ℕ):ℝ)*s) - (1/s)*Real.log (a + (k:ℝ)*s) := by
        intro k _
        have hx : 0 < a + (k:ℝ)*s := by positivity
        have hk := inv_le_log_step (a + (k:ℝ)*s) s hx hs
        have hcast : a + ((k+1:ℕ):ℝ)*s = (a + (k:ℝ)*s) + s := by push_cast; ring
        rw [hcast]
        have hthis : (1/s) * Real.log ((a + (k:ℝ)*s) + s) - (1/s) * Real.log (a + (k:ℝ)*s)
            = (1/s) * (Real.log ((a + (k:ℝ)*s) + s) - Real.log (a + (k:ℝ)*s)) := by ring
        rw [hthis]
        exact hk
      calc (∑ k ∈ Finset.range m, 1/(a + ((k+1:ℕ):ℝ)*s))
          ≤ ∑ k ∈ Finset.range m,
              ((1/s) * Real.log (a + ((k+1:ℕ):ℝ)*s) - (1/s)*Real.log (a + (k:ℝ)*s)) :=
            Finset.sum_le_sum hstep
        _ = (1/s) * Real.log (a + (m:ℝ)*s) - (1/s) * Real.log (a + ((0:ℕ):ℝ)*s) := by
            simpa using Finset.sum_range_sub (fun k => (1/s) * Real.log (a + (k:ℝ)*s)) m
    have hFbound : (1/s) * Real.log (a + (m:ℝ)*s) - (1/s) * Real.log (a + ((0:ℕ):ℝ)*s)
        ≤ (1/s) * Real.log ((a + ((m+1:ℕ):ℝ)*s) / a) := by
      have h0 : a + ((0:ℕ):ℝ)*s = a := by rw [Nat.cast_zero, zero_mul, add_zero]
      rw [h0]
      rw [Real.log_div (x := a + ((m+1:ℕ):ℝ)*s) (y := a) (ne_of_gt (by positivity)) (ne_of_gt ha)]
      have hle : Real.log (a + (m:ℝ)*s) ≤ Real.log (a + ((m+1:ℕ):ℝ)*s) := by
        apply Real.log_le_log (by positivity)
        have hm : (m:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ m
        nlinarith [hs]
      have := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 1/s)
      linarith
    have hsum := htail.trans hFbound
    linarith

end Work.PARIMPL2.Direct
