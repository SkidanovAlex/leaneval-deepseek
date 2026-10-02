import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Telescoping one-step bound: for `0 < a`, `0 < s` and `k : ℕ`,
`1/(a+(k+1)s)^2 ≤ (1/s)*(1/(a+ks) - 1/(a+(k+1)s))`, since the right-hand side
equals `1/((a+ks)(a+(k+1)s))` and `a+ks ≤ a+(k+1)s`. -/
private lemma one_div_sq_step (a s : ℝ) (ha : 0 < a) (hs : 0 < s) (k : ℕ) :
    (1:ℝ) / (a + ((k+1:ℕ):ℝ) * s) ^ 2 ≤
      (1/s) * (1/(a + (k:ℝ)*s) - 1/(a + ((k+1:ℕ):ℝ)*s)) := by
  have hx : 0 < a + (k:ℝ)*s := by positivity
  have hy : 0 < a + ((k+1:ℕ):ℝ)*s := by positivity
  have hxy : a + (k:ℝ)*s ≤ a + ((k+1:ℕ):ℝ)*s := by
    have hk : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ k
    have hk2 := mul_le_mul_of_nonneg_right hk (le_of_lt hs)
    linarith
  have hrw : (1/s) * (1/(a + (k:ℝ)*s) - 1/(a + ((k+1:ℕ):ℝ)*s))
      = 1 / ((a + (k:ℝ)*s) * (a + ((k+1:ℕ):ℝ)*s)) := by
    field_simp
    push_cast
    ring
  rw [hrw]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem sumInvSqLe (a s : ℝ) (n : ℕ) (ha : 0 < a) (hs : 0 < s) :
    (∑ j ∈ Finset.range n, 1 / (a + (j : ℝ) * s) ^ 2) ≤ 1 / a ^ 2 + 1 / (s * a) := by
  rcases n with _ | m
  · simp
    positivity
  · rw [Finset.sum_range_succ']
    have hf0 : (1:ℝ) / (a + ((0:ℕ):ℝ) * s) ^ 2 = 1 / a ^ 2 := by norm_num
    rw [hf0]
    have htail : ∑ k ∈ Finset.range m, (1:ℝ)/(a + ((k+1:ℕ):ℝ)*s)^2 ≤ 1/(s*a) := by
      have key : ∀ k ∈ Finset.range m,
          (1:ℝ)/(a + ((k+1:ℕ):ℝ)*s)^2 ≤
            (1/s) * (1/(a + (k:ℝ)*s) - 1/(a + ((k+1:ℕ):ℝ)*s)) :=
        fun k _ => one_div_sq_step a s ha hs k
      calc ∑ k ∈ Finset.range m, (1:ℝ)/(a + ((k+1:ℕ):ℝ)*s)^2
          ≤ ∑ k ∈ Finset.range m, (1/s) * (1/(a + (k:ℝ)*s) - 1/(a + ((k+1:ℕ):ℝ)*s)) :=
              Finset.sum_le_sum key
        _ = (1/s) * ∑ k ∈ Finset.range m, (1/(a + (k:ℝ)*s) - 1/(a + ((k+1:ℕ):ℝ)*s)) := by
              rw [Finset.mul_sum]
        _ = (1/s) * (1/(a + (0:ℝ)*s) - 1/(a + (m:ℝ)*s)) := by
              congr 1
              simpa using Finset.sum_range_sub' (fun k => (1:ℝ)/(a + (k:ℝ)*s)) m
        _ ≤ 1/(s*a) := by
              have h1 : (1:ℝ)/(a + (m:ℝ)*s) ≤ 1/a :=
                one_div_le_one_div_of_le ha (by
                  have : (0:ℝ) ≤ (m:ℝ)*s := by positivity
                  linarith)
              have h2 : (1:ℝ)/(a + (0:ℝ)*s) = 1/a := by norm_num
              rw [h2]
              have ht : (0:ℝ) ≤ 1/(a + (m:ℝ)*s) := by positivity
              have h3 : (1:ℝ)/a - 1/(a + (m:ℝ)*s) ≤ 1/a := by linarith
              calc (1/s) * (1/a - 1/(a + (m:ℝ)*s))
                  ≤ (1/s) * (1/a) := by
                    apply mul_le_mul_of_nonneg_left h3 (by positivity)
                _ = 1/(s*a) := by field_simp
    linarith

end Work.PARIMPL2.Direct
