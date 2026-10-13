import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

/-- **Subadditivity of the `ℋ^k`-integrand for a difference**: if every mixed derivative
`D_z^j D_θ^i G` (`j + i ≤ k`) is pointwise the difference of the corresponding derivatives of
`A` and `B`, then

`HkIntegrand α k G z θ ≤ 2 · HkIntegrand α k A z θ + 2 · HkIntegrand α k B z θ`.

This is purely algebraic: `HkIntegrand` is a sum of squares of the finitely many slots
(`D_z^i G · w/sin(2θ)^{η/2}` for `0 ≤ i ≤ k`, and `D_z^j D_θ^i G · W` for `1 ≤ i`, `i + j ≤ k`),
and each slot of `G` is the difference of the corresponding slots, so
`(x - y)² ≤ 2x² + 2y²` applied slotwise and summed gives the claim.  The `D_z`-slots are the
`i = 0` case of the mixed slots, so the single hypothesis `hsub` covers both sums. -/
theorem HkIntegrand_sub_le {α : ℝ} {k : ℕ} {G A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hsub : ∀ j i : ℕ, j + i ≤ k →
      Work.Spaces.mixed j i G z θ = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ) :
    Work.Spaces.HkIntegrand α k G z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k A z θ + 2 * Work.Spaces.HkIntegrand α k B z θ := by
  -- the `D_z`-slots are the mixed slots with `i = 0`
  have hdz : ∀ i : ℕ, i ≤ k → Work.Spaces.DzIter i G z θ
      = Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ := by
    intro i hi
    have h := hsub i 0 (by omega)
    simpa only [Work.Spaces.mixed_zero_right] using h
  -- the elementary square estimate `(x - y)² c² ≤ 2 (xc)² + 2 (yc)²`
  have hsq : ∀ x y c : ℝ, ((x - y) * c) ^ 2 ≤ 2 * (x * c) ^ 2 + 2 * (y * c) ^ 2 := by
    intro x y c
    nlinarith [sq_nonneg ((x + y) * c)]
  -- the `D_z`-sum
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i G z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i A z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i B z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i G z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ 2 * (Work.Spaces.DzIter i A z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
            + 2 * (Work.Spaces.DzIter i B z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      intro i hi
      have hik : i ≤ k := by
        have := Finset.mem_range.mp hi; omega
      rw [hdz i hik]
      exact hsq _ _ _
    calc (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i G z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i A z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i B z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) :=
          Finset.sum_le_sum hterm
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i A z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i B z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the mixed sum
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    have hinner : ∀ i ∈ Finset.range (k + 1),
        (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 2 * (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i hi
      have hterm : ∀ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            + 2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
        intro j hj
        split_ifs with hc
        · rw [hsub j i (by omega)]
          exact hsq _ _ _
        · norm_num
      calc (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ j ∈ Finset.range (k + 1),
              (2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
                + 2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            Finset.sum_le_sum hterm
        _ = 2 * (∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            + 2 * (∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum hinner
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Work.Spaces.HkIntegrand]
  linarith [hS1, hS2]

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
