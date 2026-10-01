import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Icc_inv_le_one

namespace Work.LinnikAreas.Density4

/--

Sum over `e ∈ [1, ⌊2X⌋]` of `1/e` restricted to those `e` with `d * e` lying in the
half-open interval `(⌊X⌋, ⌊2X⌋]`.  All such `e` have `d * e > X` and `d * e ≤ 2X`, so
they form a set of integers contained in a multiplicative window `[m, 2m-1]` of length
`m`, in which every reciprocal is at most `1/m`; the whole sum is therefore at most `1`.
-/
theorem inner_indicator_le_one (X : ℝ) (hX : 0 < X) (d : ℕ) (hd : 1 ≤ d) :
    ∑ e ∈ Finset.Icc 1 (Nat.floor (2 * X)),
      (if d * e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)) then (1 : ℝ) / (e : ℝ) else 0) ≤ 1 := by
  set S : Finset ℕ := (Finset.Icc 1 (Nat.floor (2 * X))).filter
      (fun e => d * e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X))) with hS
  have hsum : (∑ e ∈ Finset.Icc 1 (Nat.floor (2 * X)),
      (if d * e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)) then (1 : ℝ) / (e : ℝ) else 0))
      = ∑ e ∈ S, (1 : ℝ) / (e : ℝ) := by
    rw [hS, Finset.sum_filter]
  rw [hsum]
  rcases Finset.eq_empty_or_nonempty S with hSempty | hSne
  · rw [hSempty]; simp
  · set m : ℕ := S.min' hSne with hm
    have hmS : m ∈ S := Finset.min'_mem S hSne
    have hmf := Finset.mem_filter.mp hmS
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmf.1).1
    have hmcond : Nat.floor X < d * m ∧ d * m ≤ Nat.floor (2 * X) := Finset.mem_Ioc.mp hmf.2
    have hsub : S ⊆ Finset.Icc m (2 * m - 1) := by
      intro e he
      rw [Finset.mem_Icc]
      refine ⟨Finset.min'_le S e he, ?_⟩
      have hef := Finset.mem_filter.mp he
      have hecond : Nat.floor X < d * e ∧ d * e ≤ Nat.floor (2 * X) := Finset.mem_Ioc.mp hef.2
      have hdm_gt_X : X < (d * m : ℝ) := by
        have h1 : (Nat.floor X : ℝ) + 1 ≤ (d * m : ℝ) := by
          have : Nat.floor X + 1 ≤ d * m := hmcond.1
          exact_mod_cast this
        have h2 : X < (Nat.floor X : ℝ) + 1 := Nat.lt_floor_add_one X
        linarith
      have hde_le : (d * e : ℝ) ≤ 2 * X := by
        have h1 : (d * e : ℝ) ≤ (Nat.floor (2 * X) : ℝ) := by exact_mod_cast hecond.2
        have h2 : (Nat.floor (2 * X) : ℝ) ≤ 2 * X := Nat.floor_le (by positivity)
        linarith
      have hde_lt : (d * e : ℝ) < 2 * (d * m : ℝ) := by linarith
      have hltN : d * e < 2 * (d * m) := by exact_mod_cast hde_lt
      have he_lt : e < 2 * m := by
        have h4 : d * e < d * (2 * m) := by
          rwa [show 2 * (d * m) = d * (2 * m) by ring] at hltN
        exact (Nat.mul_lt_mul_left (by omega : 0 < d)).mp h4
      omega
    have hle : ∑ e ∈ S, (1 : ℝ) / (e : ℝ) ≤ ∑ e ∈ Finset.Icc m (2 * m - 1), (1 : ℝ) / (e : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi hit
      exact one_div_nonneg.mpr (Nat.cast_nonneg i)
    have hbound := sum_Icc_inv_le_one m hm1
    linarith

end Work.LinnikAreas.Density4
