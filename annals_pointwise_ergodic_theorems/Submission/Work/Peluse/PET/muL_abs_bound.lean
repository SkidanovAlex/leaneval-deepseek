/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.MuL.muL_tsum
import Submission.Work.Peluse.MuL.muL_eq_zero

/-!
# The first moment of Peluse's weight `μ_L` on the interval `[-L, L]`

Peluse's weight `μ_L(h) = #{h₁, h₂ ∈ [L] : h₁ - h₂ = h}/L²` (`Work.Peluse.muL`) is the law of the
difference of two independent uniform points of `[L] = {1, …, L}`.  This module proves the
elementary first-moment bound on the symmetric interval `[-L, L]`:

`∑_{a ∈ [-L, L]} μ_L(a) · |a| ≤ L`   (`Work.Peluse.PET.muL_abs_bound`).

The proof does not need the exact value of the sum.  Two facts suffice, both already available in
the workspace:

* `μ_L` is nonnegative (it is a cardinality times the nonnegative factor `1/L²`);
* `μ_L` has total mass one: `∑_h μ_L(h) = 1` (`Work.Peluse.MuL.muL_tsum`), and since `μ_L`
  vanishes off `[1-L, L-1] ⊆ [-L, L]` (`Work.Peluse.MuL.muL_eq_zero`), the mass on `[-L, L]`
  is also one.

Then `|a| ≤ L` for every `a ∈ [-L, L]` gives the termwise bound `μ_L(a)|a| ≤ L · μ_L(a)`, and
summing yields `L · 1 = L`.  (The sharper value of the sum is `E|h₁ - h₂| = (L² - 1)/(3L)`, but
only the trivial bound is needed here.)
-/

namespace Work.Peluse.PET

open scoped BigOperators

/-- `μ_L` is nonnegative: it is `(1/L²)` times a cardinality. -/
lemma muL_nonneg (L : ℕ) (a : ℤ) : 0 ≤ Work.Peluse.muL L a := by
  rw [Work.Peluse.muL]
  positivity

/-- The total mass of `μ_L` restricted to the symmetric interval `[-L, L]` is `1`.  This is
`Work.Peluse.MuL.muL_tsum` (`∑_h μ_L(h) = 1`) combined with the fact that `μ_L` is supported in
`[1-L, L-1] ⊆ [-L, L]`. -/
lemma sum_muL_Icc (L : ℕ) (hL : 1 ≤ L) :
    ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a = 1 := by
  have hzero : ∀ a ∉ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a = 0 := by
    intro a ha
    apply Work.Peluse.MuL.muL_eq_zero
    simp only [Finset.mem_Icc, not_and_or, not_le] at ha
    rcases ha with h | h
    · rw [abs_of_neg (by omega : a < 0)]; omega
    · rw [abs_of_pos (by omega : 0 < a)]; omega
  have htsum : (∑' a : ℤ, Work.Peluse.muL L a)
      = ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a :=
    tsum_eq_sum hzero
  rw [← htsum]
  exact Work.Peluse.MuL.muL_tsum L hL

/-- The first moment of `μ_L` on `[-L, L]` is at most `L`:

`∑_{a ∈ [-L, L]} μ_L(a) · |a| ≤ L`.

Since `μ_L` is a probability weight on `[-L, L]` and `|a| ≤ L` there, each term is at most
`L · μ_L(a)` and the sum is at most `L · 1 = L`. -/
theorem muL_abs_bound (L : ℕ) (hL : 1 ≤ L) :
    ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a * |(a : ℝ)| ≤ (L : ℝ) := by
  -- Step 1: `|a| ≤ L` for `a ∈ [-L, L]`, so each summand is at most `L · μ_L(a)`.
  have hterm : ∀ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      Work.Peluse.muL L a * |(a : ℝ)| ≤ Work.Peluse.muL L a * (L : ℝ) := by
    intro a ha
    have habs : |(a : ℝ)| ≤ (L : ℝ) := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
      rw [abs_le]
      exact ⟨by simpa using (show ((-(L : ℤ)) : ℝ) ≤ (a : ℝ) by exact_mod_cast h1),
        by exact_mod_cast h2⟩
    exact mul_le_mul_of_nonneg_left habs (muL_nonneg L a)
  -- Step 2: sum and use that the total mass on `[-L, L]` is one.
  calc ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a * |(a : ℝ)|
      ≤ ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a * (L : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Work.Peluse.muL L a) * (L : ℝ) :=
        (Finset.sum_mul _ _ _).symm
    _ = (L : ℝ) := by rw [sum_muL_Icc L hL, one_mul]

end Work.Peluse.PET
