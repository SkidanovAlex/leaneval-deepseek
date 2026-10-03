import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.rk_toeplitzSeries_ge_of_leading_general

namespace Work.ORHughesFree.NaturalExtension

/-- For a skew Laurent series `p` whose coefficients vanish below `i` and whose `i`-th
coefficient is `a`, the normalized rank of the `(n+1) × (n+1)` Toeplitz matrix of `p` is
eventually at least the normalized "leading ratio" `((n+1) - max i (-i))/(n+1) * rk a`.

This is `rk_toeplitzSeries_ge_of_leading_general` at `N = n+1`, valid for all `n` with
`max i (-i) < n+1`, divided by the positive number `n + 1`. -/
theorem eventually_leading_le_toeplitz {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : Work.ORHughesFree.SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (p : Work.ORHughesFree.SkewLaurentSeries U) (i : ℤ) (a : U) (hi : p.1 i = a)
    (hlo : ∀ k : ℤ, k < i → p.1 k = 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((((n+1 : ℤ) - max i (-i) : ℤ) : ℝ) / ((n+1 : ℕ) : ℝ)) *
          rk.rk 1 1 (Work.ORHughesFree.oneByOne a)
        ≤ rk.rk (n+1) (n+1)
            (Work.ORHughesFree.NaturalExtension.toeplitzSeries (n+1) p) / ((n+1 : ℕ) : ℝ) := by
  classical
  rw [Filter.eventually_atTop]
  refine ⟨(max i (-i)).toNat, fun n hn => ?_⟩
  have hmax : 0 ≤ max i (-i) := by
    rcases le_total 0 i with h | h
    · exact le_trans h (le_max_left i (-i))
    · exact le_trans (by omega : (0:ℤ) ≤ -i) (le_max_right i (-i))
  have hA : (((max i (-i)).toNat : ℕ) : ℤ) = max i (-i) := Int.toNat_of_nonneg hmax
  have hcast : (((max i (-i)).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hN : max i (-i) < ((n+1 : ℕ) : ℤ) := by
    rw [← hA]; push_cast; omega
  have hge := rk_toeplitzSeries_ge_of_leading_general rk hτ p i a hi hlo (n+1) hN
  have hc : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
  have h2 : ((((n+1 : ℕ) : ℤ) - max i (-i) : ℤ) : ℝ) * rk.rk 1 1 (Work.ORHughesFree.oneByOne a)
      / ((n+1 : ℕ) : ℝ)
      ≤ rk.rk (n+1) (n+1) (Work.ORHughesFree.NaturalExtension.toeplitzSeries (n+1) p)
        / ((n+1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hge hc
  convert h2 using 1
  push_cast; ring

end Work.ORHughesFree.NaturalExtension
