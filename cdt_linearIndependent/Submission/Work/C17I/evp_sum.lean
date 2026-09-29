import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.evp_add_mul

/-!
# Area C17I — `evp` commutes with finite sums

`evp f z = ∑' n, (coeff n f : ℂ) * z ^ n` (see `Submission.Work.CPull.defs`).

For a finite family `g : ι → ℚ⟦X⟧` whose coefficient series are each summable at `z`, the
evaluation of the finite sum is the finite sum of the evaluations:

`evp (∑ i ∈ s, g i) z = ∑ i ∈ s, evp (g i) z`.

The proof is a direct instance of `Summable.tsum_finsetSum`: `PowerSeries.coeff n` is additive,
so the `n`-th coefficient of `∑ i ∈ s, g i` is `∑ i ∈ s, coeff n (g i)`, and `tsum` of a finite
sum of summable series is the finite sum of the `tsum`s.
-/

namespace Work.C17I

theorem evp_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℚ) (z : ℂ)
    (h : ∀ i ∈ s, Summable fun n : ℕ => ((PowerSeries.coeff n (g i) : ℚ) : ℂ) * z ^ n) :
    Work.CPull.evp (∑ i ∈ s, g i) z = ∑ i ∈ s, Work.CPull.evp (g i) z := by
  -- The `n`-th coefficient of the finite sum is the finite sum of the coefficients.
  have hcoeff : ∀ n : ℕ, ((PowerSeries.coeff n (∑ i ∈ s, g i) : ℚ) : ℂ) * z ^ n
      = ∑ i ∈ s, ((PowerSeries.coeff n (g i) : ℚ) : ℂ) * z ^ n := by
    intro n
    rw [map_sum]
    push_cast
    rw [Finset.sum_mul]
  simp only [Work.CPull.evp]
  rw [tsum_congr hcoeff]
  rw [Summable.tsum_finsetSum h]

end Work.C17I
