import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The slowly varying inequality for the weight `wt`

`wt k = 1 + Σᵢ kᵢ²`.  For coefficient families on `ℤᵈ` one needs the standard bound
`⟨k⟩ ≤ 2⟨l⟩⟨k - l⟩`, i.e. here `wt k ≤ 2 * (wt l * wt (k - l))`: this is where the
(squared) weight interacts with the group structure of `ℤᵈ`, and it is what makes the
convolution estimates of Layer A go through.

The proof is the triangle-type inequality `(a + b)² ≤ 2a² + 2b²` summed over the
coordinates, together with `1 + 2A + 2B ≤ 2 (1 + A) (1 + B)` for `A, B ≥ 0`.
-/

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι]

/-- `(a + b)² ≤ 2 a² + 2 b²` for real numbers. -/
private lemma sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The slowly varying inequality for `wt`: `wt k ≤ 2 * (wt l * wt (k - l))`. -/
lemma wt_le_two_mul (k l : ι → ℤ) : wt k ≤ 2 * (wt l * wt (k - l)) := by
  classical
  have hcoord : ∀ i : ι,
      ((k i : ℤ) : ℝ) ^ 2 ≤ 2 * ((l i : ℝ) ^ 2 + (((k - l) i : ℤ) : ℝ) ^ 2) := by
    intro i
    have hkl : ((k - l) i : ℤ) = k i - l i := Pi.sub_apply k l i
    have hcast : (k i : ℝ) = (l i : ℝ) + (((k - l) i : ℤ) : ℝ) := by
      rw [hkl]; push_cast; ring
    rw [hcast]
    nlinarith [sq_add_le (l i : ℝ) (((k - l) i : ℤ) : ℝ)]
  have hsum : ∑ i, ((k i : ℤ) : ℝ) ^ 2
      ≤ 2 * (∑ i, ((l i : ℤ) : ℝ) ^ 2) + 2 * (∑ i, (((k - l) i : ℤ) : ℝ) ^ 2) := by
    calc ∑ i, ((k i : ℤ) : ℝ) ^ 2
        ≤ ∑ i, (2 * ((l i : ℝ) ^ 2 + (((k - l) i : ℤ) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = ∑ i, (2 * ((l i : ℤ) : ℝ) ^ 2 + 2 * (((k - l) i : ℤ) : ℝ) ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, 2 * ((l i : ℤ) : ℝ) ^ 2) + ∑ i, 2 * (((k - l) i : ℤ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = 2 * (∑ i, ((l i : ℤ) : ℝ) ^ 2) + 2 * (∑ i, (((k - l) i : ℤ) : ℝ) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  have hA : (0 : ℝ) ≤ ∑ i, ((l i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (0 : ℝ) ≤ ∑ i, (((k - l) i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [wt]
  nlinarith [hsum, hA, hB, mul_nonneg hA hB]

theorem wt_pow_le {ι : Type*} [Fintype ι] (s : ℕ) (k l : ι → ℤ) :
    Work.Diff.STE.wt k ^ s ≤ 2 ^ s * (Work.Diff.STE.wt l ^ s * Work.Diff.STE.wt (k - l) ^ s) := by
  classical
  have hle : Work.Diff.STE.wt k ≤ 2 * (Work.Diff.STE.wt l * Work.Diff.STE.wt (k - l)) :=
    wt_le_two_mul k l
  have hk : (0 : ℝ) ≤ Work.Diff.STE.wt k := le_of_lt (wt_pos k)
  calc Work.Diff.STE.wt k ^ s
      ≤ (2 * (Work.Diff.STE.wt l * Work.Diff.STE.wt (k - l))) ^ s :=
        pow_le_pow_left₀ hk hle s
    _ = 2 ^ s * (Work.Diff.STE.wt l ^ s * Work.Diff.STE.wt (k - l) ^ s) := by
        rw [mul_pow, mul_pow]

end Work.Diff.STE
