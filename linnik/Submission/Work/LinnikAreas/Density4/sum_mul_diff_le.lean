import Mathlib
import Submission.Work.LinnikAreas.Density4.abel_identity
import Submission.Work.LinnikAreas.Density4.mono_diff_sum_le

namespace Work.LinnikAreas.Density4

/-- Abel-type bound for a weighted sum of the successive differences of a sequence `w` lying in
`[0,1]`, with a nondecreasing weight `c`: `Σ_{A ≤ n ≤ B} c n (w n - w (n+1)) ≤ c B`.
(Exact telescoping: the sum equals `c A w A - c B w (B+1) + Σ_{A<n≤B} (c n - c (n-1)) w n`.) -/
theorem sum_mul_diff_le {c w : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B + 1)
    (hc0 : 0 ≤ c A) (hcB : 0 ≤ c B)
    (hcmono : ∀ n, A + 1 ≤ n → n ≤ B → c (n - 1) ≤ c n)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    ∑ n ∈ Finset.Ico A (B + 1), c n * (w n - w (n + 1)) ≤ c B := by
  rcases eq_or_lt_of_le hAB with h | h
  · -- `A = B + 1`: the sum is empty.
    rw [← h]
    simp only [Finset.Ico_self, Finset.sum_empty]
    exact hcB
  · -- `A ≤ B`: telescope with Abel summation, then bound termwise.
    have hAB' : A ≤ B := by omega
    rw [abel_identity c w hAB']
    have h2 := mono_diff_sum_le c w hAB' hcmono hw1
    have h3 : c A * w A ≤ c A := by nlinarith [hw1 A, hc0]
    have h4 : 0 ≤ c B * w (B + 1) := mul_nonneg hcB (hw0 (B + 1))
    linarith

end Work.LinnikAreas.Density4
