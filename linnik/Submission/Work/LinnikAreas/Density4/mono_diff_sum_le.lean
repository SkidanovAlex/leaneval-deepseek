import Mathlib

namespace Work.LinnikAreas.Density4

/-- If `c` is nondecreasing on the interval `[A+1, B]` and `w ≤ 1` pointwise, the weighted sum of
the successive differences of `c` against `w` is at most `c B - c A`. -/
theorem mono_diff_sum_le (c w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B)
    (hcmono : ∀ n, A + 1 ≤ n → n ≤ B → c (n - 1) ≤ c n)
    (hw1 : ∀ n, w n ≤ 1) :
    ∑ n ∈ Finset.Ico (A + 1) (B + 1), (c n - c (n - 1)) * w n ≤ c B - c A := by
  have hterm : ∀ n ∈ Finset.Ico (A + 1) (B + 1),
      (c n - c (n - 1)) * w n ≤ c n - c (n - 1) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnn : 0 ≤ c n - c (n - 1) := sub_nonneg.mpr (hcmono n hn.1 (by omega))
    calc (c n - c (n - 1)) * w n ≤ (c n - c (n - 1)) * 1 :=
          mul_le_mul_of_nonneg_left (hw1 n) hnn
      _ = c n - c (n - 1) := mul_one _
  calc ∑ n ∈ Finset.Ico (A + 1) (B + 1), (c n - c (n - 1)) * w n
      ≤ ∑ n ∈ Finset.Ico (A + 1) (B + 1), (c n - c (n - 1)) := Finset.sum_le_sum hterm
    _ = ∑ i ∈ Finset.Ico A B, (c (i + 1) - c i) := by
          rw [← Finset.sum_Ico_add' (fun x => c x - c (x - 1)) A B 1]
          exact Finset.sum_congr rfl (fun x _ => by simp)
    _ = c B - c A := Finset.sum_Ico_sub c hAB

end Work.LinnikAreas.Density4
