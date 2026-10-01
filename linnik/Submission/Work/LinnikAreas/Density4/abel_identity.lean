import Mathlib

namespace Work.LinnikAreas.Density4

/-- Abel summation identity: the weighted sum of successive differences of `w` over `Ico A (B+1)`
telescopes into a boundary term plus a sum of the successive differences of the weight `c`. -/
theorem abel_identity (c w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ico A (B + 1), c n * (w n - w (n + 1))
      = c A * w A - c B * w (B + 1)
        + ∑ n ∈ Finset.Ico (A + 1) (B + 1), (c n - c (n - 1)) * w n := by
  -- Prove the statement for a fixed left endpoint `A` by induction on the right endpoint.
  let P : (n : ℕ) → A ≤ n → Prop := fun n _ =>
    ∑ k ∈ Finset.Ico A (n + 1), c k * (w k - w (k + 1))
      = c A * w A - c n * w (n + 1)
        + ∑ k ∈ Finset.Ico (A + 1) (n + 1), (c k - c (k - 1)) * w k
  have h : P B hAB := by
    refine Nat.le_induction ?base ?step B hAB
    · -- `B = A`: the sum has a single term and the second sum is empty.
      simp only [P]
      rw [Finset.sum_Ico_succ_top (a := A) (b := A) (le_refl A)
        (fun k => c k * (w k - w (k + 1)))]
      simp
      ring
    · -- Inductive step: peel off the last term of each sum.
      intro k hk ih
      simp only [P] at ih ⊢
      rw [Finset.sum_Ico_succ_top (a := A) (b := k + 1) (by omega)
        (fun n => c n * (w n - w (n + 1)))]
      rw [Finset.sum_Ico_succ_top (a := A + 1) (b := k + 1) (by omega)
        (fun n => (c n - c (n - 1)) * w n)]
      rw [ih]
      have hk1 : k + 1 - 1 = k := by omega
      rw [hk1]
      ring
  simpa only [P] using h

end Work.LinnikAreas.Density4
