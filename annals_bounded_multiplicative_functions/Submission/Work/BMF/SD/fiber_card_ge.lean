import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Pigeonhole ("average of the fibers"): if every value `f d` for `d ∈ D` lies in
`[1, B]`, then some fiber of `f` restricted to `D` has cardinality at least
`#D / B`. -/
theorem fiber_card_ge (D : Finset ℕ) (B : ℕ) (f : ℕ → ℕ) (hB : 1 ≤ B)
    (hlo : ∀ d ∈ D, 1 ≤ f d) (hhi : ∀ d ∈ D, f d ≤ B) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ B ∧
      (D.card : ℝ) / (B : ℝ) ≤ ((D.filter (fun d => f d = j)).card : ℝ) := by
  classical
  by_contra h
  push Not at h
  -- the fibers of `f` over the value range `[1, B]` partition `D`
  have hsum_nat : D.card = ∑ j ∈ Finset.Icc 1 B, (D.filter (fun d => f d = j)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro d hd
    simpa only [Finset.mem_coe, Finset.mem_Icc] using
      (show 1 ≤ f d ∧ f d ≤ B from ⟨hlo d hd, hhi d hd⟩)
  have hsumR :
      ∑ j ∈ Finset.Icc 1 B, ((D.filter (fun d => f d = j)).card : ℝ) = (D.card : ℝ) := by
    rw [hsum_nat]
    push_cast
    ring
  have hScard : (Finset.Icc 1 B).card = B := by rw [Nat.card_Icc]; omega
  have hbne : (B : ℝ) ≠ 0 := by positivity
  -- the "total" of the average bound over the B fibers is exactly `#D`
  have hbound : ∑ j ∈ Finset.Icc 1 B, ((D.card : ℝ) / (B : ℝ)) = (D.card : ℝ) := by
    rw [Finset.sum_const, hScard, nsmul_eq_mul]
    field_simp
  have hne : (Finset.Icc 1 B).Nonempty := ⟨1, by simp [hB]⟩
  -- if every fiber were strictly smaller than the average, their sum would be too
  have hlt : ∑ j ∈ Finset.Icc 1 B, ((D.filter (fun d => f d = j)).card : ℝ) <
             ∑ j ∈ Finset.Icc 1 B, ((D.card : ℝ) / (B : ℝ)) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact h j hj.1 hj.2
  have hcontra : (D.card : ℝ) < (D.card : ℝ) := by
    calc (D.card : ℝ)
        = ∑ j ∈ Finset.Icc 1 B, ((D.filter (fun d => f d = j)).card : ℝ) := hsumR.symm
      _ < ∑ j ∈ Finset.Icc 1 B, ((D.card : ℝ) / (B : ℝ)) := hlt
      _ = (D.card : ℝ) := hbound
  exact lt_irrefl _ hcontra

end Work.BMF.SD
