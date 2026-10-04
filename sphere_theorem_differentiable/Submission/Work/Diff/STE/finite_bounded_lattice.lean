import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- A single integer whose square is at most `R` lies in a fixed bounded interval. -/
private lemma finite_int_sq_le (R : ℝ) : ({m : ℤ | (m : ℝ) ^ 2 ≤ R}).Finite := by
  have hsub : {m : ℤ | (m : ℝ) ^ 2 ≤ R} ⊆
      Set.Icc (-(⌈max R 0⌉ + 1)) (⌈max R 0⌉ + 1) := by
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm
    have hsq : ((m : ℝ)) ^ 2 ≤ max R 0 := le_trans hm (le_max_left _ _)
    have habs : |(m : ℝ)| ≤ max R 0 + 1 := by
      by_contra h
      rw [not_le] at h
      have h1 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
      have := abs_nonneg (m : ℝ)
      nlinarith [sq_abs (m : ℝ)]
    have hNge : max R 0 + 1 ≤ ((⌈max R 0⌉ + 1 : ℤ) : ℝ) := by
      have := Int.le_ceil (max R 0)
      push_cast
      linarith
    have hfin : |(m : ℝ)| ≤ (((⌈max R 0⌉ + 1 : ℤ) : ℝ)) := le_trans habs hNge
    rw [abs_le] at hfin
    simp only [Set.mem_Icc]
    exact ⟨by exact_mod_cast hfin.1, by exact_mod_cast hfin.2⟩
  exact Set.Finite.subset (Set.finite_Icc _ _) hsub

theorem finite_bounded_lattice {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℝ) :
    {k : ι → ℤ | ∑ i, ((k i : ℝ)) ^ 2 ≤ R}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.pi' (κ := fun _ : ι => ℤ) (t := fun _ => {m : ℤ | (m : ℝ) ^ 2 ≤ R})
      (fun _ => finite_int_sq_le R)) ?_
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk ⊢
  exact fun i =>
    le_trans (Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i)) hk

end Work.Diff.STE
