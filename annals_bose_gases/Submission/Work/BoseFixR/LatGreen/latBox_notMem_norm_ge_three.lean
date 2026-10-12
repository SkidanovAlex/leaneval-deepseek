import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.LatGreen.LatGreenParsevalBDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

theorem latBox_notMem_norm_ge_three {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ i : Fin 3, |u i| ≤ 2) {n : Fin 3 → ℤ} (hn : n ∉ Work.BoseFixR.LatGreen.latBox) :
    3 ≤ ‖u - Work.BoseFixR.LatGreen.latVec n‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ∉ Finset.Icc (-4 : ℤ) 4 := by
    by_contra h
    exact hn (mem_latBox.mpr fun i => by simpa using not_not.mp (not_exists.mp h i))
  simp only [Finset.mem_Icc, not_and, not_le] at hi
  have h4 : (4 : ℤ) < n i ∨ n i < -4 := by
    by_cases h : (-4 : ℤ) ≤ n i
    · exact Or.inl (hi h)
    · exact Or.inr (by omega)
  have h5 : (5 : ℤ) ≤ |n i| := by
    rcases h4 with h | h
    · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ n i)]; omega
    · rw [abs_of_nonpos (by omega : n i ≤ 0)]; omega
  have h5R : (5 : ℝ) ≤ |(n i : ℝ)| := by
    calc (5 : ℝ) = ((5 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast h5
      _ = |((n i : ℤ) : ℝ)| := by rw [Int.cast_abs]
      _ = |(n i : ℝ)| := by norm_num
  have hdiff : |(n i : ℝ)| - |u i| ≤ |u i - (n i : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub (n i : ℝ) (u i)
    rw [abs_sub_comm (n i : ℝ) (u i)] at h
    exact h
  have h3 : (3 : ℝ) ≤ |u i - (n i : ℝ)| := by
    have hui := hu i
    linarith
  have hle : |u i - (n i : ℝ)| ≤ ‖u - latVec n‖ := by
    have := PiLp.norm_apply_le (u - latVec n) i
    simpa [latVec, Real.norm_eq_abs] using this
  linarith

end Work.BoseFixR.LatGreen
