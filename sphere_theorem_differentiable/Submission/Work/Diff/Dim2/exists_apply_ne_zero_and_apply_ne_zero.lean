import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

/-- Two nonzero real-valued continuous linear functionals on a real vector space never vanish
simultaneously: there is a single vector on which both are nonzero.  (The space is not assumed
complete or nontrivial; the key point is that a real vector space cannot be the union of the two
proper subspaces `ker φ` and `ker ψ`, which is proved here by the elementary two-parameter
argument: adding a suitable multiple of a vector on which `ψ` does not vanish to a vector on
which `φ` does not vanish kills neither.) -/
theorem exists_apply_ne_zero_and_apply_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ ψ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ∃ e : E, φ e ≠ 0 ∧ ψ e ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a : E, φ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (ContinuousLinearMap.ext fun x => by simp [h x])
  obtain ⟨b, hb⟩ : ∃ b : E, ψ b ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (ContinuousLinearMap.ext fun x => by simp [h x])
  by_cases hba : ψ a = 0
  · -- `ψ` vanishes at `a`: perturb `a` by a multiple of `b`.
    by_cases h1 : φ a + φ b = 0
    · have hpb : φ b ≠ 0 := by
        intro hzb
        rw [hzb, add_zero] at h1
        exact ha h1
      refine ⟨a + (2 : ℝ) • b, ?_, ?_⟩
      · have h2 : φ (a + (2 : ℝ) • b) = φ b := by
          simp only [map_add, map_smul, smul_eq_mul]
          linarith
        rw [h2]; exact hpb
      · have h3 : ψ (a + (2 : ℝ) • b) = 2 * ψ b := by
          simp only [map_add, map_smul, smul_eq_mul, hba, zero_add]
        rw [h3]; exact mul_ne_zero two_ne_zero hb
    · refine ⟨a + b, ?_, ?_⟩
      · have h2 : φ (a + b) = φ a + φ b := by simp only [map_add]
        rw [h2]; exact h1
      · have h3 : ψ (a + b) = ψ b := by simp only [map_add, hba, zero_add]
        rw [h3]; exact hb
  · exact ⟨a, ha, hba⟩

end Work.Diff.Dim2
