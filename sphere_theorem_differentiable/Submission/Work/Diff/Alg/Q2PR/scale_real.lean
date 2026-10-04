import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PR

/-- For any complex number `s` there is a nonzero complex `l` with `l * l * s` real. -/
theorem scale_real (s : ℂ) : ∃ l : ℂ, l ≠ 0 ∧ (l * l * s).im = 0 := by
  by_cases hs : s = 0
  · exact ⟨1, one_ne_zero, by simp [hs]⟩
  · obtain ⟨l, hl⟩ := Complex.isSquare (starRingEnd ℂ s)
    refine ⟨l, ?_, ?_⟩
    · intro h
      apply hs
      have h2 : (starRingEnd ℂ) s = 0 := by rw [hl, h]; ring
      exact (starRingEnd ℂ).map_eq_zero_iff.mp h2
    · have h3 : l * l * s = (starRingEnd ℂ) s * s := by rw [hl]
      rw [h3, mul_comm, Complex.mul_conj]
      simp

end Work.Diff.Alg.Q2PR
