import Mathlib

namespace Work.Mostow

/-- A map `φ : ℝ → ℝ` that preserves all pairwise distances is an affine isometry:
it is either a translation or a reflection-translation `s ↦ -s + c`. -/
theorem affineIsometryReal (φ : ℝ → ℝ) (h : ∀ s t : ℝ, |φ s - φ t| = |s - t|) :
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ s : ℝ, φ s = ε * s + c := by
  -- ε is determined by the image of `1`, and `φ 0 = c`.
  have h1 : |φ 1 - φ 0| = 1 := by simpa using h 1 0
  have hε : (φ 1 - φ 0 = 1 ∨ φ 1 - φ 0 = -1) := by
    have h1' : |φ 1 - φ 0| = |(1:ℝ)| := by simpa using h1
    rcases abs_eq_abs.mp h1' with hh | hh
    · left; exact hh
    · right; exact hh
  refine ⟨φ 1 - φ 0, φ 0, hε, fun s => ?_⟩
  -- Distance equalities squared, compared via `nlinarith`.
  have hs1 : |φ s - φ 0| = |s| := by simpa using h s 0
  have hs2 : |φ s - φ 1| = |s - 1| := by simpa using h s 1
  have e1 : (φ s - φ 0)^2 = s^2 := by
    have := congrArg (fun x : ℝ => x^2) hs1
    rwa [sq_abs, sq_abs] at this
  have e2 : (φ s - φ 1)^2 = (s - 1)^2 := by
    have := congrArg (fun x : ℝ => x^2) hs2
    rwa [sq_abs, sq_abs] at this
  have he : (φ 1 - φ 0)^2 = 1 := by
    rcases hε with hh | hh <;> rw [hh] <;> norm_num
  nlinarith [e1, e2, he]

end Work.Mostow
