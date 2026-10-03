import Mathlib
import Submission.Work.ORLocInd.FKS.SL2Defs

namespace Work.ORLocInd.FKS

/-- The ping-pong sets `pset p j` have a common exterior point: the point `-(p+2) + I` of `ℍ` has
real part at most `-2`, while every `pset p j` is contained in the half plane `Re > -1`. -/
theorem exists_notMem_pset (p : ℕ) :
    ∃ x : UpperHalfPlane, ∀ j : ℕ, x ∉ Work.ORLocInd.FKS.pset p j := by
  -- The witness is the point `-(p+2) + I`, whose imaginary part is `1 > 0`.
  have hz_im : 0 < (-((p : ℂ) + 2) + Complex.I).im := by
    simp [Complex.add_im, Complex.I_im]
  refine ⟨⟨-((p : ℂ) + 2) + Complex.I, hz_im⟩, ?_⟩
  intro j hj
  -- The distance from the witness to the cusp `p*j` is at least its real part's absolute value,
  -- which equals `p + 2 + p*j ≥ 2 > 1`.
  have hj' : ‖(-((p : ℂ) + 2) + Complex.I) - (p * j : ℂ)‖ < 1 := hj
  have hre : ((-((p : ℂ) + 2) + Complex.I) - (p * j : ℂ)).re = -((p : ℝ) + 2 + p*j) := by
    simp
    ring
  have hnn : (0 : ℝ) ≤ (p : ℝ) * (j : ℝ) :=
    mul_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ (p : ℝ))
      (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  have habs : |((-((p : ℂ) + 2) + Complex.I) - (p * j : ℂ)).re| = (p : ℝ) + 2 + p*j := by
    rw [hre, abs_of_nonpos (by linarith), neg_neg]
  have hnorm : (2 : ℝ) ≤ ‖(-((p : ℂ) + 2) + Complex.I) - (p * j : ℂ)‖ :=
    le_trans (by rw [habs]; linarith) (Complex.abs_re_le_norm _)
  linarith

end Work.ORLocInd.FKS
