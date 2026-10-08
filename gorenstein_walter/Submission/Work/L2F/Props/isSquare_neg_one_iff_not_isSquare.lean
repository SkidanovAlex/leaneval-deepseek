import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Props

/-- In a finite field `F` of odd characteristic, if `-lam` is not a square then `-1` is a
square precisely when `lam` is not.

The proof is a one-line argument with the quadratic character `χ = quadraticChar F`: since
`χ (-lam) = -1` and `χ (-lam) = χ (-1) · χ lam`, we get `χ (-1) · χ lam = -1`, i.e.
`χ (-1) = -χ lam` (both values lie in `{±1}`).  As `χ a = 1` exactly on nonzero squares and
`χ a = -1` exactly on nonsquares, this is the claimed equivalence. -/
theorem isSquare_neg_one_iff_not_isSquare (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (lam : F) (h : ¬ IsSquare (-lam)) :
    IsSquare (-1 : F) ↔ ¬ IsSquare lam := by
  classical
  -- `0` is a square, so `-lam ≠ 0`, hence `lam ≠ 0`.
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    exact h ⟨0, by simp⟩
  have hneg1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  -- Multiplicativity of the quadratic character turns the hypothesis into
  -- `χ (-1) * χ lam = -1`.
  have hmul : quadraticChar F (-1) * quadraticChar F lam = -1 := by
    have h1 : quadraticChar F (-lam) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h
    rwa [show (-lam : F) = -1 * lam by ring, map_mul] at h1
  constructor
  · -- If `-1` is a square then `χ (-1) = 1`, and if `lam` were a square too then
    -- `χ lam = 1`, contradicting `χ (-1) * χ lam = -1`.
    intro hsqneg
    rintro hsqlam
    have hc1 : quadraticChar F (-1) = 1 := (quadraticChar_one_iff_isSquare hneg1).mpr hsqneg
    have hc2 : quadraticChar F lam = 1 := (quadraticChar_one_iff_isSquare hlam0).mpr hsqlam
    rw [hc1, hc2] at hmul
    norm_num at hmul
  · -- If `lam` is not a square then `χ lam = -1`, so `χ (-1) = 1` and `-1` is a square.
    intro hnot
    have hc2 : quadraticChar F lam = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hnot
    rw [hc2] at hmul
    have hc1 : quadraticChar F (-1) = 1 := by linarith
    exact (quadraticChar_one_iff_isSquare hneg1).mp hc1

end Work.L2F.Props
