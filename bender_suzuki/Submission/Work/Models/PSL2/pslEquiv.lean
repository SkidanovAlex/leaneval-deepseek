import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SL(2, 2ⁿ) ≅ PSL(2, 2ⁿ)`

For a field `F` of characteristic `2`, the only scalar matrix in `SL(2,F)` is the identity
(the scalar `λ` must satisfy `λ² = 1`, and in characteristic `2` this forces `λ = 1`).
Hence `Z(SL(2,F)) = 1` and the quotient map `SL(2,F) → PSL(2,F) = SL(2,F)/Z(SL(2,F))`
is an isomorphism.  Specialising to `F = GF(2ⁿ)` gives the stated equivalence.
-/

namespace Work.Models.PSL2

open Matrix

/-- The center of `SL(2,F)` is trivial when `F` has characteristic `2`. -/
theorem center_SL2_eq_bot (F : Type*) [Field F] [CharP F 2] :
    Subgroup.center (Work.Models.SL2 F) = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  rw [Subgroup.mem_bot]
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hscalar⟩ := hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.mp hr2 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  apply Subtype.ext
  rw [← hscalar, hr1]
  simp [Matrix.scalar_apply]

theorem pslEquiv (n : ℕ) :
    Nonempty (Work.Models.SL2 (GaloisField 2 n) ≃* LeanEval.GroupTheory.Defs.PSL2Model n) := by
  have hc : Subgroup.center (Work.Models.SL2 (GaloisField 2 n)) = ⊥ :=
    center_SL2_eq_bot (GaloisField 2 n)
  exact ⟨(QuotientGroup.quotientBot (G := Work.Models.SL2 (GaloisField 2 n))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)⟩

end Work.Models.PSL2
