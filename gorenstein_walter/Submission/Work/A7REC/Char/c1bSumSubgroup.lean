import Mathlib
import Submission.Work.A7REC.Char.c1bLib
import Submission.OddOrder.GroupTheory.RepresentationTheory.Clifford

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory

/-- **The sum of an irreducible character over a subgroup is a multiple of the subgroup
order.**  For any subgroup `H ≤ G` and `χ ∈ Irr G`, the sum `∑_{h ∈ H} χ(h)` equals `|H| · m`
with `m` the multiplicity of the trivial character of `H` in `Res_H^G χ`,
`m = ⟨Res_H^G χ, 1_H⟩_H = |H|⁻¹ ∑_{h ∈ H} χ(h)`, a non-negative integer
(`ClassFunction.restrictionMultiplicity_natCast` applied to `θ = 1_H`). -/
theorem c1bSumSubgroup {G : Type} [Group G] [Finite G] (H : Subgroup G) [Fintype ↥H]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) :
    ∃ m : ℕ, ∑ h : ↥H, (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) h
      = (Nat.card ↥H : ℂ) * (m : ℂ) := by
  classical
  have hInv : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The multiplicity of the trivial character of `H` in `Res_H^G χ` is a natural number.
  obtain ⟨k, hk⟩ := ClassFunction.restrictionMultiplicity_natCast (H := H)
    (IrreducibleCharacter.isIrreducible χ) trivialClassFunction_isIrreducible
  refine ⟨k, ?_⟩
  rw [ClassFunction.restrictionMultiplicity_def, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum] at hk
  -- Unfold the restricted inner product into `|H|⁻¹ · ∑_{h ∈ H} χ(h)`.
  have hsum : (∑ h : ↥H,
        ClassFunction.restrict H (χ : ClassFunction G ℂ) h
          * star (trivialClassFunction ↥H h))
      = ∑ h : ↥H, (χ : ClassFunction G ℂ) h := by
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [ClassFunction.restrict_apply, trivialClassFunction_apply, star_one, mul_one]
  rw [hsum] at hk
  -- Multiply by `|H|`.
  have h2 := congrArg (fun z : ℂ => (Nat.card ↥H : ℂ) * z) hk
  rw [← mul_assoc, mul_invOf_self, one_mul] at h2
  exact h2

end Work.A7REC.Char
