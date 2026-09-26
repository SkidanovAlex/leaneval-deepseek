/-
# Membership in the odd collapse ideal `(1+z)R`

`z = Rneg = -I` is a central involution of `R = ℂ[SL(2,ℤ)]`, so `R = R₊ × R₋` with
`R₊ = (1+z)R` (`Work.Asymptotics.augIdealOdd`) and `R₋ = (1-z)R`.  Since `z` is central and
`z² = 1`, an element lies in `R₊` exactly when right multiplication by `z` fixes it:

  `A ∈ augIdealOdd ↔ A * Rneg = A`.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Residues.Basic

noncomputable section

namespace Work.Asymptotics

open Work.Kernels

lemma Rneg_comm' (r : R) : Rneg * r = r * Rneg := Work.Residues.Rneg_comm r

lemma Rneg_mul_self' : Rneg * Rneg = (1 : R) := Work.Residues.Rneg_mul_Rneg

lemma Rneg_sub_mul_self : (1 - Rneg) * Rneg = -(1 - Rneg) := by
  rw [sub_mul, one_mul, Rneg_mul_self', neg_sub]

lemma augIdealOdd_mem_iff {A : R} : A ∈ augIdealOdd ↔ A * Rneg = A := by
  constructor
  · intro hA
    have hz : (Rneg + 1) * Rneg = Rneg + 1 := by
      rw [add_mul, one_mul, Rneg_mul_self', add_comm (1 : R) Rneg]
    have key : ∀ r s : R, r * (Rneg + 1) * s * Rneg = r * (Rneg + 1) * s := by
      intro r s
      calc r * (Rneg + 1) * s * Rneg
          = r * (Rneg + 1) * (s * Rneg) := by noncomm_ring
        _ = r * (Rneg + 1) * (Rneg * s) := by rw [← Rneg_comm' s]
        _ = r * ((Rneg + 1) * Rneg) * s := by noncomm_ring
        _ = r * (Rneg + 1) * s := by rw [hz]
    induction hA using Submodule.span_induction with
    | mem x hx => obtain ⟨r, s, rfl⟩ := hx; exact key r s
    | zero => rw [zero_mul]
    | add x y _ _ hx hy => rw [add_mul, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, hx]
  · intro hA
    have h2 : A * (Rneg + 1) = (2 : ℂ) • A := by
      rw [mul_add, mul_one, hA, ← two_smul ℂ A]
    refine Submodule.subset_span ⟨(2⁻¹ : ℂ) • A, 1, ?_⟩
    rw [mul_one, Algebra.smul_mul_assoc, h2, smul_smul,
      show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

end Work.Asymptotics
