import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.FreeProduct.Model
import Submission.Work.ORHughesFree.Rat.FreeProduct.first_letter_NU

namespace Work.ORHughesFree.Rat

open WordModel FreeProduct

theorem first_letter {U : Type} [Group U] (a a' : Work.ORHughesFree.RatU U) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (m m' : Work.ORHughesFree.Rat.WordModel.Mword U)
    (hm : Work.ORHughesFree.Rat.WordModel.Mval m ≠ 0)
    (hm' : Work.ORHughesFree.Rat.WordModel.Mval m' ≠ 0)
    (h : Work.ORHughesFree.Rat.WordModel.letterOf (Work.ORHughesFree.Rat.WordModel.rho a) * m
      = Work.ORHughesFree.Rat.WordModel.letterOf (Work.ORHughesFree.Rat.WordModel.rho a') * m') :
    ∃ v : U, a' = Work.ORHughesFree.RatU.ofGroup v⁻¹ * a ∧ m = Work.ORHughesFree.Rat.WordModel.Mu v * m' := by
  -- The hypothesis, read in `Rat(U)`, is `a⋄ * Mval m = a'⋄ * Mval m'`.
  have h2 : RatU.ratOp a * WordModel.Mval m = RatU.ratOp a' * WordModel.Mval m' := by
    have hM := congrArg WordModel.Mval h
    rwa [WordModel.Mval_mul, WordModel.Mval_mul, Mval_letterOf_rho, Mval_letterOf_rho] at hM
  -- Transport along the model `ℕ[U ♮ X]`: the letters became `Xgen`.
  have h3 : NU.Xgen a * nrm m = NU.Xgen a' * nrm m' := by
    have h4 := congrArg Psi h2
    rw [map_mul, map_mul, Psi_ratOp ha, Psi_ratOp ha', Psi_Mval hm, Psi_Mval hm',
      MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one] at h4
    exact MonoidAlgebra.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h4
  -- First letter in `U ♮ X`.
  obtain ⟨v, hv, hq⟩ := first_letter_NU a a' (nrm m) (nrm m') h3
  refine ⟨v, ?_, ?_⟩
  · apply NU.Xgen_injective
    rw [hv, NU.Xgen_mul_Ugen, actR]
  · have hmv : WordModel.Mval (WordModel.Mu v) ≠ 0 := by
      rw [WordModel.Mval_Mu]; exact ofGroup_ne_zero v
    have hmm' : WordModel.Mval (WordModel.Mu v * m') ≠ 0 := by
      rw [WordModel.Mval_mul]
      intro h0
      have ht : Rat.treeOfRat U (WordModel.Mval (WordModel.Mu v)) *
          Rat.treeOfRat U (WordModel.Mval m') = 0 := by
        rw [← Rat.treeOfRat_mul, h0, Rat.treeOfRat_zero]
      rcases (Tree.mul_eq_zero _ _).mp ht with h | h
      · rw [WordModel.Mval_Mu, Rat.treeOfRat_ofGroup] at h
        exact Tree.one_ne_zero h
      · exact hm' ((Rat.treeOfRat_eq_zero_iff U _).mp h)
    refine nrm_injective_of_ne hm hmm' (hq.trans ?_)
    rw [nrm_mul hmv hm', nrm_Mu]

end Work.ORHughesFree.Rat
