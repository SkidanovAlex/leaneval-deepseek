import Mathlib
import Submission.Work.Cohomology.MVBasic

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- Exactness at the middle term of the Mayer–Vietoris sequence: the kernel of `mvBeta` (the
difference of the restrictions to `A` and `B`, with values on `A ⊓ B`) is the range of `mvAlpha`
(restriction to the two pieces), when `A` and `B` cover `S`.

The inclusion `range α ⊆ ker β` is `Submission.Cohomology.mvBeta_comp_mvAlpha`.  For the reverse
inclusion, given `p` with `mvBeta S A B n p = 0`, the two components of `p` agree on `A ⊓ B`
(after rewriting with `pullbackCo_apply` and using that the underlying simplices are equal); glue
them by `w σ := p.1 ⟨σ, h⟩` if `σ ∈ A.obj (op ⦋n⦌)` and `w σ := p.2 ⟨σ, h'⟩` otherwise, where
`h'` comes from `hAB : A ⊔ B = ⊤` rewritten as `Subfunctor.max_obj`, and `classical` is needed for
the `if`.  Then `mvAlpha w = p` componentwise. -/
theorem mvBeta_ker_eq_range (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (n : ℕ) :
    LinearMap.ker (Submission.Cohomology.mvBeta S A B n)
      = (Submission.Cohomology.mvAlpha S A B n).range := by
  classical
  apply le_antisymm
  · rintro p hp
    rw [LinearMap.mem_ker] at hp
    rw [LinearMap.mem_range]
    -- the two components of `p` agree on the intersection `A ⊓ B`
    have hker : Submission.Cohomology.pullbackCo ℚ
          (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) p.1
        = Submission.Cohomology.pullbackCo ℚ
          (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) p.2 := by
      have h := hp
      rw [Submission.Cohomology.mvBeta_apply] at h
      exact sub_eq_zero.mp h
    have hpoint : ∀ x : (A ⊓ B : S.Subcomplex).obj (op ⦋n⦌),
        p.1 ⟨x.val, x.prop.1⟩ = p.2 ⟨x.val, x.prop.2⟩ := by
      intro x
      exact congrFun hker x
    -- every simplex of `S` lies in `A` or in `B`
    have hcov : ∀ σ : S.obj (op ⦋n⦌),
        σ ∈ A.obj (op ⦋n⦌) ∨ σ ∈ B.obj (op ⦋n⦌) := by
      intro σ
      have h : σ ∈ (A ⊔ B).obj (op ⦋n⦌) := by rw [hAB]; trivial
      simpa only [Subfunctor.max_obj, Set.mem_union] using h
    refine ⟨fun σ => if h : σ ∈ A.obj (op ⦋n⦌) then p.1 ⟨σ, h⟩
      else p.2 ⟨σ, (hcov σ).resolve_left h⟩, ?_⟩
    apply Prod.ext
    · rw [Submission.Cohomology.mvAlpha_fst]
      funext x
      show (if h : x.val ∈ A.obj (op ⦋n⦌) then p.1 ⟨x.val, h⟩
        else p.2 ⟨x.val, (hcov x.val).resolve_left h⟩) = p.1 x
      rw [dif_pos x.prop]
      rfl
    · rw [Submission.Cohomology.mvAlpha_snd]
      funext x
      show (if h : x.val ∈ A.obj (op ⦋n⦌) then p.1 ⟨x.val, h⟩
        else p.2 ⟨x.val, (hcov x.val).resolve_left h⟩) = p.2 x
      by_cases h : x.val ∈ A.obj (op ⦋n⦌)
      · rw [dif_pos h]
        exact hpoint ⟨x.val, h, x.prop⟩
      · rw [dif_neg h]
        rfl
  · rintro p ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun (Submission.Cohomology.mvBeta_comp_mvAlpha S A B n) u
    simpa using h

end Work.Cohomology
