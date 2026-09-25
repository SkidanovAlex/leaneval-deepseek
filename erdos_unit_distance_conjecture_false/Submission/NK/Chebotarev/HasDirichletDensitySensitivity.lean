import Mathlib
import Submission.NK.Chebotarev.Density
open IsDedekindDomain
namespace NK.Chebotarev
theorem HasDirichletDensitySensitivity {K : Type*} [Field K] [NumberField K]
    {S T : Set (NK.Chebotarev.PrimeIdeal K)} {δ : ℝ}
    (h : (S \ T ∪ T \ S).Finite)
    (hS : NumberField.Set.HasDirichletDensity S δ) :
    NumberField.Set.HasDirichletDensity T δ := by
  have hTS : (T \ S).Finite := h.subset Set.subset_union_right
  have hST : (S \ T).Finite := h.subset Set.subset_union_left
  have hA : NumberField.Set.HasDirichletDensity (S ∪ T) δ := by
    have := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_finite
      (S := S) (T := T \ S) hS hTS
    rwa [Set.union_sdiff_self] at this
  have hF0 : NumberField.Set.HasDirichletDensity (S \ T) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hST
  have hU := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
    (S := (S ∪ T)ᶜ) (T := S \ T)
    (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hA) hF0
  have hfinal := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hU
  have heq : (((S ∪ T)ᶜ ∪ (S \ T))ᶜ : Set (NK.Chebotarev.PrimeIdeal K)) = T := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_diff, not_or, not_and,
      not_not]; tauto
  rw [heq, show (1:ℝ) - (1 - δ) = δ by ring] at hfinal
  exact hfinal
end NK.Chebotarev
