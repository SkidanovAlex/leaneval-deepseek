import Mathlib
import Submission.Work.Frobenius.Pair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Frobenius.Induction

open Classical

/-- `Ind_H^G f` is invariant under conjugation of its argument: for all `g y : G`,
`indFun H f (y * g * y⁻¹) = indFun H f g`.

Indeed, `Ind_H^G f g = |H|⁻¹ ∑_{x : x*g*x⁻¹ ∈ H} f ⟨x*g*x⁻¹, _⟩`, and for a fixed `y`
the summand at `x` in the sum for `y * g * y⁻¹` equals the summand at `z = x * y` in the
sum for `g`, because `x * (y * g * y⁻¹) * x⁻¹ = (x * y) * g * (x * y)⁻¹`.  Reindexing the
sum over `G` by the permutation `x ↦ x * y` (`Fintype.sum_equiv` applied to
`Equiv.mulRight y`) gives the claim. -/
theorem indFun_conj_apply {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (f : H → ℂ)
    (g y : G) : indFun H f (y * g * y⁻¹) = indFun H f g := by
  classical
  -- The two summands agree after the reindexing `x ↦ x * y`.
  have key : ∀ x : G,
      (if hx : x * (y * g * y⁻¹) * x⁻¹ ∈ H then f ⟨x * (y * g * y⁻¹) * x⁻¹, hx⟩ else 0)
        = (if hz : (x * y) * g * (x * y)⁻¹ ∈ H then
                f ⟨(x * y) * g * (x * y)⁻¹, hz⟩ else 0) := by
    intro x
    have he : (x * y) * g * (x * y)⁻¹ = x * (y * g * y⁻¹) * x⁻¹ := by group
    by_cases h1 : x * (y * g * y⁻¹) * x⁻¹ ∈ H
    · have h2 : (x * y) * g * (x * y)⁻¹ ∈ H := he.symm ▸ h1
      rw [dite_eq_left h1, dite_eq_left h2]
      exact congrArg f (Subtype.ext he.symm)
    · have h2 : (x * y) * g * (x * y)⁻¹ ∉ H := fun hh => h1 (he ▸ hh)
      rw [dite_eq_right h1, dite_eq_right h2]
  simp only [indFun]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight y) _ _ key

theorem isClassFun_indFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (f : H → ℂ) : IsClassFun (indFun H f) := by
  intro g y
  exact indFun_conj_apply f g y

end Work.Frobenius.Induction
