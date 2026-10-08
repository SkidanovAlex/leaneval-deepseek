import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- Every class function on a finite group is a linear combination of the irreducible
characters, with coefficients the normalised inner products `cfInner f χ`.

Write `S = ∑ χ ∈ Irr G, (cfInner f χ) • χ`.  Both `f` and `S` are class functions, and
for `ψ ∈ Irr G` the orthonormality of the irreducible characters
(`Work.CharCore.irr_orthonormal`) collapses the sum
`⟨S, ψ⟩ = ∑_χ ⟨f, χ⟩ ⟨χ, ψ⟩` to the single term `⟨f, ψ⟩`, so `f - S` is a class function
orthogonal to every irreducible character.  Such a class function is zero by
`Work.CharCore.classFun_eq_zero_of_orthogonal`. -/
theorem classFun_eq_sum_irr {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClassFun f) :
    f = ∑ χ ∈ Irr G, (cfInner f χ) • χ := by
  set S : G → ℂ := ∑ χ ∈ Irr G, (cfInner f χ) • χ with hS
  -- `S` is a class function, being a combination of the class functions `χ ∈ Irr G`.
  have hS_class : IsClassFun S :=
    IsClassFun.sum (Irr G) (fun χ => (cfInner f χ) • χ)
      (fun χ hχ => IsClassFun.smul (cfInner f χ) (isClassFun_of_mem_Irr hχ))
  have hg : IsClassFun (f - S) := IsClassFun.sub hf hS_class
  -- `f - S` is orthogonal to every irreducible character.
  have horth : ∀ ψ ∈ Irr G, cfInner (f - S) ψ = 0 := by
    intro ψ hψ
    have hsum : cfInner S ψ = ∑ χ ∈ Irr G, cfInner f χ * cfInner χ ψ := by
      rw [hS, cfInner_sum_smul_left]
    have hsingle : (∑ χ ∈ Irr G, cfInner f χ * cfInner χ ψ) = cfInner f ψ := by
      rw [Finset.sum_eq_single ψ]
      · rw [irr_orthonormal ψ ψ hψ hψ, if_pos rfl, mul_one]
      · intro χ hχ hne
        rw [irr_orthonormal χ ψ hχ hψ, if_neg hne, mul_zero]
      · intro hnot
        exact absurd hψ hnot
    rw [cfInner_sub_left, hsum, hsingle, sub_self]
  have hzero : f - S = 0 := classFun_eq_zero_of_orthogonal hg horth
  exact sub_eq_zero.mp hzero

end Work.CharCore
