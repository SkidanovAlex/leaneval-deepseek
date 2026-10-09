import Mathlib
import Submission.Work.SSGRoute.PTCore.invariantsSubmodule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTCore

/-- A `Γ`-equivariant linear equivalence restricts to a linear equivalence between the
submodules of invariants (fixed points) of the two actions. -/
noncomputable def invariantsSubmoduleEquivOfEquiv
    {R : Type} [Semiring R] {Γ X Y : Type} [Group Γ]
    [AddCommMonoid X] [Module R X] [DistribMulAction Γ X] [SMulCommClass Γ R X]
    [AddCommMonoid Y] [Module R Y] [DistribMulAction Γ Y] [SMulCommClass Γ R Y]
    (e : X ≃ₗ[R] Y) (he : ∀ (γ : Γ) (x : X), e (γ • x) = γ • e x) :
    invariantsSubmodule Γ R X ≃ₗ[R] invariantsSubmodule Γ R Y := by
  have hmem : ∀ x : X, x ∈ invariantsSubmodule Γ R X ↔
      e x ∈ invariantsSubmodule Γ R Y := by
    intro x
    rw [mem_invariantsSubmodule, mem_invariantsSubmodule]
    constructor
    · intro hx γ
      rw [← he γ x, hx γ]
    · intro hx γ
      exact e.injective (by rw [he γ x, hx γ])
  refine LinearEquiv.ofBijective
    { toFun := fun x => ⟨e x, (hmem x).mp x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp } ?_
  constructor
  · intro x y hxy
    have h : (e x : Y) = (e y : Y) := by simpa using congrArg Subtype.val hxy
    exact Subtype.ext (e.injective h)
  · intro y
    refine ⟨⟨e.symm y, (hmem _).mpr (by simp)⟩, ?_⟩
    ext
    simp

/-- **Invariants of equivariantly equivalent modules have the same rank.**

If `X` and `Y` are `Γ`-equivariantly linearly equivalent (over a semiring `R` with compatible
`Γ`-action), then the `R`-ranks of their submodules of `Γ`-invariants agree. This is immediate
from `invariantsSubmoduleEquivOfEquiv` together with `LinearEquiv.finrank_eq`. -/
theorem finrank_invariants_equivariant
    {R : Type} [Semiring R] {Γ X Y : Type} [Group Γ]
    [AddCommMonoid X] [Module R X] [DistribMulAction Γ X] [SMulCommClass Γ R X]
    [AddCommMonoid Y] [Module R Y] [DistribMulAction Γ Y] [SMulCommClass Γ R Y]
    (e : X ≃ₗ[R] Y) (he : ∀ (γ : Γ) (x : X), e (γ • x) = γ • e x) :
    Module.finrank R (Work.SSGRoute.PTCore.invariantsSubmodule Γ R X)
      = Module.finrank R (Work.SSGRoute.PTCore.invariantsSubmodule Γ R Y) :=
  (invariantsSubmoduleEquivOfEquiv e he).finrank_eq

end Work.SSGRoute.PTCore
