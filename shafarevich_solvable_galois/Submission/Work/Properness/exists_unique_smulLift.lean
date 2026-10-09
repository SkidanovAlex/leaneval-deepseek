/-
Copyright (c) 2025. All rights reserved.

# The set of lifts is a torsor under `Z¹(H, A)`

Let `S` be the abstract setting of an embedding problem with abelian kernel
(`Work.Properness.Setup`): `1 → A → E → Q → 1` with `A = ker π` abelian, and `ρ : H ↠ Q` the map
to be lifted.  A **lift** (solution) is a homomorphism `ψ : H →* E` with `π ∘ ψ = ρ`, and the set
of lifts is a torsor under `Z¹(H, A)` for the canonical conjugation action of `H` on the kernel
`A` (Proposition 11 of Schmidt–Wingberg, arXiv:math/9809211).

The present file records the resulting **uniqueness of the torsor coordinate**: given any two lifts
`ψ`, `ψ'` there is a *unique* `1`-cocycle `x ∈ Z¹(H, A)` with

`ψ' h = x h · ψ h`   for all `h : H`

(`ψ' = x · ψ`).  This is `Work.Properness.exists_unique_smulLift`.

## Proof

* **Existence.**  Take `x = cocycleOfLiftFun ψ ψ'`, the difference
  `h ↦ ψ' h * (ψ h)⁻¹ ∈ A`; it is a `1`-cocycle (`cocycleOfLiftFun_mem_Z1`) and the pointwise
  product `(cocycleOfLiftFun ψ ψ') · ψ` recovers `ψ'` (`mulFun_cocycleOfLiftFun`).
* **Uniqueness.**  If `x · ψ = ψ'` pointwise, then `x` agrees with the difference cocycle
  `cocycleOfLiftFun ψ ψ'` at every `h` (`cocycleOfLiftFun_eq_of_forall_mulFun`); two elements of
  the subgroup `Z¹(H, A)` that agree pointwise are equal.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.cocycleOfLiftFun_mem_Z1
import Submission.Work.Properness.mulFun_cocycleOfLiftFun
import Submission.Work.Properness.cocycleOfLiftFun_eq_of_forall_mulFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- `autoImplicit` is needed for the universe binder `{u v w : Universe}` of the statement below,
-- exactly as in the sibling files of this directory.
set_option autoImplicit true

namespace Work.Properness

/-- **The lifts form a torsor under `Z¹(H, A)`: the torsor coordinate is unique.**

For any two lifts `ψ`, `ψ'` of the embedding problem there is a unique `1`-cocycle
`x ∈ Z¹(H, A)` whose pointwise product with `ψ` is `ψ'`:
`ψ' h = x h · ψ h` for all `h : H`.

Existence is the `1`-cocycle `cocycleOfLiftFun ψ ψ' = ψ' - ψ`; uniqueness is the injectivity of
the map `x ↦ x · ψ`. -/
theorem exists_unique_smulLift {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ ψ' : S.Lift) : ∃! x : Work.GroupCohomology.Z1 S.H (Additive S.A), ∀ h : S.H, (ψ' : S.H → S.E) h = S.mulFun x.1 ψ.1 h := by
  -- candidate coordinate: the difference cocycle `ψ' - ψ`
  refine ⟨⟨S.cocycleOfLiftFun ψ ψ',
      @cocycleOfLiftFun_mem_Z1 Universe u v w S ψ ψ'⟩, ?_, ?_⟩
  · -- existence: `(ψ' - ψ) · ψ = ψ'`
    intro h
    exact (@mulFun_cocycleOfLiftFun Universe u v w S ψ ψ' h).symm
  · -- uniqueness: any cocycle realizing `ψ'` agrees pointwise with `ψ' - ψ`
    intro y hy
    apply Subtype.ext
    funext h
    exact (@cocycleOfLiftFun_eq_of_forall_mulFun Universe u v w S ψ ψ' y hy h).symm

end Work.Properness
