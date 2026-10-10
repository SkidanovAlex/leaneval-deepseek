/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Mathlib
import Submission.Work.FFResidual.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Change of model for a place of a function field

The residual input `Work.FFResidual.HasFunctionFieldPlace 𝔽 𝕜` — the existence of a place of the
function field `𝕜` over its constants `𝔽` (a discrete valuation ring `R ⊆ 𝕜` with `𝔽 ⊆ R` and a
chosen uniformizer `π`) — is *invariant under an `𝔽`-algebra isomorphism* `𝕜 ≃ₐ[𝔽] 𝕜'` of the top
field, as it must be: the place lives on the abstract function field, not on a particular model of
it.

The transport keeps the same valuation ring `R` and the same uniformizer `π`, and pushes the
`R`-algebra structure of `𝕜` forward along the isomorphism `e`:

`Algebra R 𝕜' := RingHom.toAlgebra (e.toRingEquiv.toRingHom.comp (algebraMap R 𝕜))`.

Then

* `IsScalarTower 𝔽 R 𝕜'` follows from `IsScalarTower 𝔽 R 𝕜` since `e` is `𝔽`-linear
  (`IsScalarTower.of_algebraMap_eq`), and
* `IsFractionRing R 𝕜'` follows from `IsFractionRing R 𝕜` since `e` is an `R`-algebra equivalence
  (`IsFractionRing.of_algEquiv`, i.e. `IsLocalization.isLocalization_of_algEquiv`).

This is the model-change step between two fraction fields of the same ring, e.g. between
`FractionRing (MvPolynomial (Fin n) 𝔽)` and `(Spec (MvPolynomial (Fin n) 𝔽)).functionField`,
which Mathlib likes to present as distinct (but canonically isomorphic) fraction fields.

## Main result

* `Work.FFResidual.Geometry.hasFunctionFieldPlace_of_algEquiv` — `HasFunctionFieldPlace` transports
  along `𝕜 ≃ₐ[𝔽] 𝕜'`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.FFResidual.Geometry

/-- **A place of a function field transports along an `𝔽`-algebra isomorphism of the field.**

If the function field `𝕜` has a place over `𝔽`, then so does any `𝔽`-algebra-isomorphic field `𝕜'`:
keep the valuation ring `R` and the uniformizer `π`, and let `R` act on `𝕜'` through `e`'s pullback
of scalars, `algebraMap R 𝕜' = e ∘ algebraMap R 𝕜`.  The constants still land in `R`
(`IsScalarTower 𝔽 R 𝕜'`), and `𝕜'` is still the fraction ring of `R`
(`IsFractionRing R 𝕜'`), so the transported data is again a place. -/
theorem hasFunctionFieldPlace_of_algEquiv {𝔽 𝕜 𝕜' : Type} [Field 𝔽] [Field 𝕜] [Field 𝕜']
    [Algebra 𝔽 𝕜] [Algebra 𝔽 𝕜'] (e : 𝕜 ≃ₐ[𝔽] 𝕜')
    (h : Work.FFResidual.HasFunctionFieldPlace 𝔽 𝕜) :
    Work.FFResidual.HasFunctionFieldPlace 𝔽 𝕜' := by
  obtain ⟨P⟩ := h
  -- The data of the place of `𝕜`, as local instances.
  letI := P.commRing
  letI := P.isDomain
  letI := P.isDiscreteValuationRing
  letI := P.algebraF
  letI := P.algebraR
  letI := P.tower
  letI := P.isFractionRing
  -- Push the `R`-algebra structure of `𝕜` forward along `e`.
  letI : Algebra P.R 𝕜' :=
    RingHom.toAlgebra ((e.toRingEquiv : 𝕜 →+* 𝕜').comp (algebraMap P.R 𝕜))
  -- The constants are still integral at the place: `e` is `𝔽`-linear and `𝔽 → R → 𝕜` is a tower.
  have htower : IsScalarTower 𝔽 P.R 𝕜' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [show algebraMap P.R 𝕜' (algebraMap 𝔽 P.R x)
            = e (algebraMap P.R 𝕜 (algebraMap 𝔽 P.R x)) from rfl,
          ← IsScalarTower.algebraMap_apply 𝔽 P.R 𝕜 x]
      exact (e.commutes x).symm
  -- `e` is an `R`-algebra equivalence, so `IsFractionRing` transports across it.
  have hfr : IsFractionRing P.R 𝕜' :=
    IsFractionRing.of_algEquiv (R := P.R) (K := 𝕜) (L := 𝕜')
      { e.toRingEquiv with commutes' := fun r => rfl }
  exact ⟨{ R := P.R, π := P.π, isUniformizer := P.isUniformizer }⟩

end Work.FFResidual.Geometry
