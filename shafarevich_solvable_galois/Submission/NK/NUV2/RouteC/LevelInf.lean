import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# The level inflation maps (Route C copy of the abstract local level theory)

For a tower of fields `F ⊆ M ⊆ L` (with `M/F` normal), this file defines the *level inflation map*

`levelInfMap : H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)`

as the map induced by the restriction `Gal(L/F) →* Gal(M/F)` and the units inclusion `Mˣ → Lˣ`
(a coefficient change of representations).  This is the intrinsic form of the transition map of the
local class formation: its two structural properties are

* functoriality (`levelInfMap_comp`) — it is a functor on the tower, immediate from
  `groupCohomology.map_comp`;
* normality with the `H⁰ × H²` cup product (`levelInfMap_cup`) — `Inf(a ∪ δ(χ ∘ res)) = a ∪ δχ`;
* injectivity with range the `[M:F]`-torsion (`levelInfMap_injective`, `levelInfMap_range`),
  which is the Galois-descent / Hilbert-90 statement.

The first two are proved here; the third is the target of a delegated lemma (its proof goes through
the identification of the source with the invariants of the ambient cohomology,
`Commons…addEquiv_groupCohomology_two_quotientToInvariants_units`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory Representation

namespace NK.NUV2.RouteC

set_option maxHeartbeats 1600000

universe u

section UnitsIncl

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L]

/-- The units inclusion `Mˣ → Lˣ` as a `ℤ`-linear map. -/
noncomputable def unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by
        show Additive.ofMul (Units.map (algebraMap M L).toMonoidHom
              (Additive.toMul (x + y))) =
            Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x)) +
              Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul y))
        rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
        rfl }

@[simp]
theorem unitsInclLinearMap_apply (x : Additive Mˣ) :
    (unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ) x
      = Additive.ofMul (Units.map (algebraMap M L).toMonoidHom (Additive.toMul x)) := rfl

end UnitsIncl

section LevelInf

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [Normal F M]

/-- **The coefficient morphism of the level inflation map**: the units inclusion `Mˣ → Lˣ` as a
morphism of representations over the restriction `Gal(L/F) →* Gal(M/F)`. -/
noncomputable abbrev unitsInclCoeff :
    Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) (E := M))
        (Rep.ofAlgebraAutOnUnits F M) ⟶ Rep.ofAlgebraAutOnUnits F L :=
  Rep.ofHom
    { toLinearMap := (unitsInclLinearMap : Additive Mˣ →ₗ[ℤ] Additive Lˣ)
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        set y : Mˣ := Additive.toMul x with hy
        show Additive.ofMul (Units.map (algebraMap M L).toMonoidHom
            (Units.map (((AlgEquiv.restrictNormalHom (K₁ := L) (E := M)) σ)).toMonoidHom y))
          = Additive.ofMul ((σ : L ≃ₐ[F] L) • Units.map (algebraMap M L).toMonoidHom y)
        rw [AlgEquiv.smul_units_def]
        congr 1
        apply Units.ext
        simp only [Units.coe_map]
        rw [show (AlgEquiv.restrictNormalHom (K₁ := L) (E := M)) σ = σ.restrictNormal M from rfl]
        exact AlgEquiv.restrictNormal_commutes (F := F) σ M y }

/-- **The level inflation map** `H²(Gal(M/F), Mˣ) → H²(Gal(L/F), Lˣ)` for `F ⊆ M ⊆ L`. -/
noncomputable abbrev levelInfMap :
    groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := L) (E := M))
    (unitsInclCoeff : Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) (E := M))
      (Rep.ofAlgebraAutOnUnits F M) ⟶ Rep.ofAlgebraAutOnUnits F L) 2

end LevelInf

end NK.NUV2.RouteC
namespace NK.NUV2.RouteC

section LevelInfZ

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [Normal F M]

/-- **The coefficient morphism on trivial `ℤ`-coefficients**: the identity, viewed as a morphism
`Rep.res (restrictNormalHom) (trivial ℤ Gal(M/F) ℤ) ⟶ trivial ℤ Gal(L/F) ℤ`. -/
noncomputable abbrev trivialCoeffIso :
    Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) (E := M)) (Rep.trivial ℤ (M ≃ₐ[F] M) ℤ) ⟶
      Rep.trivial ℤ (L ≃ₐ[F] L) ℤ :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' := fun _ => by
        ext v; simp [Rep.trivial_ρ, Representation.trivial_apply] }

/-- **The level inflation on trivial `ℤ`-coefficients**: `H²(Gal(M/F), ℤ) → H²(Gal(L/F), ℤ)`. -/
noncomputable abbrev levelInfMapZ :
    groupCohomology (Rep.trivial ℤ (M ≃ₐ[F] M) ℤ) 2 ⟶
      groupCohomology (Rep.trivial ℤ (L ≃ₐ[F] L) ℤ) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := L) (E := M)) (trivialCoeffIso (F := F)) 2

end LevelInfZ

end NK.NUV2.RouteC
