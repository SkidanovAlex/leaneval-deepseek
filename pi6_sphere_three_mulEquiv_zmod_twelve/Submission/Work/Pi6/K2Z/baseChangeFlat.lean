import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Change of coefficients for singular homology along a flat ring homomorphism `ℤ → 𝕜`

The singular chains of a space with coefficients in a commutative ring are the integral ones
with coefficients extended along `ℤ → R`.  When the ring homomorphism is **flat**, extension of
scalars is exact, hence commutes with homology, and we obtain the change-of-coefficients
isomorphism

`H_n(X;𝕜) ≅ 𝕜 ⊗[ℤ] H_n(X;ℤ)`.

This is the generalisation of `Work.StemsB.sphRatHomology`/`Work.RatHurewicz` (the case `𝕜 = ℚ`)
to an arbitrary flat field `𝕜` (e.g. any field of characteristic `0`).

The two ingredients, both already in the library:

* `Work.StemsB.SphRat.chainComplexBaseChange`: `C_*(X;ℤ) ⊗[ℤ] 𝕜 ≅ C_*(X;𝕜)` as chain complexes
  (`C_*` being the simplicial chain complex of the singular simplicial set);
* `Work.StemsB.SphRat.homologyMapBaseChange`: an additive exact functor commutes with homology.

The only new point is the identification of the coefficient object
`(extendScalars (ℤ → 𝕜)).obj ℤ ≅ 𝕜`, which is exactly the isomorphism
`εIso` of the monoidal structure of the extension-of-scalars functor.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.K2Z

noncomputable section

/-- The coefficient object `𝕜 ⊗[ℤ] ℤ = (extendScalars (ℤ → 𝕜)).obj ℤ` is `𝕜`.

This is the `ε` of the monoidal structure of the extension-of-scalars functor
(`Functor.Monoidal.εIso`), i.e. the isomorphism `𝕜 ⊗[ℤ] ℤ ≅ 𝕜`, `a ⊗ z ↦ z • a`. -/
noncomputable def extendScalarsIntFieldIso (𝕜 : Type) [CommRing 𝕜] :
    (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of 𝕜 𝕜 :=
  (Functor.Monoidal.εIso (ModuleCat.extendScalars (Int.castRingHom 𝕜))).symm

theorem baseChangeFlat {𝕜 : Type} [Field 𝕜] (hfl : (Int.castRingHom 𝕜).Flat) (X : Type)
    [TopologicalSpace X] (n : ℕ) :
    Nonempty (Work.Pi6.HR 𝕜 X n ≅
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ X n)) := by
  -- `𝕜` flat over `ℤ` means extension of scalars is exact, hence preserves homology
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom 𝕜)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hfl
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom 𝕜)) := inferInstance
  haveI : (ModuleCat.extendScalars (Int.castRingHom 𝕜)).PreservesHomology := inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)) := fun _ => inferInstance
  -- the comparison `C_*(X;ℤ) ⊗[ℤ] 𝕜 ≅ C_*(X;𝕜)` of chain complexes
  let F : ModuleCat ℤ ⥤ ModuleCat 𝕜 := ModuleCat.extendScalars (Int.castRingHom 𝕜)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Y
  let L : ChainComplex (ModuleCat 𝕜) ℕ := Work.Cohomology.singularChains 𝕜 Y
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y)
        (extendScalarsIntFieldIso 𝕜)
  -- hence, `𝕜` being flat, `H_n(X;𝕜)` is the extension of scalars of `H_n(X;ℤ)`
  have hΨ : L.homology n ≅ F.obj (K.homology n) :=
    (HomologicalComplex.homologyMapIso hΦ n).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange F K n).some
  exact ⟨hΨ⟩

end

end Work.Pi6.K2Z
