/-
# The valuation-ring extension used in the proof of `Work.SpecLin.specLin`
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Interface

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin

variable {K : Type u} [Field K]

section Instances

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

example : Algebra K (FractionRing R) := inferInstance
example : IsScalarTower K R (FractionRing R) := inferInstance
example : IsLocalRing R := inferInstance
example : IsScalarTower K R (IsLocalRing.ResidueField R) := inferInstance
noncomputable example : Algebra K (AlgebraicClosure (FractionRing R)) := inferInstance
noncomputable example : IsScalarTower K (FractionRing R) (AlgebraicClosure (FractionRing R)) :=
  inferInstance
noncomputable example : IsAlgClosed (AlgebraicClosure (FractionRing R)) := inferInstance
noncomputable example : Field (AlgebraicClosure (FractionRing R)) := inferInstance

end Instances

/-- A valuation ring extension of `R` inside an algebraically closed field, chosen once and for
all in the proof of `specLin`: it consists of an algebraically closed field `F` which is an
extension of the fraction field of `R`, of a valuation ring `R'` inside `F` whose fraction field
is `F`, and of a local `K`-algebra map `R → R'` compatible with the structure maps to `F`.

The proof of `specLin` never needs the actual construction: it only needs that such data exist
(`nonempty_ext`). -/
structure Ext (K : Type u) [Field K] (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] where
  /-- the algebraically closed field where the generic divisors split -/
  F : Type u
  [fieldF : Field F]
  [algKF : Algebra K F]
  [algFracF : Algebra (FractionRing R) F]
  [towerFracF : IsScalarTower K (FractionRing R) F]
  [isAlgClosedF : IsAlgClosed F]
  /-- the valuation ring of `F` containing the image of `R` -/
  R' : Type u
  [commRingR' : CommRing R']
  [isDomainR' : IsDomain R']
  [valuationRingR' : ValuationRing R']
  [algKR' : Algebra K R']
  [algR'F : Algebra R' F]
  [isFractionRingR' : IsFractionRing R' F]
  [towerR'F : IsScalarTower K R' F]
  /-- the (local) map from `R` into the valuation ring -/
  e : R →ₐ[K] R'
  isLocal : IsLocalHom e.toRingHom
  /-- compatibility with the structure maps into `F` -/
  compat : ∀ r : R, algebraMap R' F (e r) =
    algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)

attribute [instance] Ext.fieldF Ext.algKF Ext.algFracF Ext.towerFracF Ext.isAlgClosedF
  Ext.commRingR' Ext.isDomainR' Ext.valuationRingR' Ext.algKR' Ext.algR'F Ext.isFractionRingR'
  Ext.towerR'F

namespace Ext

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]

/-- The maps encoded by `Ext` are compatible: the composite `R → R' → F` is the canonical
`R → Frac R → F`. -/
theorem compat' (E : Ext K R) :
    (IsScalarTower.toAlgHom K E.R' E.F).comp E.e
      = (IsScalarTower.toAlgHom K (FractionRing R) E.F).comp
          (IsScalarTower.toAlgHom K R (FractionRing R)) := by
  ext r
  exact E.compat r

/-- The canonical `K`-algebra map from the fraction field of `E.R'` into `E.F`: since `E.F` is a
fraction field of `E.R'`, this is an isomorphism onto `E.F`. -/
noncomputable def psi (E : Ext K R) : FractionRing E.R' →ₐ[K] E.F where
  toRingHom := IsFractionRing.lift (IsFractionRing.injective E.R' E.F)
  commutes' := fun k => by
    show IsFractionRing.lift (IsFractionRing.injective E.R' E.F)
      ((algebraMap E.R' (FractionRing E.R')) ((algebraMap K E.R') k)) = (algebraMap K E.F) k
    rw [IsFractionRing.lift_algebraMap]
    exact (IsScalarTower.algebraMap_apply K E.R' E.F k).symm

/-- `psi` is the structure map on `E.R'`. -/
theorem psi_algebraMap (E : Ext K R) (x : E.R') :
    E.psi (algebraMap E.R' (FractionRing E.R') x) = algebraMap E.R' E.F x := by
  show IsFractionRing.lift (IsFractionRing.injective E.R' E.F)
    (algebraMap E.R' (FractionRing E.R') x) = algebraMap E.R' E.F x
  exact IsFractionRing.lift_algebraMap _ x

end Ext

/-- **The valuation ring extension exists.**  Given a valuation ring `R` over a field `K`, there
is an algebraically closed field `F` extending the fraction field of `R`, a valuation ring `R'`
of `F` and a local `K`-algebra map `R → R'` compatible with the structure maps.

We take `F` to be an algebraic closure of the fraction field of `R` and `R'` the valuation
subring of `F` produced by `IsLocalRing.exists_factor_valuationRing` applied to the structure map
`R → F`. -/
theorem nonempty_ext (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R] :
    Nonempty (Ext K R) := by
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨W, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
  let R' := ↥W
  have hK : ∀ k : K, algebraMap K F k ∈ W.toSubring := fun k => by
    have h1 : (algebraMap (FractionRing R) F) (algebraMap R (FractionRing R) (algebraMap K R k)) =
        algebraMap K F k := rfl
    rw [← h1]; exact hmem (algebraMap K R k)
  letI : Algebra K R' := (RingHom.codRestrict (algebraMap K F) W.toSubring hK).toAlgebra
  haveI : IsScalarTower K R' F := IsScalarTower.of_algebraMap_eq (fun k => by
    rw [RingHom.algebraMap_toAlgebra]
    rfl)
  let g : R →+* R' :=
    ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).codRestrict
      W.toSubring hmem
  have hgl : IsLocalHom g := hloc
  let e : R →ₐ[K] R' := AlgHom.mk g (fun k => by
    refine Subtype.ext ?_
    exact (show (algebraMap (FractionRing R) F) (algebraMap R (FractionRing R) (algebraMap K R k)) =
      algebraMap K F k from rfl))
  have hel : IsLocalHom e.toRingHom := hgl
  exact ⟨{ F := F, R' := R', e := e, isLocal := hel, compat := fun r => rfl }⟩

end Work.SpecLin
