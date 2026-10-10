import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.deltaHom_inflHIn
import Submission.Work.SSGRoute.inflTrivIn_trans
import Submission.Work.SSGRoute.phi1_classIncl_compat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity of the level inflation maps `Work.SSGRoute.PTExt.inflHIn`

`Work.SSGRoute.inflHIn_trans` is the `map_map` axiom for the level system of the cohomological
input of the descent step (`phi1_mono_step_in`): for finite Galois levels `k ⊆ K ⊆ L ⊆ L' ≤ L''`
of a fixed closure `Ω`, inflating a class `y ∈ H^n(Gal(L/k), res M)` first to `L'` and then to
`L''` is inflating along the composite inclusion `L ≤ L''`.

This is the general-coefficient companion of `Work.SSGRoute.inflTrivIn_trans` and the
`inflCIn` analogue `Work.SSGRoute.inflCIn_trans`.  `inflHIn` unfolds
(`SSGRoute.PTExt.inflHIn`, `SSGRoute.PTExt.inflHLevel`) to
`extHMap (galRes k ↥L ↥L') (resResHom M)`, where the coefficient map `resResHom M` is the canonical
identity transport between the two presentations of `res M` as a `Gal(↥L'/k)`-module
(`SSGRoute.PTExt.resResHom`, identified with the `eqToHom` of the corresponding equality of group
homomorphisms in `Work.SSGRoute.resResHom_eq_transport`).

The proof has two layers, mirroring `inflTrivIn_trans`:

* `extHMap_comp_eqToHom`: an abstract statement about two group homomorphisms `p : G →* X`,
  `a : H →* G`, `b : I →* H` and their composite presentations `q = p.comp a`, `r = q.comp b`,
  `c = a.comp b`: inflating along `a` with the transport `q = p.comp a` and then along `b` with the
  transport `r = q.comp b` equals inflating along the composite `c` with the transport
  `r = p.comp c`.  After substituting the three defining equations (`cases`) all transports become
  `eqToHom rfl = 𝟙`, and the statement is `Work.SSGRoute.extHMap_comp_aux` (proved in
  `inflTrivIn_trans.lean`) for the identity coefficient maps.
* the concrete statement then follows from `resResHom_eq_transport` for the three inclusions and
  `IsScalarTower.AlgEquiv.restrictNormalHom_comp` for the three equalities of restriction maps.

All of this is formal bookkeeping of `Abelian.Ext.mapExactFunctor` and `resResHom`; no arithmetic,
no choice, no CFT input.
-/

set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt

section Abstract

variable {X G H I : Type} [Group X] [Group G] [Group H] [Group I]

/-- **Composition of the transports of the level restriction maps.**  For group homomorphisms
`p : G →* X`, `a : H →* G`, `b : I →* H` and a module `M` over `X`, the two-step inflation of
`y ∈ Hⁿ(G, res_p M)` along `a` (transporting the presentation of `res M` along `q = p.comp a`)
and then along `b` (transporting along `r = q.comp b`) agrees with inflating along the composite
`c = a.comp b` (transporting along `r = p.comp c`).

The three transports are the `eqToHom` of the corresponding `congrArg` equalities of restricted
modules; the composite transport on the right is the one displayed.  This is the abstract form of
`Work.SSGRoute.inflHIn_trans` and the general-coefficient companion of
`Work.SSGRoute.inflTriv_comp_aux`. -/
theorem extHMap_comp_eqToHom (p : G →* X) (a : H →* G) (q : H →* X) (hq : q = p.comp a)
    (b : I →* H) (r : I →* X) (hr : r = q.comp b) (c : I →* G) (hc : c = a.comp b)
    (M : Rep.{0} Coeff X) {n : ℕ} (y : extH (Rep.res p M) n) :
    extHMap b (eqToHom (congrArg (fun t => Rep.res t M) hr.symm))
        (extHMap a (eqToHom (congrArg (fun t => Rep.res t M) hq.symm)) y)
      = extHMap c
          (eqToHom ((congrArg (fun t => Rep.res (p.comp t) M) hc).trans
            ((congrArg (fun t => Rep.res (t.comp b) M) hq).symm.trans
              (congrArg (fun t => Rep.res t M) hr.symm)))) y := by
  cases hc
  cases hq
  cases hr
  -- all three transports are now `eqToHom` of a self-equality, hence the identity
  simp only [eqToHom_refl]
  have hι : Rep.resMap b (𝟙 (Rep.res a (Rep.res p M))) ≫
      𝟙 (Rep.res b (Rep.res a (Rep.res p M))) =
      𝟙 (Rep.res (a.comp b) (Rep.res p M)) := by
    rw [Category.comp_id]
    exact (Rep.resFunctor b).map_id _
  exact extHMap_comp_aux a b (𝟙 _) (𝟙 _) (𝟙 _) hι y

end Abstract

/-- **Transitivity of the level inflation maps** (the `map_map` axiom for the level system
`L ↦ H^n(Gal(L/k), res_L M)`): inflating `H^n(Gal(L/k), M)` first to `L'` and then to `L''` is
inflating along the composite inclusion `L ≤ L''`. -/
theorem inflHIn_trans {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    {L L' L'' : IntermediateField K Ω} [NumberField L] [NumberField L'] [NumberField L'']
    [FiniteDimensional k L] [FiniteDimensional k L'] [FiniteDimensional k L'']
    [IsGalois k L] [IsGalois k L'] [IsGalois k L''] (h₁ : L ≤ L') (h₂ : L' ≤ L'')
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {n : ℕ}
    (y : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) n) :
    SSGRoute.PTExt.inflHIn (k := k) (K := K) h₂ (SSGRoute.PTExt.inflHIn (k := k) (K := K) h₁ y)
      = SSGRoute.PTExt.inflHIn (k := k) (K := K) (h₁.trans h₂) y := by
  -- the three inclusions of levels, as algebras and towers of fields
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion h₁).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥L' := Module.Finite.of_restrictScalars_finite k ↥L ↥L'
  haveI : IsGalois ↥L ↥L' := IsGalois.tower_top_of_isGalois k ↥L ↥L'
  letI : Algebra ↥L' ↥L'' := (IntermediateField.inclusion h₂).toAlgebra
  haveI : IsScalarTower k ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L' ↥L'' := Module.Finite.of_restrictScalars_finite k ↥L' ↥L''
  haveI : IsGalois ↥L' ↥L'' := IsGalois.tower_top_of_isGalois k ↥L' ↥L''
  letI : Algebra ↥L ↥L'' := (IntermediateField.inclusion (h₁.trans h₂)).toAlgebra
  haveI : IsScalarTower k ↥L ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥L'' := Module.Finite.of_restrictScalars_finite k ↥L ↥L''
  haveI : IsGalois ↥L ↥L'' := IsGalois.tower_top_of_isGalois k ↥L ↥L''
  haveI : IsScalarTower ↥L ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- restriction of automorphisms is compatible with the scalar towers
  have hF₁ : SSGRoute.PTExt.galRes k K ↥L' = (SSGRoute.PTExt.galRes k K ↥L).comp
      (SSGRoute.PTExt.galRes k ↥L ↥L') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k K ↥L ↥L'
  have hF₂ : SSGRoute.PTExt.galRes k K ↥L'' = (SSGRoute.PTExt.galRes k K ↥L').comp
      (SSGRoute.PTExt.galRes k ↥L' ↥L'') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k K ↥L' ↥L''
  have hF₃ : SSGRoute.PTExt.galRes k K ↥L'' = (SSGRoute.PTExt.galRes k K ↥L).comp
      (SSGRoute.PTExt.galRes k ↥L ↥L'') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k K ↥L ↥L''
  have hc : SSGRoute.PTExt.galRes k ↥L ↥L'' = (SSGRoute.PTExt.galRes k ↥L ↥L').comp
      (SSGRoute.PTExt.galRes k ↥L' ↥L'') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k ↥L ↥L' ↥L''
  -- `inflHIn` is `inflHLevel`, i.e. `extHMap` of the restriction map with the canonical transport
  simp only [SSGRoute.PTExt.inflHIn, SSGRoute.PTExt.inflHLevel]
  rw [resResHom_eq_transport (k := k) (K := K) (L := ↥L) (L₂ := ↥L') hF₁ M,
    resResHom_eq_transport (k := k) (K := K) (L := ↥L') (L₂ := ↥L'') hF₂ M,
    resResHom_eq_transport (k := k) (K := K) (L := ↥L) (L₂ := ↥L'') hF₃ M]
  exact extHMap_comp_eqToHom (SSGRoute.PTExt.galRes k K ↥L) (SSGRoute.PTExt.galRes k ↥L ↥L')
    (SSGRoute.PTExt.galRes k K ↥L') hF₁ (SSGRoute.PTExt.galRes k ↥L' ↥L'')
    (SSGRoute.PTExt.galRes k K ↥L'') hF₂ (SSGRoute.PTExt.galRes k ↥L ↥L'') hc M y

end Work.SSGRoute
