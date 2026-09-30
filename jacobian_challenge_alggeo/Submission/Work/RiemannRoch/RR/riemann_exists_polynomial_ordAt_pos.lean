/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A polynomial vanishing at a prescribed place where `t` is regular

Let `C` be a smooth proper geometrically irreducible curve over a field `k`, let
`t ∈ K(C)` be transcendental over `k`, and let `P` be a place of `C` at which `t` is
regular (`0 ≤ ord_P t`).  Then there is a nonzero polynomial `μ ∈ k[X]` with
`0 < ord_P (μ(t))`: some nonzero polynomial expression in `t` vanishes at `P`.

The proof is the usual one: `t` being regular at `P`, it lies in the local ring `O_{C,P}` and
has a residue class `t̄` in the residue field `κ(P) = O_{C,P}/𝔪`.  The residue field of a
closed point of a curve is finite over `k` (`Work.CurveBasics.Place.residueDegree_pos` and
`Work.CurveBasics.Place.degree_eq_finrank`, packaged as
`Work.CurveBasics.Linear.finiteDimensional_residueField`), so `t̄` is algebraic over `k`;
taking `μ` to be its minimal polynomial, `μ(t)` reduces to `0` modulo `𝔪`, i.e. lies in the
maximal ideal of the valuation ring at `P`, which is exactly `0 < ord_P (μ(t))`
(`Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt`).

Note that the hypothesis `[K(C) : k(t)] < ∞` is not needed: the argument only uses
finiteness of the residue field extensions, which holds for every closed point of a curve.
-/
import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics in
theorem riemann_exists_polynomial_ordAt_pos {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) (t : C.functionField) (ht : Transcendental k t)
    [FiniteDimensional (IntermediateField.adjoin k ({t} : Set C.functionField)) C.functionField]
    (P : C.Place) (hP : 0 ≤ C.ordAt t P) :
    ∃ μ : Polynomial k, μ ≠ 0 ∧ 0 < C.ordAt (Polynomial.aeval t μ) P := by
  classical
  -- the local ring at `P` is a discrete valuation ring
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk P.point) :=
    Work.CurveBasics.Place.isDiscreteValuationRing P
  letI hAlg : Algebra k (C.left.presheaf.stalk P.point) :=
    Work.CurveBasics.Linear.instAlgebraStalk C P
  haveI hST : IsScalarTower k (C.left.presheaf.stalk P.point) C.functionField :=
    Work.CurveBasics.Linear.isScalarTower_stalk_field C P
  -- `t` is regular at `P`, hence lies in the local ring
  have htO : t ∈ P.valuationSubring :=
    (Work.CurveBasics.Place.mem_valuationSubring_iff C P t).mpr hP
  have ht_mem : t ∈ Subring.map (algebraMap (C.left.presheaf.stalk P.point) C.functionField) ⊤ := by
    rw [IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
    exact htO
  obtain ⟨t₀, -, ht₀⟩ := Subring.mem_map.mp ht_mem
  -- the canonical identification of the local ring with the valuation ring at `P`
  let e : (C.left.presheaf.stalk P.point) ≃+* ↥(P.valuationSubring) :=
    IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk P.point)
      (K := C.functionField)
  have he_coe : ∀ y : C.left.presheaf.stalk P.point,
      ((e y : ↥(P.valuationSubring)) : C.functionField) =
        algebraMap (C.left.presheaf.stalk P.point) C.functionField y := by
    intro y
    show ((IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk P.point)
      (K := C.functionField) y : ↥(P.valuationSubring)) : C.functionField) = _
    rw [IsDiscreteValuationRing.equivValuationSubring]
    rfl
  -- the residue field of a closed point of a curve is finite, hence algebraic, over `k`
  haveI hfin : FiniteDimensional k (C.left.residueField P.point) :=
    Work.CurveBasics.Linear.finiteDimensional_residueField C P
  haveI halg : Algebra.IsAlgebraic k (C.left.residueField P.point) :=
    Algebra.IsAlgebraic.of_finite k _
  haveI hint : Algebra.IsIntegral k (C.left.residueField P.point) :=
    Algebra.IsAlgebraic.isIntegral
  -- the minimal polynomial of the residue class of `t`
  let tbar : C.left.residueField P.point := IsLocalRing.residue _ t₀
  let μ : Polynomial k := minpoly k tbar
  have hμne : μ ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral tbar)
  have hμeval : Polynomial.aeval tbar μ = 0 := minpoly.aeval k tbar
  -- `μ(t)` is the image of `μ(t₀)`
  have haeval_eq : Polynomial.aeval t μ =
      algebraMap (C.left.presheaf.stalk P.point) C.functionField
        (Polynomial.aeval t₀ μ) := by
    rw [← ht₀]
    let φ : (C.left.presheaf.stalk P.point) →ₐ[k] C.functionField :=
      IsScalarTower.toAlgHom k (C.left.presheaf.stalk P.point) C.functionField
    have hφ : ∀ x, φ x = algebraMap (C.left.presheaf.stalk P.point) C.functionField x :=
      fun x => rfl
    simpa only [hφ] using Polynomial.aeval_algHom_apply φ t₀ μ
  -- the residue map of the local ring, as a `k`-algebra homomorphism
  let ρ : (C.left.presheaf.stalk P.point) →ₐ[k] C.left.residueField P.point :=
    { IsLocalRing.residue _ with
      commutes' := fun c => Work.CurveBasics.Linear.residue_algebraMap_eq C P c }
  have hres0 : ρ (Polynomial.aeval t₀ μ) = 0 := by
    have h4 : Polynomial.aeval (ρ t₀) μ = ρ (Polynomial.aeval t₀ μ) :=
      Polynomial.aeval_algHom_apply ρ t₀ μ
    have h5 : ρ t₀ = tbar := rfl
    rw [← h4, h5, hμeval]
  have hmem0 : Polynomial.aeval t₀ μ ∈
      IsLocalRing.maximalIdeal (C.left.presheaf.stalk P.point) := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact hres0
  -- hence `μ(t₀)` is not a unit, and neither is its image in the valuation ring
  have hnonunit : ¬ IsUnit (Polynomial.aeval t₀ μ) := by
    change Polynomial.aeval t₀ μ ∈
      IsLocalRing.maximalIdeal (C.left.presheaf.stalk P.point)
    exact hmem0
  have hnonunit' : ¬ IsUnit (e (Polynomial.aeval t₀ μ)) := by
    intro hu
    have h1 : IsUnit (e.symm (e (Polynomial.aeval t₀ μ))) :=
      IsUnit.map (e.symm : ↥(P.valuationSubring) →+* (C.left.presheaf.stalk P.point)) hu
    rw [RingEquiv.symm_apply_apply] at h1
    exact hnonunit h1
  have hmemK : Polynomial.aeval t μ ∈ P.valuationSubring := by
    rw [haeval_eq, ← he_coe (Polynomial.aeval t₀ μ)]
    exact (e (Polynomial.aeval t₀ μ)).2
  let a : ↥(P.valuationSubring) := ⟨Polynomial.aeval t μ, hmemK⟩
  have hkey : e (Polynomial.aeval t₀ μ) = a := by
    apply Subtype.ext
    rw [he_coe]
    exact haeval_eq.symm
  -- `μ(t)` lies in the maximal ideal of the valuation ring at `P`
  have hmemM : a ∈ IsLocalRing.maximalIdeal ↥(P.valuationSubring) := by
    rw [← hkey]
    change e (Polynomial.aeval t₀ μ) ∈ nonunits ↥(P.valuationSubring)
    exact hnonunit'
  have hane : (a : C.functionField) ≠ 0 := by
    change Polynomial.aeval t μ ≠ 0
    intro h
    exact hμne ((transcendental_iff.mp ht μ) h)
  -- membership in the maximal ideal is positivity of the order of vanishing
  have h1 : (1 : ℤ) ≤ C.ordAt (Polynomial.aeval t μ) P := by
    have hm1 : a ∈ IsLocalRing.maximalIdeal ↥(P.valuationSubring) ^ 1 := by
      rw [pow_one]
      exact hmemM
    have h := (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt C P a hane 1).mp hm1
    simpa using h
  exact ⟨μ, hμne, by omega⟩

end Work.RiemannRoch.RR
