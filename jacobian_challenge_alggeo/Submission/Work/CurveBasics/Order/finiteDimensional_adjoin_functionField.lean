/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `K(C)` is finite over `k(h)` for `h` transcendental

For a smooth, proper, geometrically irreducible curve `C` over a field `k`, the function field
`K(C)` has transcendence degree `1` over `k`.  Consequently, for any transcendental element
`h ∈ K(C)`, the extension `K(C)/k(h)` is algebraic and finitely generated, hence finite
dimensional.

The proof reads off the transcendence degree from the geometry of the curve:

* the underlying topological space of a curve has Krull dimension `≤ 1`
  (`topologicalKrullDim_left_le_one`), which gives the same bound for the ring of sections of an
  affine open (`ringKrullDimLE_sections`);
* Noether normalization expresses the ring of sections of an affine chart as a finite module over
  a polynomial ring `k[X₁,…,Xₛ]`; since Krull dimension does not increase under an injective
  integral extension (`ringKrullDimLE_of_isIntegral_of_injective`) we get `s ≤ 1`;
* transcendence degree is additive in towers, so `trdeg_k K(C) = s ≤ 1`;
* a transcendence basis of `K(C)` extending `{h}` therefore has at most one element, so it is
  exactly `{h}` and `K(C)/k(h)` is algebraic.
-/
import Mathlib
import Submission.Work.CurveBasics.Order
import Submission.Work.CurveBasics.Basic.Sections

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics.Order

open Work.CurveBasics
open _root_.Order

section CurveLemmas

variable {k : Type*} [Field k]

/-- The underlying topological space of a curve has Krull dimension at most one. -/
lemma topologicalKrullDim_left_le_one (C : Curve k) :
    topologicalKrullDim C.left ≤ (1 : WithBot ℕ∞) := by
  show krullDim (TopologicalSpace.IrreducibleCloseds C.left) ≤ (1 : WithBot ℕ∞)
  rw [krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C.left))]
  rw [krullDim_eq_iSup_coheight]
  refine iSup_le fun z => ?_
  exact_mod_cast C.coheight_le_one z

/-- The ring of sections of an affine open of a curve has Krull dimension at most one. -/
lemma ringKrullDimLE_sections (C : Curve k) {U : C.left.Opens} (hU : IsAffineOpen U) :
    Ring.KrullDimLE 1 Γ(C.left, U) := by
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim, Nat.cast_one,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C.left, U)]
  change topologicalKrullDim (Spec Γ(C.left, U)) ≤ 1
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le C.left U).trans (topologicalKrullDim_left_le_one C)

/-- The ring of sections of an affine open of a curve is finitely generated over `k`. -/
lemma algebra_finiteType_sections (C : Curve k) {U : C.left.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k Γ(C.left, U) := by
  rw [← RingHom.finiteType_algebraMap]
  have h1 : (C.hom.appLE ⊤ U (le_top : U ≤ C.hom ⁻¹ᵁ ⊤)).hom.FiniteType :=
    C.hom.finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of k))) hU le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv :
      CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of k), ⊤)).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact h1.comp h2

end CurveLemmas

section General

/-- Krull dimension does not increase under an injective integral extension of commutative rings. -/
lemma ringKrullDimLE_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) {n : ℕ}
    (hn : Ring.KrullDimLE n S) : Ring.KrullDimLE n R := by
  haveI : Algebra.HasGoingUp R S := Algebra.HasGoingUp.of_isIntegral
  refine ⟨?_⟩
  rw [krullDim, iSup_le_iff]
  intro l
  have hker : RingHom.ker (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    rw [show RingHom.ker (algebraMap R S) = ⊥ from
      (RingHom.injective_iff_ker_eq_bot _).mp h]
    exact bot_le
  obtain ⟨P, -, hPprime, hPunder⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RelSeries.head l).asIdeal ⊥ hker
  haveI : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPunder.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  have h1 : (L.length : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
    L.length_le_krullDim.trans hn.krullDim_le
  rwa [hlen] at h1

end General

section CurveLemmasTwo

variable {k : Type*} [Field k]

/-- The function field of a curve is algebraic over the ring of sections of any nonempty
affine open: every element of `K(C)` is a quotient of two regular functions. -/
lemma isAlgebraic_sections_functionField (C : Curve k) {U : C.left.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : Algebra.IsAlgebraic Γ(C.left, U) C.functionField := by
  haveI : IsFractionRing Γ(C.left, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C.left U hU
  have hinj : Function.Injective (algebraMap Γ(C.left, U) C.functionField) :=
    IsFractionRing.injective _ _
  rw [Algebra.isAlgebraic_def]
  intro x
  obtain ⟨a, b, hb, hxy⟩ := IsFractionRing.div_surjective Γ(C.left, U) x
  rw [← hxy]
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbne : algebraMap Γ(C.left, U) C.functionField b ≠ 0 := by
    intro h
    rw [← map_zero (algebraMap Γ(C.left, U) C.functionField)] at h
    exact hb' (hinj h)
  have hmem : algebraMap Γ(C.left, U) C.functionField b ∈ nonZeroDivisors C.functionField :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hbne
  have h1 : IsAlgebraic Γ(C.left, U) (algebraMap Γ(C.left, U) C.functionField b) :=
    isAlgebraic_algebraMap b
  have h2 : IsAlgebraic Γ(C.left, U)
      (algebraMap Γ(C.left, U) C.functionField b *
        (algebraMap Γ(C.left, U) C.functionField a /
          algebraMap Γ(C.left, U) C.functionField b)) := by
    have hmul : algebraMap Γ(C.left, U) C.functionField b *
        (algebraMap Γ(C.left, U) C.functionField a /
          algebraMap Γ(C.left, U) C.functionField b)
        = algebraMap Γ(C.left, U) C.functionField a := by
      rw [mul_comm, div_mul_cancel₀ _ hbne]
    rw [hmul]
    exact isAlgebraic_algebraMap a
  exact IsAlgebraic.of_mul hmem h1 h2

end CurveLemmasTwo

open Work.CurveBasics in
theorem finiteDimensional_adjoin_functionField {k : Type*} [Field k] (C : Curve k)
    {h : C.functionField} (hh : Transcendental k h) :
    FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField := by
  classical
  -- an affine chart of the curve
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C.left)
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp C.left.isBasis_affineOpens)
      (show x₀ ∈ (⊤ : C.left.Opens) from trivial)
  haveI hUne : Nonempty U := ⟨⟨x₀, hxU⟩⟩
  -- the chart ring is the fraction ring of the function field
  haveI hfrac : IsFractionRing Γ(C.left, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C.left U hU
  have hinj : Function.Injective (algebraMap Γ(C.left, U) C.functionField) :=
    IsFractionRing.injective _ _
  haveI hdom : IsDomain Γ(C.left, U) := Function.Injective.isDomain _ hinj
  haveI hfg : Algebra.FiniteType k Γ(C.left, U) := algebra_finiteType_sections C hU
  haveI hstAE : IsScalarTower k Γ(C.left, U) C.functionField :=
    Curve.isScalarTower_sections C U
  haveI halgAE : Algebra.IsAlgebraic Γ(C.left, U) C.functionField :=
    isAlgebraic_sections_functionField C hU
  -- the chart ring has Krull dimension at most one
  have hdimA : Ring.KrullDimLE 1 Γ(C.left, U) := ringKrullDimLE_sections C hU
  -- Noether normalization
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k Γ(C.left, U)
  letI hAlgB : Algebra (MvPolynomial (Fin s) k) Γ(C.left, U) := g.toAlgebra
  haveI hSTB : IsScalarTower k (MvPolynomial (Fin s) k) Γ(C.left, U) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    simp [RingHom.algebraMap_toAlgebra]
  haveI hFaithB : FaithfulSMul (MvPolynomial (Fin s) k) Γ(C.left, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      simpa [RingHom.algebraMap_toAlgebra] using hg_inj)
  haveI hfinBA : Module.Finite (MvPolynomial (Fin s) k) Γ(C.left, U) := hg_fin
  haveI hIntBA : Algebra.IsIntegral (MvPolynomial (Fin s) k) Γ(C.left, U) :=
    Algebra.IsIntegral.of_finite _ _
  haveI halgBA : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) Γ(C.left, U) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  -- consequently `s ≤ 1`
  have hdimB : Ring.KrullDimLE 1 (MvPolynomial (Fin s) k) :=
    ringKrullDimLE_of_isIntegral_of_injective hg_inj hdimA
  have hsle : s ≤ 1 := by
    have h := hdimB.krullDim_le
    rw [← ringKrullDim, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] at h
    exact_mod_cast h
  -- transcendence degree of the chart ring
  have htrA : Algebra.trdeg k Γ(C.left, U) = (s : Cardinal) := by
    rw [← trdeg_add_eq (A := Γ(C.left, U)) k (MvPolynomial (Fin s) k),
      trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := Γ(C.left, U)), add_zero,
      MvPolynomial.trdeg_of_isDomain]
    simp
  -- transcendence degree of the function field
  haveI hFaithAE : FaithfulSMul Γ(C.left, U) C.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have htrE : Algebra.trdeg k C.functionField = (s : Cardinal) := by
    rw [← trdeg_add_eq (A := C.functionField) k Γ(C.left, U),
      trdeg_eq_zero (R := Γ(C.left, U)) (A := C.functionField), add_zero, htrA]
  have htrle : Algebra.trdeg k C.functionField ≤ (1 : Cardinal) := by
    rw [htrE]
    exact_mod_cast hsle
  -- a transcendence basis of `K(C)` over `k` extending `{h}` has at most one element
  obtain ⟨t, ht_sub, ht_basis⟩ :=
    exists_isTranscendenceBasis_superset (R := k) (s := ({h} : Set C.functionField))
      (by
        haveI : Subsingleton ↥({h} : Set C.functionField) :=
          ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
        exact (algebraicIndependent_singleton_iff
          (i := (⟨h, Set.mem_singleton h⟩ : ↥({h} : Set C.functionField)))).mpr hh)
  have hth : h ∈ t := ht_sub (Set.mem_singleton h)
  have htcard : Cardinal.mk t ≤ 1 := by
    rw [ht_basis.cardinalMk_eq_trdeg]
    exact htrle
  have hsub : t.Subsingleton := Cardinal.mk_le_one_iff_set_subsingleton.mp htcard
  have ht_eq : t = {h} := Set.eq_singleton_iff_unique_mem.mpr ⟨hth, fun y hy => hsub hy hth⟩
  -- hence `K(C)` is algebraic over `k(h)`
  haveI halg : Algebra.IsAlgebraic (IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField := by
    have hb := ht_basis.isAlgebraic_field
    rwa [Subtype.range_coe, ht_eq] at hb
  -- `K(C)` is essentially of finite type over `k(h)`, hence finite over it
  haveI hEFTA : Algebra.EssFiniteType Γ(C.left, U) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors Γ(C.left, U))
  haveI hEFT : Algebra.EssFiniteType k C.functionField :=
    Algebra.EssFiniteType.comp k Γ(C.left, U) C.functionField
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField :=
    Algebra.EssFiniteType.of_comp k _ C.functionField
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end Work.CurveBasics.Order
