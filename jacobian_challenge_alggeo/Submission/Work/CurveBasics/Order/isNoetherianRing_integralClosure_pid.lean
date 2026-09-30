/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The integral closure of a PID in a finite field extension is Noetherian

Let `A` be a principal ideal domain with fraction field `K`, and let `L/K` be a finite field
extension (possibly inseparable).  We show that the integral closure `B` of `A` in `L` is a
Noetherian ring.

This is the `A`-principal case of the Krull-Akizuki theorem.  The proof does *not* assume
separability (which is what Mathlib's `integralClosure.isNoetherianRing` requires); instead it
uses the following chain of facts, valid over any PID:

* for every maximal ideal `p` of `A`, the `A/p`-vector space `B/pB` is finite dimensional
  (`submodule_finite_quotient_maximal`, proved from the PID structure by clearing denominators);
* hence for every `0 ≠ a ∈ A` the `A`-module `B/aB` has finite length
  (`isFiniteLength_quotient_of_ne_zero`, by UFD factorisation of `a`);
* finally, if `B/aB` has finite length for every `0 ≠ a ∈ A`, then `B` is Noetherian
  (`isNoetherianRing_of_finiteLength`): for an ideal `I`, pick `0 ≠ a` in `I ∩ A`, so that
  `I/aB` is a submodule of the finite-length module `B/aB`, hence finitely generated.
-/
import Mathlib
import Submission.Work.CurveBasics.Order.submodule_finite_quotient_maximal
import Submission.Work.CurveBasics.Order.isFiniteLength_quotient_of_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

open scoped Classical

namespace Work.CurveBasics.Order

/-- A finite-dimensional module over a quotient `A ⧸ p` has finite length. -/
theorem isFiniteLength_of_finite_module_over_quotient_maximal
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsMaximal]
    {N : Type*} [AddCommGroup N] [Module (A ⧸ p) N] [Module.Finite (A ⧸ p) N] :
    IsFiniteLength (A ⧸ p) N := by
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

/-- For a maximal ideal `p` of `A`, the quotient `B ⧸ pB` of the integral closure `B` of the PID
`A` in a finite extension `L/K` has finite length as an `A`-module. -/
theorem isFiniteLength_quotient_maximal
    {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {L : Type*} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    (p : Ideal A) [p.IsMaximal] :
    IsFiniteLength A (↥(integralClosure A L) ⧸ (p • (⊤ : Submodule A ↥(integralClosure A L)))) := by
  let N := ↥(integralClosure A L) ⧸ (p • (⊤ : Submodule A ↥(integralClosure A L)))
  have hfin : Module.Finite (A ⧸ p) N :=
    submodule_finite_quotient_maximal (K := FractionRing A) p (integralClosure A L).toSubmodule
  have hFL : IsFiniteLength (A ⧸ p) N :=
    isFiniteLength_of_finite_module_over_quotient_maximal p (N := N)
  have key : Module.length A N = Module.length (A ⧸ p) N :=
    Module.length_eq_of_surjective (S := A) (R := A ⧸ p) Ideal.Quotient.mk_surjective
  have hne : Module.length A N ≠ ⊤ := by
    rw [key]
    exact (Module.length_ne_top_iff (R := A ⧸ p) (M := N)).mpr hFL
  exact (Module.length_ne_top_iff (R := A) (M := N)).mp hne

/-- **Krull-Akizuki, step 3.**  If `B` is an integral extension of the PID `A` such that `B/aB` has
finite length as an `A`-module for every `0 ≠ a ∈ A`, then `B` is Noetherian. -/
theorem isNoetherianRing_of_finiteLength
    {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Algebra.IsIntegral A B]
    (hgen : ∀ a : A, a ≠ 0 → IsFiniteLength A (B ⧸ (Ideal.span {a} • (⊤ : Submodule A B)))) :
    IsNoetherianRing B := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  have hunder : Ideal.under A I ≠ ⊥ := fun h => hI (Ideal.eq_bot_of_under_eq_bot h)
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (Ideal.under A I)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hunder
    rw [ha]
    exact Submodule.span_singleton_eq_bot.mpr rfl
  have hb : algebraMap A B a ∈ I := by
    have : a ∈ Ideal.under A I := by rw [ha]; exact Submodule.mem_span_singleton_self a
    rwa [Ideal.under, Ideal.mem_comap] at this
  set K : Ideal B := Ideal.span {algebraMap A B a} with hK
  have hKI : K ≤ I := by
    rw [hK]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hb)
  have hsub : Ideal.span {a} • (⊤ : Submodule A B) = K.restrictScalars A := by
    rw [hK, Ideal.smul_top_eq_map, Ideal.map_span, Set.image_singleton]
  have hFL : IsFiniteLength A (B ⧸ K.restrictScalars A) := by
    have h := hgen a ha0
    rw [hsub] at h
    exact h
  haveI hNA : IsNoetherian A (B ⧸ K.restrictScalars A) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hFL).1
  have hNA' : IsNoetherian A (B ⧸ K) := hNA
  haveI hNB : IsNoetherian B (B ⧸ K) := isNoetherian_of_tower A hNA'
  have hIK : (Submodule.map (Submodule.mkQ K) (I : Submodule B B)).FG :=
    (isNoetherian_def.mp hNB) _
  have hFK : K.FG := Submodule.IsPrincipal.fg inferInstance
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ K) hIK ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hKI]
  exact hFK

/-- **Krull-Akizuki for principal ideal domains.**  The integral closure of a principal ideal
domain `A` in a finite field extension `L` of its fraction field is a Noetherian ring.

Unlike Mathlib's `integralClosure.isNoetherianRing`, this does not assume that `L` is separable
over `FractionRing A`. -/
theorem isNoetherianRing_integralClosure_pid {A : Type*} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] {L : Type*} [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] :
    IsNoetherianRing ↥(integralClosure A L) := by
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L]
    exact (FaithfulSMul.algebraMap_injective (FractionRing A) L).comp
      (FaithfulSMul.algebraMap_injective A (FractionRing A))
  haveI hFaith : FaithfulSMul A ↥(integralClosure A L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hAL
    have h2 := congrArg (fun z : ↥(integralClosure A L) => (z : L)) hxy
    simpa using h2
  haveI hInt : Algebra.IsIntegral A ↥(integralClosure A L) :=
    IsIntegralClosure.isIntegral_algebra (R := A) (A := ↥(integralClosure A L)) (B := L)
  exact isNoetherianRing_of_finiteLength (fun a ha =>
    isFiniteLength_quotient_of_ne_zero (fun p hp => isFiniteLength_quotient_maximal p) a ha)

end Work.CurveBasics.Order
