import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicCompletionExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocVal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia-field (unramified subextension) setup for the local different bound

Let `p` be a prime, `Q₀ = (p)` the prime of `𝓞 ℚ` it generates, `K` a number field and `Q | Q₀` a
prime of `𝓞 K`.  Write `L := Q.adicCompletion K` for the `Q`-adic completion, `B := 𝒪_L` for its
ring of integers and `ℤ_p := Q₀.adicCompletionIntegers ℚ`, `ℚ_p := Q₀.adicCompletion ℚ`.

This file installs the algebra structures between `ℤ_p, ℚ_p, B, L`, the fact that `B` is the
integral closure of `ℤ_p` in `L`, and the "inertia subfield"

`E := ℚ_p(ζ) ⊆ L`   for   `ζ ∈ B` a Teichmüller lift of a generator of the residue field,

together with its ring of integers `C := 𝒪_E = integralClosure ℤ_p E` (a Dedekind domain) and the
canonical `ℤ_p`-algebra map `φ : C → B` (`inertiaMap`).

The objects are `↥(inertiaField Q0 Q ζ)` (the field `E`) and `↥(inertiaRing Q0 Q ζ)` (the ring
`C`); the second one is the "Mathlib `B`" of the AKLB setting with base `ℤ_p` and ambient field
`E`.
-/

open IsDedekindDomain

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open scoped NumberField

noncomputable section

section Setup

variable {K : Type*} [Field K] [NumberField K]
variable (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
variable (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable [hQ : Q.asIdeal.LiesOver Q0.asIdeal]

/-- The `ℚ_p`-algebra structure on the completion `L = Q.adicCompletion K`. -/
instance adicLocExpAlgebraField : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
  RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)

/-- The `ℤ_p`-algebra structure on `B = 𝒪_L`. -/
instance adicLocExpAlgebraIntegers : Algebra (Q0.adicCompletionIntegers ℚ)
    (Q.adicCompletionIntegers K) :=
  RingHom.toAlgebra
    (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)

/-- The `ℤ_p`-algebra structure on `L`. -/
instance adicLocExpAlgebraIntegersField : Algebra (Q0.adicCompletionIntegers ℚ)
    (Q.adicCompletion K) :=
  RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ).comp
    (Q0.adicCompletionIntegers ℚ).subtype)

instance adicLocExpIsScalarTower₁ : IsScalarTower (Q0.adicCompletionIntegers ℚ)
    (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance adicLocExpIsScalarTower₂ : IsScalarTower (Q0.adicCompletionIntegers ℚ)
    (Q.adicCompletionIntegers K) (Q.adicCompletion K) :=
  Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion
    Q0 Q hQ

instance adicLocExpIsIntegralClosure : IsIntegralClosure (Q.adicCompletionIntegers K)
    (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) :=
  Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
    Q0 Q hQ

instance adicLocExpCharZero : CharZero (Q0.adicCompletion ℚ) :=
  Commons.NumberTheory.NumberField.charZero_adicCompletion (K := ℚ) Q0

theorem adicLocExp_algebraMap_injective : Function.Injective
    (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K)) :=
  (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective Q0 Q hQ).comp
    Subtype.coe_injective

instance adicLocExpIsTorsionFreeField : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ)
    (Q.adicCompletion K) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h1 : algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) r * m = 0 := by
      rwa [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (adicLocExp_algebraMap_injective Q0 Q (by rw [h2, map_zero]))
    · exact Or.inr h2

instance adicLocExpIsTorsionFreeIntegers : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ)
    (Q.adicCompletionIntegers K) :=
  Function.Injective.moduleIsTorsionFree _ Subtype.coe_injective fun _ _ => rfl

instance adicLocExpFiniteField : Module.Finite (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
  Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 Q hQ

instance adicLocExpFiniteIntegers : Module.Finite (Q0.adicCompletionIntegers ℚ)
    (Q.adicCompletionIntegers K) :=
  Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q0 Q hQ

instance adicLocExpIsIntegralField : Algebra.IsIntegral (Q0.adicCompletion ℚ)
    (Q.adicCompletion K) := inferInstance

instance adicLocExpIsSeparableField : Algebra.IsSeparable (Q0.adicCompletion ℚ)
    (Q.adicCompletion K) := inferInstance

end Setup

section Inertia

variable {K : Type*} [Field K] [NumberField K]
variable (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
variable (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
variable (ζ : Q.adicCompletionIntegers K)

/-- `ζ` viewed in `L = Q.adicCompletion K`. -/
abbrev liftElem : Q.adicCompletion K := ((ζ : Q.adicCompletionIntegers K) : Q.adicCompletion K)

/-- Every element of `B = 𝒪_L` is integral over `ℤ_p`, hence over `ℚ_p`. -/
theorem liftElem_isIntegral :
    IsIntegral (Q0.adicCompletion ℚ) (liftElem Q ζ) := by
  have h : IsIntegral (Q0.adicCompletionIntegers ℚ) (ζ : Q.adicCompletionIntegers K) :=
    IsIntegralClosure.isIntegral (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) ζ
  have h2 : IsIntegral (Q0.adicCompletionIntegers ℚ) (liftElem Q ζ) :=
    h.map (IsScalarTower.toAlgHom (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)
      (Q.adicCompletion K))
  obtain ⟨f, hfmonic, hfa⟩ := h2
  refine ⟨f.map (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)),
    hfmonic.map _, ?_⟩
  have hcomp : (algebraMap (Q0.adicCompletion ℚ) (Q.adicCompletion K)).comp
      (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)) =
      algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) :=
    RingHom.ext fun x => IsScalarTower.algebraMap_apply (Q0.adicCompletionIntegers ℚ)
      (Q0.adicCompletion ℚ) (Q.adicCompletion K) x
  show Polynomial.eval₂ (algebraMap (Q0.adicCompletion ℚ) (Q.adicCompletion K)) (liftElem Q ζ)
    (f.map (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ))) = 0
  rw [Polynomial.eval₂_map, hcomp]
  exact hfa

/-- **The inertia subfield** `E = ℚ_p(ζ) ⊆ L`. -/
def inertiaField : IntermediateField (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
  IntermediateField.adjoin (Q0.adicCompletion ℚ) {liftElem Q ζ}

instance adicLocExpFiniteInertia : FiniteDimensional (Q0.adicCompletion ℚ)
    ↥(inertiaField Q0 Q ζ) :=
  IntermediateField.adjoin.finiteDimensional (liftElem_isIntegral Q0 Q ζ)

instance adicLocExpFiniteInertiaTop : Module.Finite ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) :=
  Module.Finite.right (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K)

instance adicLocExpSeparableInertia : Algebra.IsSeparable (Q0.adicCompletion ℚ)
    ↥(inertiaField Q0 Q ζ) := inferInstance

instance adicLocExpIsIntegralInertiaTop : Algebra.IsIntegral ↥(inertiaField Q0 Q ζ)
    (Q.adicCompletion K) := inferInstance

instance adicLocExpSeparableInertiaTop : Algebra.IsSeparable ↥(inertiaField Q0 Q ζ)
    (Q.adicCompletion K) := inferInstance

instance adicLocExpIsScalarTowerInertiaFieldE : IsScalarTower (Q0.adicCompletionIntegers ℚ)
    ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  show (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K)) x =
    (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K))
      ((algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaField Q0 Q ζ)) x)
  rw [IsScalarTower.algebraMap_apply (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
      (Q.adicCompletion K) x]
  rw [IsScalarTower.algebraMap_apply (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
      ↥(inertiaField Q0 Q ζ) x]
  rw [IsScalarTower.algebraMap_apply (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K)]

instance adicLocExpIsTorsionFreeInertiaField : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ)
    ↥(inertiaField Q0 Q ζ) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h2 : algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaField Q0 Q ζ) r * m = 0 := by
        rwa [Algebra.smul_def] at h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso
        have hr0 : algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ) r ≠ 0 :=
          fun h4 => hr (Subtype.coe_injective h4)
        have h5 : algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaField Q0 Q ζ) r =
            algebraMap (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ)
              (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ) r) :=
          IsScalarTower.algebraMap_apply _ _ _ r
        rw [h5] at h3
        exact ((map_ne_zero (algebraMap (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ))).mpr hr0) h3
      · exact h3

/-- The ring of integers `C = 𝒪_E` of the inertia field, as a `ℤ_p`-subalgebra of `E`. -/
abbrev inertiaRing := integralClosure (Q0.adicCompletionIntegers ℚ) ↥(inertiaField Q0 Q ζ)

instance adicLocExpIsDedekindInertia : IsDedekindDomain (inertiaRing Q0 Q ζ) :=
  IsIntegralClosure.isDedekindDomain (Q0.adicCompletionIntegers ℚ)
    (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) (inertiaRing Q0 Q ζ)

instance adicLocExpIsIntegrallyClosedInertia : IsIntegrallyClosed (inertiaRing Q0 Q ζ) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (R := Q0.adicCompletionIntegers ℚ)
    (K := Q0.adicCompletion ℚ) (L := ↥(inertiaField Q0 Q ζ))

instance adicLocExpIsFractionRingInertia : IsFractionRing (inertiaRing Q0 Q ζ)
    ↥(inertiaField Q0 Q ζ) :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Q0.adicCompletionIntegers ℚ)
    (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) (inertiaRing Q0 Q ζ)

instance adicLocExpFiniteInertiaRing : Module.Finite (Q0.adicCompletionIntegers ℚ)
    (inertiaRing Q0 Q ζ) :=
  IsIntegralClosure.finite (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
    ↥(inertiaField Q0 Q ζ) (inertiaRing Q0 Q ζ)

instance adicLocExpIsTorsionFreeInertiaRing : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ)
    (inertiaRing Q0 Q ζ) :=
  Function.Injective.moduleIsTorsionFree _ Subtype.coe_injective fun _ _ => rfl

/-- The `ℤ_p`-algebra structure on `L` induced by `𝒪_E ⊆ E ⊆ L`. -/
instance adicLocExpIsScalarTowerInertiaField : IsScalarTower (Q0.adicCompletionIntegers ℚ)
    ↥(inertiaRing Q0 Q ζ) (Q.adicCompletion K) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  show (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K)) x =
    (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletion K))
      ((algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ)) x)
  rw [IsScalarTower.algebraMap_apply ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K)]
  rw [← IsScalarTower.algebraMap_apply (Q0.adicCompletionIntegers ℚ)
      ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)]
  rw [← IsScalarTower.algebraMap_apply (Q0.adicCompletionIntegers ℚ)
      ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K)]

/-- **The canonical `ℤ_p`-algebra map `φ : 𝒪_E → 𝒪_L`.** -/
def inertiaMap : ↥(inertiaRing Q0 Q ζ) →ₐ[Q0.adicCompletionIntegers ℚ]
    (Q.adicCompletionIntegers K) :=
  IsIntegralClosure.lift (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)
    (Q.adicCompletion K) (S := ↥(inertiaRing Q0 Q ζ))

instance adicLocExpAlgebraInertiaL : Algebra ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) :=
  (inertiaMap Q0 Q ζ).toRingHom.toAlgebra

theorem inertiaMap_apply (x : ↥(inertiaRing Q0 Q ζ)) :
    ((inertiaMap Q0 Q ζ x : Q.adicCompletionIntegers K) : Q.adicCompletion K) =
      (x : Q.adicCompletion K) :=
  IsIntegralClosure.algebraMap_lift (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)
    (Q.adicCompletion K) (S := ↥(inertiaRing Q0 Q ζ)) x

theorem inertiaMap_injective : Function.Injective (inertiaMap Q0 Q ζ) := by
  intro a b hab
  have h := congrArg (fun y : Q.adicCompletionIntegers K => (y : Q.adicCompletion K)) hab
  rw [inertiaMap_apply Q0 Q ζ a, inertiaMap_apply Q0 Q ζ b] at h
  exact Subtype.coe_injective (Subtype.coe_injective h)

instance adicLocExpIsScalarTowerInertia : IsScalarTower (Q0.adicCompletionIntegers ℚ)
    ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  show (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) x =
    (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K))
      ((algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ)) x)
  rw [RingHom.algebraMap_toAlgebra]
  exact ((inertiaMap Q0 Q ζ).commutes x).symm

instance adicLocExpIsScalarTowerInertiaL : IsScalarTower ↥(inertiaRing Q0 Q ζ)
    (Q.adicCompletionIntegers K) (Q.adicCompletion K) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  change (x : Q.adicCompletion K) =
    ((inertiaMap Q0 Q ζ x : Q.adicCompletionIntegers K) : Q.adicCompletion K)
  rw [inertiaMap_apply]

instance adicLocExpIsTorsionFreeInertia : Module.IsTorsionFree ↥(inertiaRing Q0 Q ζ)
    (Q.adicCompletionIntegers K) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h2 : algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) r * m = 0 := by
        rwa [Algebra.smul_def] at h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (inertiaMap_injective Q0 Q ζ (by
          rw [RingHom.algebraMap_toAlgebra] at h3
          simpa using h3)) hr
      · exact h3

instance adicLocExpFiniteInertia' : Module.Finite ↥(inertiaRing Q0 Q ζ)
    (Q.adicCompletionIntegers K) :=
  Module.Finite.of_restrictScalars_finite (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ)
    (Q.adicCompletionIntegers K)

instance adicLocExpIsIntegralClosureInertia : IsIntegralClosure (Q.adicCompletionIntegers K)
    ↥(inertiaRing Q0 Q ζ) (Q.adicCompletion K) :=
  IsIntegralClosure.tower_top (R := Q0.adicCompletionIntegers ℚ)
    (A := ↥(inertiaRing Q0 Q ζ)) (B := Q.adicCompletion K)
    (C := Q.adicCompletionIntegers K)

end Inertia

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
