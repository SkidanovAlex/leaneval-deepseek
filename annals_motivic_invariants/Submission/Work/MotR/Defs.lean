/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotR
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.PointlessTwist.Defs
import Submission.Work.FFResidual.All

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotR` — the arithmetic of Lin–Shinder, Theorem 1.2 (1)

The area `Submission/Work/MotR` supplies the **arithmetic** input of the classes (a)–(d) of
Lin–Shinder, *Motivic invariants of birational maps*, Annals of Math. **199** (1), 2024,
Theorem 1.2 (1): a cyclic quintic extension `L/𝕜` of the field of constants of the class at hand,
together with a **place** of `L` at which the extension is totally ramified and at which the
constant Tate curve `E(𝕜)` has good reduction with non-vanishing marker.

## The vocabulary of the area

* `Work.MotR.ratFuncPlace B c` — **the place of `B(t)` at `t = c`**: the localization of `B[t]` at
  the maximal ideal `(X - C c)`, a `FunctionFieldPlace B (RatFunc B)` (in the sense of
  `Work.FFResidual`, i.e. a discrete valuation ring with fraction field `B(t)` containing the
  constants, with the chosen uniformizer `X - C c`).  It is the place at which the Kummer descent
  (`SubmitWork.MotR.KummerDescent`) and the Artin–Schreier extension (`Work.MotR.ArtinSchreier`)
  of the classes (b), (c), (d) are constructed.
* `Work.MotR.TotallyRamified n P` — **a place of an extension totally ramified of degree `n`
  above a place `P` of the base field**: the uniformizer of `P` has order exactly `n` at the place
  of the extension (so `e = n`, and together with `[L : K] = n` this is `e = n`, `f = 1`).
* `Work.MotR.HasCyclicQuinticAt` — the *Prop*-level form of the deliverable of the area: a cyclic
  quintic extension of `𝕜` together with such a place.

## Main results (see `NOTES.md` for the state of each)

* `Work.MotR.exists_transcendental_of_pos_topologicalKrullDim` (`Transcendental`, node **R5**) —
  a positive-dimensional `𝔽`-variety has a transcendental function on it.
* `Work.MotR.exists_cyclicExtension_kummerDescent` (`KummerDescent`, node **R2**) — the Kummer
  descent: a cyclic quintic extension of `B(t)`, totally ramified at the place `t = ζ₅ + a`.
* `Work.MotR.exists_cyclicExtension_artinSchreier` (`ArtinSchreier`, node **R3**) — the
  characteristic-`5` Artin–Schreier version, totally ramified at the place `t = a`.
* `Work.MotR.hasPointlessTwist_numberField` (`NumberField`, node **R1**) and
  `Work.MotR.hasPointlessTwist_functionField` (`FunctionField`, node **R4**) — the arithmetic
  halves of the classes (a) and (b)–(d).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

namespace Work.MotR

noncomputable section

/-! ## 1. The place of `B(t)` at `t = c` -/

/-- **The place of `B(t)` at a monic irreducible polynomial `h ∈ B[t]`**: the localization of
`B[t]` at the prime `(h)`, a discrete valuation ring with fraction field `B(t)` containing the
constants, whose uniformizer is the image of `h`.  Its residue field is `B[t]/(h)`.

This is the general place construction of this area; `ratFuncPlace` (`h = t - c`) and
`placeOfMinpoly` (`h = minpoly_B x`) are the two instances that are used. -/
noncomputable def ratFuncPlaceAt (B : Type) [Field B] (h : Polynomial B) (hirr : Irreducible h) :
    Work.FFResidual.FunctionFieldPlace B (RatFunc B) :=
  let p : Ideal (Polynomial B) := Ideal.span {h}
  have hp : p.IsPrime :=
    (Ideal.span_singleton_prime (fun h0 => hirr.ne_zero (by rw [h0]))).mpr hirr.prime
  letI : p.IsPrime := hp
  let R := Localization.AtPrime p
  have hne : p ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact fun h0 => hirr.ne_zero (by rw [h0])
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial B) hne R
  letI hAlgF : Algebra B R :=
    RingHom.toAlgebra ((algebraMap (Polynomial B) R).comp (algebraMap B (Polynomial B)))
  letI hAlgR : Algebra R (RatFunc B) :=
    RingHom.toAlgebra
      (((RatFunc.toFractionRingRingEquiv B).symm : FractionRing (Polynomial B) →+* RatFunc B).comp
        (algebraMap R (FractionRing (Polynomial B))))
  haveI htow1 : @IsScalarTower (Polynomial B) R (RatFunc B)
      (Algebra.toSMul) (Algebra.toSMul) (Algebra.toSMul) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap (Polynomial B) (RatFunc B) x =
      (RatFunc.toFractionRingRingEquiv B).symm
        (algebraMap R (FractionRing (Polynomial B)) (algebraMap (Polynomial B) R x))
    rw [← IsScalarTower.algebraMap_apply (Polynomial B) R (FractionRing (Polynomial B)) x]
    exact (RatFunc.ofFractionRing_algebraMap x).symm
  haveI hfr : IsFractionRing R (RatFunc B) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R (RatFunc B)
  haveI htow2 : @IsScalarTower B R (RatFunc B)
      (Algebra.toSMul) (Algebra.toSMul) (Algebra.toSMul) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    calc algebraMap B (RatFunc B) x
        = algebraMap (Polynomial B) (RatFunc B) (algebraMap B (Polynomial B) x) :=
            IsScalarTower.algebraMap_apply B (Polynomial B) (RatFunc B) x
      _ = algebraMap R (RatFunc B)
            (algebraMap (Polynomial B) R (algebraMap B (Polynomial B) x)) :=
            IsScalarTower.algebraMap_apply (Polynomial B) R (RatFunc B) _
      _ = algebraMap R (RatFunc B) (algebraMap B R x) := rfl
  { R := R
    π := algebraMap (Polynomial B) R h
    isUniformizer := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_span, Set.image_singleton] }

/-- **The place of the rational function field `B(t)` at `t = c`.**

The localization `B[t]_{(t - c)}` is a discrete valuation ring (`B[t]` is a principal ideal domain,
so the localization at a nonzero prime is a discrete valuation ring), its fraction field is `B(t)`
and it contains the constants `B`; its maximal ideal is generated by the image of `t - c`, so
`t - c` is a uniformizer.  This is the place at which the local theory of the classes (b), (c), (d)
of the function-field case of Lin–Shinder is run: the Artin–Schreier construction at `t = a` in
characteristic `5` uses `ratFuncPlace B a`. -/
noncomputable def ratFuncPlace (B : Type) [Field B] (c : B) :
    Work.FFResidual.FunctionFieldPlace B (RatFunc B) :=
  ratFuncPlaceAt B (Polynomial.X - Polynomial.C c) (Polynomial.irreducible_X_sub_C c)

/-- **The place of `B(t)` "at `t = x`"**, for an element `x` of a finite extension field `B'` of
`B`: the place whose residue field is `B(x)`, i.e. the localization of `B[t]` at the prime
generated by the minimal polynomial of `x` over `B`.

This is the place at which the Kummer descent (node **R2**) of the classes (b), (c), (d) is
constructed: for `B' = B(ζ₅)` and `x = ζ₅ + a`, its residue field is the field `B(ζ₅)` generated by
the fifth roots of unity, so that the place *splits completely* in `B(ζ₅)(t)` and the Kummer
element `∏ᵢ (t - ζ₅^{g^i} - a)^{g^{-i}}` has order one at each of the `d = [B(ζ₅):B]` places above
it. -/
noncomputable def placeOfMinpoly (B : Type) [Field B] (B' : Type) [Field B'] [Algebra B B']
    [FiniteDimensional B B'] (x : B') : Work.FFResidual.FunctionFieldPlace B (RatFunc B) :=
  ratFuncPlaceAt B (minpoly B x) (minpoly.irreducible (IsIntegral.of_finite B x))

/-! ## 2. Total ramification at a place -/

section TotalRamification

variable {𝔽 : Type} [Field 𝔽] {K : Type} [Field K] [Algebra 𝔽 K]

/-- **A place of the extension `L` of `K`, above the place `P` of `K`, totally ramified of degree
`n`.**

`R'` is the valuation ring of a place of `L` which lies above `P` (the constants of `K` are
integral at `R'` compatibly: `P.R → R' → L` is a tower, and `P.R → K → L` agrees with it), and a
uniformizer of `P` becomes, in `L`, a unit `ε` of `R'` times the `n`-th power of a uniformizer
`π'` of `R'`.

Together with `Module.finrank K L = n` this is "`e = n`" at the place, and hence (since
`e · f · r = n` and `r ≥ 1`) `f = 1`: the residue extension is trivial.

**Scope.**  This records the *ramification of the uniformizers* only.  For the assembly with the
reduction map on the points of a constant elliptic curve one furthermore needs the Galois generator
`σ` of `L/K` to preserve `R'` and to act trivially on its residue ring, and the compatibility of
`P.R → K → L` with `P.R → R' → L`; that richer datum is not carried here.  The interface actually
used by the function-field classes is the local data of
`Work.MotR.KummerDescent.KummerPlaceData` and `Work.MotR.R4.hasPointlessTwist_of_kummerPlaceData`
(see `Submission/Work/MotR/NOTES.md`). -/
structure TotallyRamified (n : ℕ) {P : Work.FFResidual.FunctionFieldPlace 𝔽 K}
    {L : Type} [Field L] [Algebra K L] where
  /-- The valuation ring of the place of the extension. -/
  R' : Type
  [commRing' : CommRing R']
  [isDomain' : IsDomain R']
  [isDiscreteValuationRing' : IsDiscreteValuationRing R']
  [algebra' : Algebra R' L]
  [isFractionRing' : IsFractionRing R' L]
  /-- The place of `L` lies above `P`: `P.R → R' → L` is a tower. -/
  [algebraR : Algebra P.R R']
  [algebraRL : Algebra P.R L]
  [tower' : IsScalarTower P.R R' L]
  /-- A uniformizer of the place of the extension. -/
  π' : R'
  /-- `π'` generates the maximal ideal of `R'`. -/
  isUniformizer' : IsLocalRing.maximalIdeal R' = Ideal.span {π'}
  /-- The unit relating the two uniformizers. -/
  ε : R'
  /-- `ε` is a unit of `R'`. -/
  isUnit_ε : IsUnit ε
  /-- **Total ramification**: the uniformizer of `P` is `ε · π' ^ n` in `L`. -/
  uniformizer_eq : algebraMap K L (algebraMap P.R K P.π) = algebraMap R' L (ε * π' ^ n)

/-- The `Prop`-level form of `TotallyRamified`. -/
def HasTotallyRamified (n : ℕ) (P : Work.FFResidual.FunctionFieldPlace 𝔽 K)
    (L : Type) [Field L] [Algebra K L] : Prop := Nonempty (TotallyRamified n (P := P) (L := L))

end TotalRamification

/-! ## 3. The class statements of the area

The arithmetic half of the classes of Theorem 1.2 (1), in the `DecidableEq`-free form used by the
class theorems of the workspace: there is a curve `C₅` over `𝕜` with a rational point of order `5`
and `j ≠ 1728`, and a cyclic quintic extension `L/𝕜`, such that the twist of `C₅` by the cocycle
`σ ↦ P` is pointless (`Work.PointlessTwist.PointlessOf`). -/

/-- **The arithmetic half of a field class**: a `FiveTorsionCurve` over `𝕜` and a cyclic quintic
extension `L/𝕜` whose twist by the cocycle `σ ↦ P` has no `𝕜`-point.  This is
`Work.PointlessTwist.HasPointlessOf 𝕜` (`Work.PointlessTwist.Defs`), restated in this area's
vocabulary so that the class theorems of `Work.MotR` can be compared with each other. -/
def HasTwistData (𝕜 : Type) [Field 𝕜] : Prop :=
  ∃ dec : DecidableEq 𝕜, @Work.PointlessTwist.HasPointlessOf 𝕜 inferInstance dec

/-- The same with `DecidableEq 𝕜` as an explicit instance (the form in which the number-field and
function-field classes are proved). -/
def HasTwistData' (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  Work.PointlessTwist.HasPointlessOf 𝕜

theorem hasTwistData_of_hasTwistData' {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : Work.PointlessTwist.HasPointlessOf 𝕜) : HasTwistData 𝕜 := ⟨‹DecidableEq 𝕜›, h⟩

end

/-! ## 4. Cyclic quintic subextensions -/

/-- **`E` has a cyclic quintic subextension over `K`**: an intermediate field `L₀` which is a
Galois extension of `K` of degree `5` (hence cyclic: the Galois group has `5` elements, so it is
generated by any non-identity element, and `Work.TorsorExistence.CyclicExtension.of_isGalois`
packages it).

The explicit `letI` is needed because `Algebra K ↥L₀` is not found by type class search for an
`IntermediateField` whose ambient field is an `AdjoinRoot`. -/
def HasCyclicQuinticSubextension (K E : Type) [Field K] [Field E] [Algebra K E] : Prop :=
  ∃ L₀ : IntermediateField K E,
    (letI : Algebra K L₀ := inferInstance;
      IsGalois K L₀ ∧ Module.finrank K L₀ = 5)

/-! ## 5. The extension of a place to a finite separable extension -/

/-- **A place of `𝕜` above the place `A` of `K₀`.**

`A` is the valuation ring of a place of `K₀` (a discrete valuation ring with `IsFractionRing A K₀`),
`𝕜 ⊇ K₀` is a finite separable extension, and `C` is the valuation ring of a place of `𝕜` lying
*above* it: `A → C → 𝕜` is a tower of algebras, `C` has fraction field `𝕜`, and the maximal ideal of
`C` contracts to that of `A` (so the place of `𝕜` restricts to the given place of `K₀`).

This is the standard "extension of a place" statement (the integral closure of `A` in `𝕜` is a
Dedekind domain; localize it at a prime above the maximal ideal of `A`), and it is the piece of the
function-field classes (b)–(d) that turns a place of the rational function field `𝔽'(t)` into a
place of the function field `𝕜 = X.functionField` of the variety. -/
structure DVRAbove (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (K₀ : Type) [Field K₀]
    [Algebra A K₀]
    (𝕜 : Type) [Field 𝕜] [Algebra K₀ 𝕜] [Algebra A 𝕜] [IsScalarTower A K₀ 𝕜] where
  /-- The valuation ring of the extended place. -/
  C : Type
  [commRingC : CommRing C]
  [isDomainC : IsDomain C]
  [isDiscreteValuationRingC : IsDiscreteValuationRing C]
  /-- The constants of `K₀` are integral at the extended place. -/
  [algebraAC : Algebra A C]
  /-- The extended place is a place of `𝕜`. -/
  [algebraCK : Algebra C 𝕜]
  [tower : IsScalarTower A C 𝕜]
  [isFractionRing : IsFractionRing C 𝕜]
  /-- The place of `𝕜` lies above the place of `K₀`. -/
  under : Ideal.comap (algebraMap A C) (IsLocalRing.maximalIdeal C) = IsLocalRing.maximalIdeal A

end Work.MotR
