import Mathlib
import Submission.NK.NUV2.RouteC.CommonsUnramified
import Submission.NK.NUV2.RouteC.unramified_invariant_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified-twist crux (Route C, Step 2): the valuation as a `Rep`-morphism

The engine `Commons.RepresentationTheory.GroupCohomology.map_eq_zero_of_mono_valuation` needs,
in the local tower, the valuation `ord₂ : (L₃)_{q₃}ˣ ⟶ ℤ` as a morphism of `Rep ℤ N` for every
subgroup `N` of the local Galois group, and the valuation-factor relation
`ι ≫ ord₂ = e • ord₁`.  This file provides the first of the two: Galois invariance of the
valuation on units is `Commons…unitsValLog_smul`, so the valuation is a `Rep`-morphism
(`valHom`), by construction.
-/

open IsDedekindDomain CategoryTheory

namespace NK.NUV2.RouteC

/-- **The valuation on the units of a local completion, as a `Rep ℤ N`-morphism to the trivial
representation `ℤ`**, for every subgroup `N` of the local Galois group.

Its underlying map is `unitsValLog`, and the intertwining property is the Galois invariance
`Commons.NumberTheory.NumberField.Completion.unitsValLog_smul`. -/
noncomputable def valHomG
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    valSeqMiddle K L Q q hq ⟶ valSeqTriv K L Q q hq := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  refine Rep.ofHom
    { toLinearMap := AddMonoidHom.toIntLinearMap
        { toFun := fun x => Multiplicative.toAdd
            (Commons.NumberTheory.NumberField.Completion.unitsValLog (q.adicCompletion L)
              (Additive.toMul x))
          map_zero' := by simp [Commons.NumberTheory.NumberField.Completion.unitsValLog]
          map_add' := fun x y => by
            show (Commons.NumberTheory.NumberField.Completion.unitsValLog
                (q.adicCompletion L) (Additive.toMul (x + y))).toAdd
              = (Commons.NumberTheory.NumberField.Completion.unitsValLog
                  (q.adicCompletion L) (Additive.toMul x)).toAdd
                + (Commons.NumberTheory.NumberField.Completion.unitsValLog
                    (q.adicCompletion L) (Additive.toMul y)).toAdd
            rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl,
              map_mul]
            rfl }
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        exact congrArg Multiplicative.toAdd
          (Commons.NumberTheory.NumberField.Completion.unitsValLog_smul Q q hq σ
            (Additive.toMul x)) }

/-- The local Galois group `Gal(E/F)` of a completion, as a **`letI`-free** type: the canonical
`Algebra` instance is built inside.  Purpose: statements about it (and about subgroups of it, and
about `Rep`s over it) can be written without a `letI`-binder, which is needed for the delegation
machinery. -/
noncomputable abbrev localGaloisGroup (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) : Type := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L

/-- **The units representation `Eˣ` of `Gal(E/F)` for a completion, as a `letI`-free wrapper.**
The canonical `Algebra` instance is built inside (the same expression as in `localGaloisGroup`, so
that the two wrappers see the same structure). -/
noncomputable abbrev localUnitsRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Rep ℤ (localGaloisGroup K L Q q hq) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)

/-- `localUnitsRep` is the middle object of the valuation sequence (definitionally). -/
theorem localUnitsRep_eq_valSeqMiddle (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    localUnitsRep K L Q q hq = valSeqMiddle K L Q q hq := rfl

/-- **The subgroup-restricted valuation**, `letI`-free: for a subgroup `N ≤ Gal(E/F)`, the
valuation on `Eˣ` as a morphism of `Rep ℤ N` onto the trivial representation `ℤ`.  This is the
`ord₂` of the twist engine `Commons…map_eq_zero_of_mono_valuation`. -/
noncomputable def localValHom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (N : Subgroup (localGaloisGroup K L Q q hq)) :
    Rep.res N.subtype (localUnitsRep K L Q q hq) ⟶ Rep.trivial ℤ N ℤ :=
  Rep.resMap N.subtype (valHomG Q q hq)

end NK.NUV2.RouteC
