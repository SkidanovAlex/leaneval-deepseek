import Mathlib
import Submission.Work.SSGRoute.phi1_lambda_defs
import Submission.Work.SSGRoute.phi1_level_limit
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.phiAt_level_infl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer compatibility of the functional `λ_L` of the E5s realisation

The realisation step `Work.SSGRoute.exists_realization_of_delta_lam` glues the level functionals

`λ_L (δ_L j) := φ¹(y)(j)`   (`Work.SSGRoute.lambdaOnRange`)

into a single functional on the direct limit `V = colim_L H²(Gal(L/k), 𝔽_p)`
(`Work.SSGRoute.LevelCohLimit`).  For that, the components must be *compatible* with the transition
maps of the levels: inflating `λ_L` along `L ≤ L'` gives `λ_{L'}` evaluated at the inflated class.

This file proves that compatibility — unconditionally (no `E0b`, no CFT input):

* `lambdaOnRange_inflCIn` — the level form
  `λ_{L'} (δ_{L'}(inflHIn h j)) = inflCIn h (λ_L (δ_L j))`, an immediate consequence of the
  computation rules `lambdaOnRange_apply` and of the pairing naturality
  `Work.SSGRoute.phiAt_level_infl` (`Submission/Work/SSGRoute/phiAt_level_infl.lean`);
* `lambdaOnRange_inflCIn_colim` — its `A`-colimit form, obtained by applying the structure map
  `ClassLevelLimit.of` and using `ClassLevelLimit.of_levelMap`.  This is the compatibility
  hypothesis of `DirectLimit.lift` for `λcolim : Wcolim →+ A`.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

variable {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- **Compatibility of the functional `λ` with inflation** (level form).  For levels `L ≤ L'` of
`Ω` and `j ∈ H¹(Gal(L/k), S.X₃)`, the value of `λ_{L'}` at `δ_{L'}(inflHIn h j)` is the inflation of
the value of `λ_L` at `δ_L j`.  Immediate from the computation rules and the naturality
`Work.SSGRoute.phiAt_level_infl` of the pairing. -/
theorem lambdaOnRange_inflCIn
    (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    {L L' : IntermediateField K Ω} [NumberField L] [NumberField L'] [FiniteDimensional k L]
    [FiniteDimensional k L'] [IsGalois k L] [IsGalois k L'] (h : L ≤ L')
    (hyL : ∀ h' : extH (Rep.res (galRes k K L) S.X₃) 1,
      deltaHom (k := k) (K := K) (L := L) S hS h' = 0 →
        phiAt (k := k) (K := K) (L := L) y h' = 0)
    (hyL' : ∀ h' : extH (Rep.res (galRes k K L') S.X₃) 1,
      deltaHom (k := k) (K := K) (L := L') S hS h' = 0 →
        phiAt (k := k) (K := K) (L := L') y h' = 0)
    (j : extH (Rep.res (galRes k K L) S.X₃) 1) :
    lambdaOnRange (k := k) (K := K) (L := L') S hS y hyL'
        ((deltaHom (k := k) (K := K) (L := L') S hS).rangeRestrict
          (inflHIn (k := k) (K := K) h j))
      = inflCIn (k := k) h
          (lambdaOnRange (k := k) (K := K) (L := L) S hS y hyL
            ((deltaHom (k := k) (K := K) (L := L) S hS).rangeRestrict j)) := by
  rw [lambdaOnRange_apply, lambdaOnRange_apply]
  exact (phiAt_level_infl L L' h S.X₃ y j).symm

/-- **Compatibility of `λ` with inflation** (class-colimit form): the `A`-valued components
`L ↦ ClassLevelLimit.of L ∘ λ_L` are compatible with the transition maps, hence define an additive
map `Wcolim →+ A`. -/
theorem lambdaOnRange_inflCIn_colim
    (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    {L L' : Lvl k K Ω} (h : L ≤ L')
    (hyL : ∀ h' : extH (Rep.res (galRes k K L.1) S.X₃) 1,
      deltaHom (k := k) (K := K) (L := L.1) S hS h' = 0 →
        phiAt (k := k) (K := K) (L := L.1) y h' = 0)
    (hyL' : ∀ h' : extH (Rep.res (galRes k K L'.1) S.X₃) 1,
      deltaHom (k := k) (K := K) (L := L'.1) S hS h' = 0 →
        phiAt (k := k) (K := K) (L := L'.1) y h' = 0)
    (j : extH (Rep.res (galRes k K L.1) S.X₃) 1) :
    ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L'
        (lambdaOnRange (k := k) (K := K) (L := L'.1) S hS y hyL'
          ((deltaHom (k := k) (K := K) (L := L'.1) S hS).rangeRestrict
            (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j)))
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (lambdaOnRange (k := k) (K := K) (L := L.1) S hS y hyL
            ((deltaHom (k := k) (K := K) (L := L.1) S hS).rangeRestrict j)) := by
  have hLL : L.1 ≤ L'.1 := h
  rw [← ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hLL
    (lambdaOnRange (k := k) (K := K) (L := L.1) S hS y hyL
      ((deltaHom (k := k) (K := K) (L := L.1) S hS).rangeRestrict j))]
  rw [classLevelMap_apply]
  exact congrArg (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L')
    (lambdaOnRange_inflCIn (k := k) (K := K) S hS y hLL hyL hyL' j)

end Work.SSGRoute
