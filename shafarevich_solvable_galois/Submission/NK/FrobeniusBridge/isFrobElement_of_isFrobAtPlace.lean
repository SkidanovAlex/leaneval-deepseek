import Mathlib
import Submission.NK.FrobeniusBridge.Basic
import Submission.NK.Reconstruct.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements at a place are Frobenius elements

`NK.Reconstruct.IsFrobElement g` says that `g : Gal(K'/K)` is an arithmetic Frobenius element at
some prime of some finite normal level `L ⊆ K'`; `NK.FrobeniusBridge.IsFrobAtPlace A g` says that
`g` restricts to an arithmetic Frobenius element at the prime below the place `A` at *every* finite
normal level.

The infinite-level condition is therefore stronger, and only the trivial level `⊥ = K` is needed to
see it: at that level the prime of `𝓞 K` below the place `A` is a legitimate witness, and the
level-wise condition at `⊥` is exactly the Frobenius statement required by `IsFrobElement`.
(Note that the Frobenius condition at the base level is vacuous — the group `Gal(K/K)` is trivial —
but this is irrelevant: the level-wise data of `h` supplies the statement directly.)

The place `A` is a finite place of `K'`, so its restriction `A.comap (algebraMap K K')` is a proper
valuation subring of `K`, hence a prime of `𝓞 K`; this is `NK.Reconstruct.primeOfLevel` at the
level `⊥`, and it lies over `A` by construction, so it lies over the prime of `𝓞 ⊥ = 𝓞 K` below it.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.FrobeniusBridge

/-- **The level-wise condition produces a Frobenius element.**  If `g` restricts to an arithmetic
Frobenius element at the prime of a finite normal level `L` below the place `A`, then `g` is a
Frobenius element of `Gal(K'/K)` in the sense of `NK.Reconstruct.IsFrobElement` — namely at the
level `L` and the prime of `𝓞 L` below `A`, which lies over the prime of `𝓞 K` below `A`. -/
theorem isFrobElement_of_frobAtLevel {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    {L : IntermediateField K K'} [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    {A : FinitePlaceOf K K'} {g : Gal(K'/K)} (h : frobAtLevel A L g) :
    NK.Reconstruct.IsFrobElement g := by
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).under
      (NumberField.RingOfIntegers K),
    NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L),
    Ideal.over_under _, h⟩

theorem isFrobElement_of_isFrobAtPlace {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    {A : NK.FrobeniusBridge.FinitePlaceOf K K'} {g : Gal(K'/K)}
    (h : NK.FrobeniusBridge.IsFrobAtPlace A g) : NK.Reconstruct.IsFrobElement g := by
  -- `↥⊥ = K` is a finite normal level of `K'` over `K`, and it is a number field.
  haveI : NumberField ↥(⊥ : IntermediateField K K') :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  -- The level-wise component of `h` is the Frobenius statement at the level `⊥`.
  exact isFrobElement_of_frobAtLevel (h ⊥)

end NK.FrobeniusBridge
