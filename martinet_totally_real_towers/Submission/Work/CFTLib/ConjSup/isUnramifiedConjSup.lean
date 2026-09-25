import Mathlib
import Submission.Work.CFTLib.Basic
import Submission.Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup
import Submission.Work.Tower.TowerCut.Transfer
import Submission.Work.CFTLib.InfinitePlace.isUnramifiedAtInfinitePlaces_iSup
import Submission.Work.CFTLib.Transport.isUnramified_algEquiv

/-!
# `CFTLib.IsUnramified F (conjSup p K' L')`

`Work.CFTLib.conjSup p K' L'` is the compositum, inside `AlgebraicClosure F`, of the conjugates
`σ(L')` of `L'` under the extensions to `AlgebraicClosure F` of the elements `σ` of `Gal(K'/F)`
(see `Submission/Work/CFTLib/Basic.lean` for the definition).  The target of this file is

`CFTLib.IsUnramified F ↥(conjSup p K' L')`,

i.e. `conjSup p K' L' / F` has trivial relative different and every real place of `F` stays real.
This is the "Galois closure of an unramified cyclic degree-`p` extension is unramified" step of
`Work.CFTLib.maximalClassCond`, where `L'/K'` is a degree-`p` unramified extension with
prescribed splitting, and `M = conjSup p K' L'` is its normal closure over `F`.

The proof has four steps, none of which uses the primality of `p` (nor the parameter `p` at
all: `conjSup` does not depend on `p`).  They are carried out in this file in a self-contained
way — note that the modules `Work.CFTLib.ConjSup.isUnramified` and
`Work.CFTLib.ConjSup.isUnramifiedAtInfinitePlaces` prove closely related statements, but they
cannot be imported together with `Work.CFTLib.ConjSup.isPGroup` (a duplicate declaration of
`conjSup_eq_iSup`), and `maximalClassCond` needs all three:

* `isUnramifiedConjSup_tower`: unramifiedness at the finite primes is transitive in the tower
  `F ⊆ K' ⊆ L'` (`Ideal.ramificationIdx_tower`);
* `isUnramifiedConjSup_conjField`: a conjugate of an everywhere unramified extension is
  everywhere unramified, by transporting along the `F`-algebra isomorphism `L' ≃ₐ[F] σ(L')`;
* `isUnramifiedConjSup_finite`: a finite supremum of extensions unramified at all finite primes
  is unramified at all finite primes
  (`Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup`); together with the previous two
  this gives `differentIdeal = ⊤`;
* `isUnramifiedConjSup_infinite`: unramifiedness at the infinite places ascends to a finite
  compositum (`Work.CFTLib.InfinitePlace.isUnramifiedAtInfinitePlaces_iSup`).

`Gal(K'/F)` is finite, because `K'/F` is finite dimensional, so the supremum over it is finite
and both `iSup` results apply.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.CFTLib.ConjSup

/-- **Unramifiedness at the finite primes is transitive in a tower of number fields.**

If `F ⊆ K' ⊆ L'` with `K'/F` and `L'/K'` unramified at every finite prime, then `L'/F` is
unramified at every finite prime.  This is the version of
`Work.Tower.IsUnramifiedExtensionForallPrimes.of_tower` in which the top field is an intermediate
field of the ambient field over the middle field rather than over the base field. -/
theorem isUnramifiedConjSup_tower (F : Type) [Field F] [NumberField F]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L']
    (hK : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K')
    (hL : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K' ↥L') :
    Work.Tower.IsUnramifiedExtensionForallPrimes F ↥L' := by
  intro 𝔓 h𝔓
  haveI := h𝔓
  have h1 : 𝔓.ramificationIdx (𝓞 F) =
      (𝔓.under (𝓞 ↥K')).ramificationIdx (𝓞 F) * 𝔓.ramificationIdx (𝓞 ↥K') :=
    Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 ↥K') (T := 𝓞 ↥L')
      (q := 𝔓.under (𝓞 ↥K')) (r := 𝔓)
  rw [h1, hK _ (inferInstance : (𝔓.under (𝓞 ↥K')).IsPrime), hL 𝔓 h𝔓, one_mul]

/-- **A conjugate of an everywhere unramified extension is everywhere unramified.**

If `L'/F` (with `F ⊆ K' ⊆ L'`) is unramified at every finite prime, then so is its image
`σ(L')` under the lift of `σ ∈ Gal(K'/F)` to an `F`-automorphism of `AlgebraicClosure F`:
the two are isomorphic as `F`-algebras and unramifiedness is invariant under such an
isomorphism. -/
theorem isUnramifiedConjSup_conjField (F : Type) [Field F] [NumberField F]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L']
    (h : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥L')
    (σ : ↥K' ≃ₐ[F] ↥K') :
    Work.Tower.IsUnramifiedExtensionForallPrimes F
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) := by
  -- `L'` is finite dimensional over `F`, being a finite extension of the finite extension `K'`
  -- of `F`; and it inherits the number field structure from the hypothesis.
  have hFdlL : FiniteDimensional F ↥L' := Module.Finite.trans ↥K' ↥L'
  haveI hFdl : FiniteDimensional F ↥(L'.restrictScalars F) := hFdlL
  haveI hNF : NumberField ↥(L'.restrictScalars F) := inferInstanceAs (NumberField ↥L')
  -- The conjugate is an isomorphic copy of `L'`, hence again a number field finite over `F`.
  have e : ↥(L'.restrictScalars F) ≃ₐ[F]
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) :=
    IntermediateField.equivMap (L'.restrictScalars F)
      (σ.liftNormal (AlgebraicClosure F)).toAlgHom
  haveI hFdl2 : FiniteDimensional F
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI hNF2 : NumberField
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) :=
    NumberField.of_module_finite F _
  have h' : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(L'.restrictScalars F) := h
  exact Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_of_algEquiv e h'

/-- **The compositum of the conjugates of an unramified extension is unramified at the finite
primes.**

If `K'/F` is a finite Galois extension unramified at every finite prime, and `L'/K'` is
unramified at every finite prime, then the compositum `conjSup p K' L'` of the conjugates of
`L'` over `K'` is unramified at every finite prime over `F`.

`Gal(K'/F)` is finite, so `conjSup p K' L'` is a finite compositum of extensions which are
unramified over `F`; a finite compositum of unramified extensions is unramified. -/
theorem isUnramifiedConjSup_finite (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L'] [NumberField ↥(conjSup p K' L')]
    (hKunr : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K')
    (hLgal : IsGalois ↥K' L')
    (hLunr : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K' ↥L') :
    Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(conjSup p K' L') := by
  -- The base of the compositum: `L'/F` is unramified at every finite prime.
  have hL'F : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥L' :=
    isUnramifiedConjSup_tower F K' L' hKunr hLunr
  -- Every conjugate of `L'` is unramified over `F`.
  have hunr : ∀ σ : ↥K' ≃ₐ[F] ↥K', Work.Tower.IsUnramifiedExtensionForallPrimes F
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) :=
    fun σ => isUnramifiedConjSup_conjField F K' L' hL'F σ
  -- The conjugates are finite dimensional over `F`, so the finite supremum can be formed.
  have hFdlL : FiniteDimensional F ↥L' := Module.Finite.trans ↥K' ↥L'
  haveI hFdl : FiniteDimensional F ↥(L'.restrictScalars F) := hFdlL
  haveI hfd : ∀ σ : ↥K' ≃ₐ[F] ↥K', FiniteDimensional F
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) :=
    fun σ => LinearEquiv.finiteDimensional (IntermediateField.equivMap (L'.restrictScalars F)
      (σ.liftNormal (AlgebraicClosure F)).toAlgHom).toLinearEquiv
  haveI : Nonempty (↥K' ≃ₐ[F] ↥K') := ⟨AlgEquiv.refl⟩
  exact Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_iSup
    (fun σ : ↥K' ≃ₐ[F] ↥K' =>
      (L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) hunr

/-- **Unramifiedness at the infinite places passes to the compositum of the conjugates.**

If `K'/F` and `L'/K'` are unramified at the infinite places, then so is the compositum
`conjSup p K' L'` of the conjugates.

`K'/F` being unramified at infinity, the same holds for `L'/F` by transitivity; each conjugate
`σ(L')` is an `F`-algebra-isomorphic copy of `L'` and so is unramified at infinity as well; a
finite supremum of extensions unramified at infinity is again unramified at infinity. -/
theorem isUnramifiedConjSup_infinite (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K']
    [IsGalois F K'] (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L'] [NumberField ↥(conjSup p K' L')]
    (hKinf : IsUnramifiedAtInfinitePlaces F ↥K')
    (hLgal : IsGalois ↥K' L')
    (hLinf : IsUnramifiedAtInfinitePlaces ↥K' ↥L') :
    IsUnramifiedAtInfinitePlaces F ↥(conjSup p K' L') := by
  haveI : IsUnramifiedAtInfinitePlaces F ↥K' := hKinf
  haveI : IsUnramifiedAtInfinitePlaces ↥K' ↥L' := hLinf
  -- The extension `L'/F` is unramified at infinity, by transitivity.
  have hL : IsUnramifiedAtInfinitePlaces F ↥L' :=
    IsUnramifiedAtInfinitePlaces.trans F ↥K' ↥L'
  have hL0 : IsUnramifiedAtInfinitePlaces F ↥(L'.restrictScalars F) := hL
  -- `L'` is finite dimensional over `F`.
  have hFdlL : FiniteDimensional F ↥L' := Module.Finite.trans ↥K' ↥L'
  haveI hFdl : FiniteDimensional F ↥(L'.restrictScalars F) := hFdlL
  -- Each conjugate is an isomorphic copy of `L'` over `F`, hence finite dimensional over `F`.
  haveI hfdE : ∀ σ : ↥K' ≃ₐ[F] ↥K', FiniteDimensional F
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) := by
    intro σ
    exact LinearEquiv.finiteDimensional (IntermediateField.equivMap (L'.restrictScalars F)
      (σ.liftNormal (AlgebraicClosure F)).toAlgHom).toLinearEquiv
  -- Every conjugate is unramified at infinity over `F`.
  have hE : ∀ σ : ↥K' ≃ₐ[F] ↥K', IsUnramifiedAtInfinitePlaces F
      ↥((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) := by
    intro σ
    exact Work.CFTLib.Transport.unramifiedAtInfinitePlaces_algEquiv
      (IntermediateField.equivMap (L'.restrictScalars F)
        (σ.liftNormal (AlgebraicClosure F)).toAlgHom) hL0
  haveI : Nonempty (↥K' ≃ₐ[F] ↥K') := ⟨AlgEquiv.refl⟩
  haveI : NumberField ↥(⨆ σ : ↥K' ≃ₐ[F] ↥K',
      (L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) :=
    ‹NumberField ↥(conjSup p K' L')›
  exact Work.CFTLib.InfinitePlace.isUnramifiedAtInfinitePlaces_iSup F (AlgebraicClosure F)
    (fun σ : ↥K' ≃ₐ[F] ↥K' =>
      (L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) hE

theorem isUnramifiedConjSup (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K'] (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L'] [NumberField ↥K'] [NumberField ↥L'] [NumberField ↥(conjSup p K' L')] (hKunr : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K') (hKinf : IsUnramifiedAtInfinitePlaces F ↥K') (hLgal : IsGalois ↥K' L') (hLunr : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K' ↥L') (hLinf : IsUnramifiedAtInfinitePlaces ↥K' ↥L') : CFTLib.IsUnramified F ↥(conjSup p K' L') := by
  refine ⟨?_, ?_⟩
  · exact Work.Tower.isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top.mp
      (isUnramifiedConjSup_finite F p K' L' hKunr hLgal hLunr)
  · exact isUnramifiedConjSup_infinite F p K' L' hKinf hLgal hLinf

end Work.CFTLib.ConjSup
