import Mathlib
import Submission.Work.CFTLib.Interfaces
import Submission.Work.WingbergEndgame.Defs
import Submission.Work.WingbergEndgame.isPGroup_of_finite_galoisGroup
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv

/-!
# `Work.CFTLib.shafBound_eval_gsF`

The `S = T = ∅` instance, at the totally real quadratic base field
`F = gsF = ℚ(√(5·13·17·29·37·41·53))`, of **Shafarevich's bound for finite unramified
`p`-extensions** (`CFTLib.ShafBound`), evaluated on the finite levels of the wide maximal
pro-`2` extension of `F`.

Let `E` be the wide maximal pro-`2` extension of `gsF` (`Work.WingbergEndgame.
UnramifiedProTwoExtension`: unramified at *every* place, finite and infinite) and suppose its
Galois group `Γ = E.K ≃ₐ[gsF] E.K` is **finite**.  Then

* `E.K/gsF` is a finite dimensional (hence a number field) Galois extension
  (`IsGalois.finiteDimensional_of_finite`, `NumberField.of_module_finite`);
* `E.K/gsF` is a `2`-extension: `Γ` is a `2`-group
  (`Work.WingbergEndgame.isPGroup_of_finite_galoisGroup`);
* `E.K/gsF` is unramified at the finite primes and at the infinite places: the two clauses
  `unramified` / `unramifiedInf` of `E` applied to the top intermediate field, transported to
  `E.K` along `IntermediateField.topEquiv`
  (`Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv`,
  `Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv`);
* `E.K/gsF` is *maximal*: `CFTLib.IsMaximalUnramified gsF E.K 2 ∅`, which is exactly the
  universal property `E.universal`.

So `CFTLib.MaximalClassCond` gives the class condition at `T = ∅`, and `CFTLib.ShafBound`
gives

```
dim H²(Γ, 𝔽₂) ≤ dim H¹(Γ, 𝔽₂) + (r₁ + r₂ − 1) + δ₂(gsF) + 0 .
```

For the real quadratic field `gsF` we have `r₁ = 2`, `r₂ = 0` and `δ₂ = 1` (`−1` is a primitive
square root of unity), so the correction term is `2`, which is the statement below.

This is the numerical input `d₂(Γ) ≤ d₁(Γ) + 2` of the classical Golod–Shafarevich argument at
`gsF` (cf. `HANDOFF.md`): combined with `d₁(Γ) = dim H¹(Γ,𝔽₂) ≥ 6` it contradicts
`Work.ProPGS.proPGolodShafarevich`, forcing `Γ` to be infinite.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.CFTLib

theorem shafBound_eval_gsF (h1 : CFTLib.ShafBound) (h2 : CFTLib.MaximalClassCond)
    (E : Work.WingbergEndgame.UnramifiedProTwoExtension ↥Work.QuadraticFields.gsF)
    (hfin : Finite (Work.WingbergEndgame.galoisGroup E)) :
    Module.finrank (ZMod 2)
        (groupCohomology (Rep.trivial (ZMod 2) (Work.WingbergEndgame.galoisGroup E) (ZMod 2)) 2) ≤
      Module.finrank (ZMod 2)
        (groupCohomology (Rep.trivial (ZMod 2) (Work.WingbergEndgame.galoisGroup E) (ZMod 2)) 1) + 2 := by
  classical
  -- `E.K/gsF` is finite dimensional, because its Galois group is finite
  haveI : Finite (E.K ≃ₐ[↥Work.QuadraticFields.gsF] E.K) := hfin
  haveI hfd : FiniteDimensional ↥Work.QuadraticFields.gsF E.K :=
    IsGalois.finiteDimensional_of_finite _ _
  -- ... hence `E.K` is a number field
  haveI hnum : NumberField E.K := NumberField.of_module_finite ↥Work.QuadraticFields.gsF E.K
  -- the top intermediate field, with the instances `E.unramified` asks for
  haveI hfdTop : FiniteDimensional ↥Work.QuadraticFields.gsF
      (↥(⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K)) := inferInstance
  haveI hgalTop : IsGalois ↥Work.QuadraticFields.gsF
      (↥(⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K)) :=
    IsGalois.of_algEquiv
      (IntermediateField.topEquiv (F := ↥Work.QuadraticFields.gsF) (E := E.K)).symm
  haveI hnumTop : NumberField (↥(⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K)) :=
    NumberField.of_module_finite ↥Work.QuadraticFields.gsF _
  -- unramifiedness of `E.K` at the finite primes and at the infinite places
  have hdiffTop : differentIdeal (𝓞 ↥Work.QuadraticFields.gsF)
      (𝓞 (↥(⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K))) = ⊤ :=
    E.unramified (⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K) hfdTop hgalTop
  have hinfTop : IsUnramifiedAtInfinitePlaces ↥Work.QuadraticFields.gsF
      (↥(⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K)) :=
    E.unramifiedInf (⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K) hfdTop hgalTop
  have hdiff : differentIdeal (𝓞 ↥Work.QuadraticFields.gsF) (𝓞 E.K) = ⊤ :=
    Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv
      (F := ↥Work.QuadraticFields.gsF) (E := ↥(⊤ : IntermediateField ↥Work.QuadraticFields.gsF E.K))
      (E' := E.K) (IntermediateField.topEquiv (F := ↥Work.QuadraticFields.gsF) (E := E.K)) hdiffTop
  have hinf : IsUnramifiedAtInfinitePlaces ↥Work.QuadraticFields.gsF E.K :=
    Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv
      (IntermediateField.topEquiv (F := ↥Work.QuadraticFields.gsF) (E := E.K)) hinfTop
  have hunr : CFTLib.IsUnramified ↥Work.QuadraticFields.gsF E.K := ⟨hdiff, hinf⟩
  -- the Galois group of `E.K/gsF` is a finite `2`-group
  have hisP : IsPGroup 2 (E.K ≃ₐ[↥Work.QuadraticFields.gsF] E.K) :=
    Work.WingbergEndgame.isPGroup_of_finite_galoisGroup E hfin
  -- `T = ∅`: the splitting condition is vacuous
  have hsplit : CFTLib.SplitsAt ↥Work.QuadraticFields.gsF E.K
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ↥Work.QuadraticFields.gsF))) := by
    intro v hv
    exact absurd hv (Finset.notMem_empty v)
  -- maximality is the universal property of `E`
  have hmax : CFTLib.IsMaximalUnramified ↥Work.QuadraticFields.gsF E.K 2
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ↥Work.QuadraticFields.gsF))) := by
    intro L _ _ _ _ _ hpL hunrL _
    obtain ⟨φ, _⟩ := E.universal L hpL hunrL.1 hunrL.2
    exact ⟨φ⟩
  have hclass : CFTLib.ClassCond ↥Work.QuadraticFields.gsF E.K 2
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ↥Work.QuadraticFields.gsF))) :=
    h2 ↥Work.QuadraticFields.gsF E.K 2 _ hisP hunr hsplit hmax
  -- Shafarevich's bound at `gsF`, `p = 2`, `T = ∅`
  have hb := h1 ↥Work.QuadraticFields.gsF E.K 2
      (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ↥Work.QuadraticFields.gsF)))
      hisP hunr hsplit hclass
  -- the numerical correction `(r₁ + r₂ − 1) + δ₂(gsF) + #∅` equals `2`
  haveI : NumberField.IsTotallyReal ↥Work.QuadraticFields.gsF := Work.QuadraticFields.gsF_isTotallyReal
  have hreal : NumberField.InfinitePlace.nrRealPlaces ↥Work.QuadraticFields.gsF = 2 :=
    (NumberField.IsTotallyReal.finrank ↥Work.QuadraticFields.gsF).symm.trans
      Work.QuadraticFields.gsF_finrank
  have hcomp : NumberField.InfinitePlace.nrComplexPlaces ↥Work.QuadraticFields.gsF = 0 :=
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero ↥Work.QuadraticFields.gsF
  have hroot : ∃ ζ : ↥Work.QuadraticFields.gsF, IsPrimitiveRoot ζ 2 :=
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
  have hdelta : CFTLib.delta ↥Work.QuadraticFields.gsF 2 = 1 := by
    simp only [CFTLib.delta, hroot, ↓reduceIte]
  rw [hreal, hcomp, hdelta, Finset.card_empty] at hb
  exact hb

end Work.CFTLib
