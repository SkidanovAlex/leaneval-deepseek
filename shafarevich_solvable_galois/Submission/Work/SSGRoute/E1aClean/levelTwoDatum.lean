import Mathlib
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
import Submission.Work.SSGRoute.E1aClean.decompField_hensel_groupIso
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.PT.freeCoverCompat
import Submission.Work.SSGRoute.PT.freeCoverCompatKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-2 datum of the base-change comparison (BC)

The last mathematical input of the finite local dictionary
`Work.SSGRoute.E1aClean.localDictionary_natural_family` is the level-change comparison

  `resH1_{D_A} (e1cMap^{(k,Ω,K)} z) = e1cMap^{(k^h,Ω,K^h)} z₂    (BC)`

between the `E1c` dictionary of the global datum `(k, Ω, K)` and the `E1c` dictionary of the
decomposition-field datum `(k^h, Ω, K^h)`.

This file provides the *wiring* of the level-2 datum, so that (BC) can be stated:

* `levelTwoGroupHom k Ω K A hA q hAq e : Gal(K^h/k^h) →* Gal(K/k)` — the group hom of the level
  change, `τ ↦ (e.symm τ : K ≃ₐ[k] K)`.  Its defining property
  (`levelTwoGroupHom_apply`) is that `e.symm τ` restricts to `levelTwoGroupHom … τ` on `K`;
* `levelTwoCoeff … X = Rep.res (levelTwoGroupHom …) X` — the level-2 coefficient module: the level-1
  representation `X` restricted to `D_q` and transported to `Gal(K^h/k^h)`.  Its underlying module is
  `X.V` (definitionally), which is what makes the two `homCoind` coefficients of `E1cGeneric` — and
  hence the two `H¹`-groups of (BC) — literally the same type;
* `levelTwoR1 … X = E1cR1 (levelTwoCoeff … X)` (the level-2 syzygy) and
  `levelOneR1Res … X = Rep.res (levelTwoGroupHom …) (E1cR1 X)` (the restriction of the level-1
  syzygy), which are related by the group-change syzygy comparison
  `Work.SSGRoute.PT.freeCoverCompat_kernelMap` instantiated at `levelTwoGroupHom`.

The comparison of the free covers along `levelTwoGroupHom` is
`Work.SSGRoute.PT.freeCoverCompat (levelTwoGroupHom …) X`, with
`freeCoverCompat_comp` giving the commuting square and `freeCoverCompat_kernelMap` the induced map on
the syzygies; these are the tools with which (BC) is proven from
`Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift`: both sides of (BC) are `H1π` of
one and the same cocycle, because the level-2 lift `ñ₂ := ñ₁ ∘ (freeCoverCompat …)` has
`iotaH₂ (c₂ g) = d0 ñ₂ g` with `c₂ g = c₁ g` for every `g ∈ D_A` (the level-1 and level-2
coefficient modules being the same underlying `X.V`).
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The group hom of the level change**: `Gal(K^h/k^h) →* Gal(K/k)`, `τ ↦ (e.symm τ : K ≃ₐ[k] K)`.

This is the map along which the level-1 coefficient module has to be restricted to obtain the
level-2 one, and along which the two canonical free covers are compared. -/
noncomputable def levelTwoGroupHom (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A)) :
    (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A) →* (K ≃ₐ[k] K) :=
  (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp e.symm.toMonoidHom

/-- The defining property of `levelTwoGroupHom`: `e.symm τ` restricts on `K` to
`levelTwoGroupHom … τ`. -/
theorem levelTwoGroupHom_apply (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (τ : henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A) :
    (levelTwoGroupHom k Ω K A hA q hAq e τ : K ≃ₐ[k] K)
      = (e.symm τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :=
  rfl

/-- **The level-2 coefficient module**: the level-1 representation `X` restricted to `D_q` and
transported along `e` to `Gal(K^h/k^h)`.

Its underlying module is `X.V` (definitionally), so the level-1 and level-2 `homCoind` coefficients
— and hence the two `H¹`-groups of the base-change comparison (BC) — are the same type. -/
noncomputable abbrev levelTwoCoeff (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Rep.{0} Coeff (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A) :=
  Rep.res (levelTwoGroupHom k Ω K A hA q hAq e) X

/-- The underlying module of the level-2 coefficient is the level-1 one. -/
theorem levelTwoCoeff_V (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    (levelTwoCoeff k Ω K A hA q hAq e X).V = X.V :=
  rfl

/-- **The level-2 syzygy** `R₂ = E1cR1 (levelTwoCoeff … X)`: the kernel of the canonical cover of
the level-2 coefficient. -/
noncomputable abbrev levelTwoR1 (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (X : Rep.{0} Coeff (K ≃ₐ[k] K)) : Rep.{0} Coeff
      (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A) :=
  Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (levelTwoCoeff k Ω K A hA q hAq e X)

/-- **The restriction of the level-1 syzygy** to `Gal(K^h/k^h)` along the level-change hom. -/
noncomputable abbrev levelOneR1Res (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (X : Rep.{0} Coeff (K ≃ₐ[k] K)) : Rep.{0} Coeff
      (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A) :=
  Work.SSGRoute.PT.freeCoverR1Res (levelTwoGroupHom k Ω K A hA q hAq e) X

/-- **The level-2 lift attached to a level-1 lift.**

For a level-1 lift `ñ : E1cN X = Hom_ℤ(ℤ[Γ]^{X.V}, Ωˣ)`, the level-2 lift is `ñ ∘ ι`, where
`ι = freeCoverCompat (levelTwoGroupHom …) X` compares the level-2 free module `ℤ[Gal(K^h/k^h)]^{X.V}`
with the level-1 one `ℤ[Γ]^{X.V}`.  This is the *same* function on the generators, which is why the
two attached cocycles agree on `D_A` (the heart of the base-change comparison (BC)). -/
noncomputable def levelTwoLift (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    [instA : IsAlgClosure ↥(decompField k Ω A) Ω]
    [instF : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [instG : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X) :
    Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A)) (Ω := Ω)
      (K := henselOverDecomp k Ω K A) (levelTwoCoeff k Ω K A hA q hAq e X) :=
  ((ñ : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) X).V →+ Additive Ωˣ).comp
    ((Work.SSGRoute.PT.freeCoverCompat (levelTwoGroupHom k Ω K A hA q hAq e) X).hom).toAddMonoidHom)

/-- **The conclusion of the base-change comparison (BC), in cocycle form**, packaged as a `Prop`.

The two level dictionaries `e1cMap X` and `e1cMap (levelTwoCoeff … X)` are `H1π` of the cocycles
`c₁` and `c₂` (`E1aClean.e1cMap_eq_H1π_of_cocycle_lift`), so this cocycle equality is (BC):
`resH1_{D_A}(e1cMap X (PhiE X y)) = e1cMap X₂ (PhiE X₂ y₂)`, with `y, y₂` matched automatically by
`levelTwoLift` (`ñ₂ = ñ ∘ freeCoverCompat`) together with the syzygy comparison
`Work.SSGRoute.PT.freeCoverCompat_kernelMap (levelTwoGroupHom …) X`.

Packaged here as a `Prop`-valued definition so that the statement can be delegated without
elaboration fragility in the conclusion. -/
def LevelTwoCocycleTarget (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (X : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ X.V]
    [instA : IsAlgClosure ↥(decompField k Ω A) Ω]
    [instF : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [instG : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (c₁ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X)
    (hñ : ∀ g, Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) X (c₁.1 g)
      = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X) ñ g)
    (c₂ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
        (levelTwoCoeff k Ω K A hA q hAq e X))))
    (hñ₂ : ∀ g, Work.SSGRoute.ExtChain.E1cGeneric.iotaH
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
        (levelTwoCoeff k Ω K A hA q hAq e X) (c₂.1 g)
      = Work.GroupCohomology.d0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A)) (Ω := Ω)
            (K := henselOverDecomp k Ω K A) (levelTwoCoeff k Ω K A hA q hAq e X))
          (levelTwoLift k Ω K A hA q hAq e X ñ) g) : Prop :=
  ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
    (((c₂.1 g : Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
          (levelTwoCoeff k Ω K A hA q hAq e X)) : X.V →+ Additive Ωˣ))
      = ((c₁.1 (((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g :
            ↥((decompField k Ω A).fixingSubgroup)) : Ω ≃ₐ[k] Ω) :
          Work.SSGRoute.homCoind k Ω K X) : X.V →+ Additive Ωˣ)

end

end Work.SSGRoute.E1aClean
