import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.E1aClean.levelChange_lift_transport
import Submission.Work.SSGRoute.E1aClean.levelTwoDatum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# **(BC)** `levelTwoCocycleAgrees`: the cocycle agreement of the level change

This file closes the last mathematical input of the finite local dictionary
`Work.SSGRoute.E1aClean.localDictionary_natural_family`: the base-change comparison **(BC)**
`resH1_{D_A}(e1cMap^{(k,Ω,K)} z) = e1cMap^{(k^h,Ω,K^h)} z₂`, here in the *cocycle* form used by the
compare-the-two-`PhiE`-values argument.

The target is `Work.SSGRoute.E1aClean.LevelTwoCocycleTarget` (`E1aClean/levelTwoDatum.lean`): for a
level-`1` cocycle `c₁` with values in `homCoind k Ω K X` and a lift `ñ` of it (`hñ`), and a level-`2`
cocycle `c₂` with the *same* lift (`ñ₂ = levelTwoLift … ñ`, `hñ₂`), the two cocycles agree:

    c₂ g = c₁ (σ g),      σ : Gal(Ω/k^h) ↪ Gal(Ω/k)  the inclusion,

for every `g : Gal(Ω/k^h)`.

The proof is two steps, both already available:

* `Work.SSGRoute.E1aClean.levelChange_lift_transport` — the level-`1` lift relation transfers along
  the level change: `iotaH^{(k^h)}(c₁.1 (σ g)) = d0 (ñ ∘ ι) g`, where `ι = freeCoverCompat φ X` and
  `ñ ∘ ι = levelTwoLift … ñ` (`levelTwoLift_eq`);
* `Work.SSGRoute.ExtChain.E1cGeneric.iotaH_injective` — `iotaH` is precomposition with the canonical
  cover `coverMap : ℤ[Γ]^{X.V} → X.V`, hence injective; so `hñ₂ g` and the transported relation
  force `c₂.1 g = c₁.1 (σ g)`.

The only new *mathematical* input in the file is `levelTwoGroupHom_res`, the `Gal`-level
compatibility `φ ∘ res_{K^h/k^h} = res_{K/k} ∘ σ` of the two restriction maps at the canonical
`φ = levelTwoGroupHom`; it is a consequence of the defining clause `he` of the group isomorphism
`Gal(K^h/k^h) ≃* D_q` and of `AlgEquiv.restrictNormalHom_apply`.

## Relation to the sibling `E1aClean/levelChange_lift_transport.lean`

Nothing here uses `hψc` (the continuity of `AlgEquiv.restrictScalars k`); that hypothesis is only
needed for the *cocycle condition* of the transported cocycle (`levelChange_mem_Z1`), which the
compare-the-`PhiE`-values route does not need, since the level-`2` cocycle is supplied there by the
level-`2` cocycle formula.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The `Gal`-level compatibility of the two restriction maps at the canonical
`φ = levelTwoGroupHom`.**

For the canonical `φ = levelTwoGroupHom (e) = (Subtype.val ∘ e.symm)`, the restriction of the
level-change `φ` to `Gal(Ω/k^h)` is the same thing as the restriction of the *function* `g` to `K`
with scalars restricted to `k`:

    φ (g|K^h) = (g|Ω)|K  .

Indeed, both sides are `g` read on `K`: the defining clause `he` of `e` says that
`e τ` acts on `K ⊆ K^h` as `τ` does, so applying it to `τ = e.symm (g|K^h)` returns `g|K`. -/
theorem levelTwoGroupHom_res
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    [IsAlgClosure ↥(decompField k Ω A) Ω]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω) :
    levelTwoGroupHom k Ω K A hA q hAq e
        (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
      = SSGRoute.res k K (AlgEquiv.restrictScalars k g) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  show (((e.symm (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g) :
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : K ≃ₐ[k] K) x : Ω)
    = ((SSGRoute.res k K (AlgEquiv.restrictScalars k g)) x : Ω)
  rw [← he (e.symm (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)) x,
    MulEquiv.apply_symm_apply]
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

/-- **The element `σ(g)` of `LevelTwoCocycleTarget` is `AlgEquiv.restrictScalars k g`.**

The cocycle agreement is stated with the element of `Gal(Ω/k)` attached to `g : Gal(Ω/k^h)` through
`IntermediateField.fixingSubgroupEquiv`; since `fixingSubgroupEquiv`'s inverse is
`AlgEquiv.restrictScalars`, this is `g` itself with scalars restricted to `k`. -/
theorem levelTwoCocycle_restrictScalars
    (A : ValuationSubring Ω)
    [IsAlgClosure ↥(decompField k Ω A) Ω]
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω) :
    ((↑((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g) : Ω ≃ₐ[k] Ω))
      = AlgEquiv.restrictScalars k g := by
  apply AlgEquiv.ext
  intro x
  rfl

/-- **The level-`2` lift is `ñ` composed with the level-change comparison of the covers.**

`levelTwoLift` (`E1aClean/levelTwoDatum.lean`) is a `def`, so this coherence is a (definitional)
lemma. -/
theorem levelTwoLift_eq
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) X) :
    levelTwoLift k Ω K A hA q hAq e X ñ
      = ñ.comp (levelChangeIota A X (levelTwoGroupHom k Ω K A hA q hAq e)) :=
  rfl

/-- **(BC) in cocycle form**: the level-`2` cocycle `c₂` attached to the same lift `ñ` as the
level-`1` cocycle `c₁` agrees with `c₁` pointwise along the inclusion `Gal(Ω/k^h) ↪ Gal(Ω/k)`.

This is `LevelTwoCocycleTarget` (`E1aClean/levelTwoDatum.lean`) — the missing mathematical input of
the finite local dictionary `localDictionary_natural_family`.  Its proof needs no `hψc`: the level-`2`
cocycle is *given* (it comes from the level-`2` cocycle formula), and the two `iotaH`-values are
compared. -/
theorem levelTwoCocycle_agrees
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
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
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN
            (k := ↥(decompField k Ω A)) (Ω := Ω)
            (K := henselOverDecomp k Ω K A)
            (levelTwoCoeff k Ω K A hA q hAq e X))
          (levelTwoLift k Ω K A hA q hAq e X ñ) g) :
    LevelTwoCocycleTarget k Ω K A hA q hAq e he X c₁ ñ hñ c₂ hñ₂ := by
  intro g
  show (((c₂.1 g : Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
        (levelTwoCoeff k Ω K A hA q hAq e X)) : X.V →+ Additive Ωˣ))
    = ((c₁.1 (((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g :
          ↥((decompField k Ω A).fixingSubgroup)) : Ω ≃ₐ[k] Ω) :
        Work.SSGRoute.homCoind k Ω K X) : X.V →+ Additive Ωˣ)
  have htrans := levelChange_lift_transport A X (levelTwoGroupHom k Ω K A hA q hAq e)
    (levelTwoGroupHom_res k Ω K A hA q hAq e he) c₁ ñ hñ g
  rw [← levelTwoLift_eq k Ω K A hA q hAq e X ñ] at htrans
  have hinj := Work.SSGRoute.ExtChain.E1cGeneric.iotaH_injective
    (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A)
    (levelTwoCoeff k Ω K A hA q hAq e X)
  have hkey : c₂.1 g = c₁.1 (AlgEquiv.restrictScalars k g) :=
    hinj ((hñ₂ g).trans htrans.symm)
  have hσ : (↑((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g) : Ω ≃ₐ[k] Ω)
      = AlgEquiv.restrictScalars k g := levelTwoCocycle_restrictScalars k Ω A g
  rw [hkey, hσ]

end

end Work.SSGRoute.E1aClean
