import Mathlib
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.E1aClean.ArchSeam
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The seam-induced coefficient change of the archimedean comparison square

This module supplies the *components* of the place-change `SES`-morphism of
`Submission/Work/SSGRoute/E1aClean/NOTE_infLocalCriterion_frontier.md` §0 (gap (iii)): the
coefficient change "push values along the seam `φ`"

    `seamCoeff φ : (V →+ Additive Ωˣ) →+ (V →+ Additive ℂˣ)`,

the two formal rules it obeys (its value formula, and its commutation with precomposition — the
`ι`/`π`-squares of the comparison square), and its **equivariance** under the `⟨σ⟩`-action, which is
the `hΘ` slot of the generic module map `E1cGeneric.localModuleMap`
(`E1cGeneric/localModuleMap.lean`).  The equivariance is exactly `linkedSeamUnitsMap`
(`E1aClean/ArchSeam.lean`) at the value of the map at an index, and is the reason the seam had to be
stated *with* the link.

Both `Ωˣ` and `ℂˣ` are divisible (both fields are algebraically closed), so the construction
`e1aSESgen` applies at the local data `(ℝ, ℂ, ⊤)` as well; the comparison between the two
resolutions is a morphism of short exact sequences whose three components are `seamCoeff` composed
with the comparison of the canonical covers (`PT.freeCoverCompat`,
`PT.e1a_localComparison_bricks.extClass_freeCoverSES_res_comparison`).
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.E1aClean

open SSGRoute.PTExt

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The seam coefficient change**: postcomposition with `φ` on units, `f ↦ φ ∘ f`. -/
def seamCoeff (φ : Ω →+* ℂ) {V : Type*} [AddCommMonoid V] :
    (V →+ Additive Ωˣ) →+ (V →+ Additive ℂˣ) where
  toFun f := (Units.map φ.toMonoidHom).toAdditive.comp f
  map_zero' := AddMonoidHom.comp_zero _
  map_add' f g := AddMonoidHom.comp_add _ _ _

/-- Value formula of `seamCoeff`. -/
@[simp] theorem seamCoeff_apply (φ : Ω →+* ℂ) {V : Type*} [AddCommMonoid V]
    (f : V →+ Additive Ωˣ) (x : V) :
    seamCoeff φ f x = Additive.ofMul (Units.map φ.toMonoidHom (Additive.toMul (f x))) := rfl

/-- **`seamCoeff` commutes with precomposition** — the `ι`/`π`-squares of the comparison square: the
coefficient change does not interact with the precomposition maps of the dualised canonical
resolution. -/
theorem seamCoeff_precomp (φ : Ω →+* ℂ) {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (u : V →+ W) (g : W →+ Additive Ωˣ) :
    seamCoeff φ (g.comp u) = (seamCoeff φ g).comp u := rfl

/-- **The value form of the link at an index**, which is the content of the equivariance of
`seamCoeff` under the `⟨σ⟩`-action (the `hΘ` slot of `E1cGeneric.localModuleMap`): the `⟨σ⟩`-action
on `Ωˣ`-valued maps is the conjugation action of the Galois action of `σ` through `res k K`, and the
`⟨σ⟩`-action on `ℂˣ`-valued maps is the *same* conjugation action with the coefficient action the
local one `localActionC τ`; the two agree on values by the linked seam `linkedSeamUnitsMap`.  This is
recorded here (at a single index) so that the `SES`-morphism of the comparison square can be stated
with both actions pinned to the same convention. -/
theorem seamCoeff_conjValue (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x)) (U : Ωˣ) :
    Additive.ofMul (Units.map φ.toMonoidHom
        (Work.SSGRoute.algEquivUnitsMapΩ k Ω σ U)) =
      Additive.ofMul (Units.map (localActionC K w hw τ).toMonoidHom
        (Units.map φ.toMonoidHom U)) :=
  congrArg Additive.ofMul (linkedSeamUnitsMap K w hw τ σ hres φ hφK hlink U)


/-! ## The local data of the archimedean comparison, named

The local dictionary lives at `(k, Ω, K) = (ℝ, ℂ, ⊤)`.  Its carrier at the level is
`localLevel = ⊤ : IntermediateField ℝ ℂ`, whose underlying type is `↥⊤` (not `ℂ`), so its group is
`localGroup = ↥⊤ ≃ₐ[ℝ] ↥⊤`.  These two `abbrev`s and the transported first variable `localX` (and
the local free module `localF`) are what lets the comparison statement be written without fighting
the `homCoind`-is-an-`abbrev` unfolding. -/

/-- The local level of the archimedean comparison. -/
abbrev localLevel : IntermediateField ℝ ℂ := ⊤

/-- The local group of the archimedean comparison. -/
abbrev localGroup : Type := (localLevel ≃ₐ[ℝ] localLevel)

/-- **The first variable of the local dictionary**: the coefficient `X` restricted to `⟨σ⟩` and
transported along `Φ` to the local group. -/
abbrev localX {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : Ω ≃ₐ[k] Ω) (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K))
    (Φ : ↥(Subgroup.zpowers σ) ≃* localGroup) : Rep.{0} SSGRoute.PTExt.Coeff localGroup :=
  Rep.res Φ.symm.toMonoidHom (Rep.res (Subgroup.zpowers σ).subtype (Rep.res (SSGRoute.res k K) X))

/-- **The second variable of the local dictionary** (the free module at the local group). -/
abbrev localF {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) :
    Rep.{0} SSGRoute.PTExt.Coeff localGroup :=
  Rep.free SSGRoute.PTExt.Coeff localGroup X.V

end Work.SSGRoute.E1aClean