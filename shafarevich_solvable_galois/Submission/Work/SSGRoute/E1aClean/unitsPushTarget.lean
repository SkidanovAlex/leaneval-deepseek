import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.decompField_hensel_groupIso
import Submission.Work.SSGRoute.E1aClean.henselEmb_equivariant
import Submission.Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The statement of the coefficient push `(K^h)ˣ → K_qˣ`, packaged as a `Prop`

The coefficient push `(PUSH)` of `Work.SSGRoute.E1aClean.localDictionary_natural_family` is

> postcomposition with `Units.map φ : (K^h)ˣ → K_qˣ` is a bijection on `Ext¹_{D_q}(X, ·)` for every
> finite `p`-torsion `X`,

where `φ : K^h →+* K_q` is the canonical embedding of the henselisation into the completion and the
`D_q`-representation structure on `(K^h)ˣ` is the one transported along
`e : D_q ≃* Gal(K^h/k^h)` (`decompField_hensel_groupIso`); that `Units.map φ` is a morphism of
`D_q`-representations at all is `Work.SSGRoute.E1aClean.henselEmb_equivariant`, and the unique
`p`-divisibility of the cokernel is
`Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed`.

The statement is packaged here as a `Prop`-valued definition so that it can be *delegated* free of
elaboration fragility in the conclusion (the `⧸`-quotient of units, the `Ext`-`postcomp` proof
argument, and the `Rep` coercions are all resolved here, once and for all).
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option linter.unusedVariables false

/-- **The target of the coefficient push `(PUSH)`.** -/
def HenUnitsPushTarget (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω))
    (φ : ↥(henselOverDecomp k Ω K A) →+*
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), le_henselField k Ω K A x.2⟩ =
        algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) x)
    (hfix : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
        (x : ↥(decompField k Ω A)),
        NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
            (φ ⟨(x : Ω), decompField_le_henselField k Ω K A x.2⟩)
          = φ ⟨(x : Ω), decompField_le_henselField k Ω K A x.2⟩)
    (hφinj : Function.Injective φ)
    (p : ℕ) [Fact p.Prime]
    (hQ : Function.Bijective (fun z : Additive (Units (NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite q))) ⧸
        (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup => p • z)) : Prop :=
  ∃ θ : Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q),
    (∀ u : Units ↥(henselOverDecomp k Ω K A),
        Rep.Hom.hom θ (Additive.ofMul u) = Additive.ofMul (Units.map φ.toMonoidHom u)) ∧
    (∀ (X : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (_ : Finite X.V), (∀ x : X.V, p • x = 0) →
      Function.Bijective ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp X (add_zero 1)))

end

end Work.SSGRoute.E1aClean
