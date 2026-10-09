import Mathlib
import Submission.Work.SSGRoute.E1aClean.Transport
import Submission.Work.SSGRoute.E1aClean.extPostIsoHomNat
import Submission.Work.SSGRoute.E1aClean.localExtTransportNat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local `Ext`-transport as an additive equivalence

`E1aClean/Transport.lean`'s `localExtTransport` is an *additive monoid homomorphism*
`Ext¹_{D_q}(res X, K_qˣ) →+ Ext¹_{Gal(K′/k_v)}(res R, (K′)ˣ)`; `localExtTransport_injective` shows it
is injective.  The assembly of the natural local dictionary needs it as an `AddEquiv` (factor `A₁`),
so this file supplies the surjectivity — all three named steps are surjective:
`extPostIsoHom` (postcomposition with an isomorphism), and twice `Functor.mapExtAddHom` of the exact
functor `Rep.resFunctor` (bijective by `Functor.mapExt_bijective_of_preservesProjectiveObjects`,
which `localExtTransport_injective` already uses) — together with the `AddEquiv` itself and the
transport of the proved naturality square.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 40000000

/-- **Surjectivity of `extPostIsoHom`**: postcomposition with an isomorphism of coefficient
representations is onto. -/
theorem extPostIsoHom_surjective {G : Type} [Group G] {N N' : Rep.{0} SSGRoute.PTExt.Coeff G}
    (e : N ≅ N') (M : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) :
    Function.Surjective (extPostIsoHom e M n) := by
  intro y
  refine ⟨extPostIsoHom e.symm M n y, ?_⟩
  rw [extPostIsoHom_apply, extPostIsoHom_apply,
    CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, e.symm_hom, e.inv_hom_id]
  exact CategoryTheory.Abelian.Ext.comp_mk₀_id y

/-- **Surjectivity of the local `Ext`-transport.** -/
theorem localExtTransport_surjective {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [Fintype (K ≃ₐ[k] K)] {A : ValuationSubring Ω}
    {hA : SSGRoute.IsFinPlace k A}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    [Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))]
    [Fintype (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ) :
    Function.Surjective (localExtTransport K' eG X hiso n) := by
  haveI hE : (Rep.resFunctor (k := Coeff) eG.symm.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence eG
  have hb : Function.Bijective (groupStep K' eG X n) :=
    Functor.mapExt_bijective_of_preservesProjectiveObjects _ _ _ _
  intro y
  obtain ⟨y₁, hy₁⟩ := extPostIsoHom_surjective (resResIsoIso K' eG (localCoeff K')) _ n y
  obtain ⟨y₂, hy₂⟩ := hb.surjective y₁
  obtain ⟨y₃, hy₃⟩ := extPostIsoHom_surjective hiso _ n y₂
  exact ⟨y₃, by
    rw [localExtTransport, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    rw [show coeffStep K' eG X hiso n y₃ = y₂ from hy₃,
      show groupStep K' eG X n y₂ = y₁ from hy₂,
      show finalStep K' eG X n y₁ = y from hy₁]⟩

/-- **The local `Ext`-transport as an additive equivalence** (factor `A₁` of the natural local
dictionary). -/
noncomputable def localExtTransportEquiv {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [Fintype (K ≃ₐ[k] K)] {A : ValuationSubring Ω}
    {hA : SSGRoute.IsFinPlace k A}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    [Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))]
    [Fintype (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ) :
    Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) n ≃+
      Abelian.Ext (localFirst K' eG X) (localCoeff K') n :=
  AddEquiv.ofBijective (localExtTransport K' eG X hiso n)
    ⟨localExtTransport_injective K' eG X hiso n, localExtTransport_surjective K' eG X hiso n⟩

/-- The computation rule of `localExtTransportEquiv`. -/
@[simp] theorem localExtTransportEquiv_apply {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [Fintype (K ≃ₐ[k] K)] {A : ValuationSubring Ω}
    {hA : SSGRoute.IsFinPlace k A}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    [Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))]
    [Fintype (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ)
    (y : Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) n) :
    localExtTransportEquiv K' eG X hiso n y = localExtTransport K' eG X hiso n y := rfl

/-- **Naturality of the transport equivalence** in the first variable (transport of
`localExtTransport_mk_natural`). -/
theorem localExtTransportEquiv_mk_natural {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [Fintype (K ≃ₐ[k] K)] {A : ValuationSubring Ω}
    {hA : SSGRoute.IsFinPlace k A}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    [Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))]
    [Fintype (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')]
    (X₁ X₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (g : X₂ ⟶ X₁)
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ)
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X₁)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) n) :
    localExtTransportEquiv K' eG X₂ hiso n
        ((CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)).comp
          y (zero_add n))
      = (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap eG.symm.toMonoidHom
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g))).comp
          (localExtTransportEquiv K' eG X₁ hiso n y) (zero_add n) := by
  change localExtTransport K' eG X₂ hiso n
      ((CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)).comp
        y (zero_add n))
    = (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap eG.symm.toMonoidHom
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g))).comp
        (localExtTransport K' eG X₁ hiso n y) (zero_add n)
  exact localExtTransport_mk_natural K' eG X₁ X₂ g hiso n y

end

end Work.SSGRoute.E1aClean
