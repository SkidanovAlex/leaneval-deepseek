import Mathlib
import Submission.Work.SSGRoute.E1aClean.Transport
import Submission.Work.SSGRoute.E1aClean.extPostIsoHomNat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the local `Ext`-transport in the first variable  (item (2) of the assembly)

`E1aClean/Transport.lean`'s `localExtTransport = finalStep ∘ (groupStep ∘ coeffStep)` is the
*named* replacement of `ext_localUnits_iso_Q`'s `Nonempty` witness.  Its factors are

* `coeffStep = extPostIsoHom hiso _ n`               (`hiso` is `X`-independent),
* `groupStep = (Rep.resFunctor eG.symm).mapExtAddHom _ _ n`, i.e. `Ext.mapExactFunctor`,
* `finalStep = extPostIsoHom (resResIsoIso …) _ n`   (`resResIsoIso` is `X`-independent),

so naturality in `X` (commuting with precomposition `mk₀ g ∘ ·`) is the three squares
`extPostIsoHom_natural`, `Ext.mapExactFunctor_comp`, `extPostIsoHom_natural`, glued by
`AddMonoidHom.comp_apply`.  Each is one `rw`.

The statement keeps the head symbol `localExtTransport` visible, so that the elaborator never has to
unfold the composite together with the whole `freeCover`/`Rep.res`/`PhiEgen` tower (the measured
cost of that unfolding is in the millions of heartbeats); the proof unfolds it once, explicitly.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 40000000

/-- **Item (2)**: the local `Ext`-transport is natural in the first variable. -/
theorem localExtTransport_mk_natural {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
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
    localExtTransport K' eG X₂ hiso n
        ((CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)).comp
          y (zero_add n))
      = (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap eG.symm.toMonoidHom
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g))).comp
          (localExtTransport K' eG X₁ hiso n y) (zero_add n) := by
  rw [localExtTransport, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    localExtTransport, AddMonoidHom.comp_apply]
  -- Step 1: `coeffStep` (postcomposition) commutes with precomposition.
  have hc : coeffStep K' eG X₂ hiso n
      ((CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)).comp
        y (zero_add n))
      = (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)).comp
        (coeffStep K' eG X₁ hiso n y) (zero_add n) :=
    extPostIsoHom_natural hiso
      (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g) n y
  rw [hc]
  -- Step 2: `groupStep` (an exact functor on `Ext`) commutes with precomposition.
  have hg : groupStep K' eG X₂ n
      ((CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)).comp
        (coeffStep K' eG X₁ hiso n y) (zero_add n))
      = (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap eG.symm.toMonoidHom
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g))).comp
          (groupStep K' eG X₁ n (coeffStep K' eG X₁ hiso n y)) (zero_add n) := by
    rw [groupStep, groupStep, Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply,
      CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  rw [hg]
  -- Step 3: `finalStep` (postcomposition) commutes with precomposition.
  exact extPostIsoHom_natural (resResIsoIso K' eG (localCoeff K'))
    (Rep.resMap eG.symm.toMonoidHom
      (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype g)) n _

end

end Work.SSGRoute.E1aClean
