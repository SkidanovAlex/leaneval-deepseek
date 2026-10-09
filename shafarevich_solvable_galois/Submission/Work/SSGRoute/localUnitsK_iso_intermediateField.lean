import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.exists_localField_subfield
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat
import Submission.Work.SSGRoute.localAutHom_bijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

/-- **E7a place glue, step 2(b): `localUnitsK` is the units of the intermediate field, with the
Galois action.**  With `𝔭 := Work.SSGRoute.primeUnder k A hA`, `q` a prime of `K` over it, and the
canonical `k_v`-algebra structure on `K_w = q.adicCompletion K` (from
`Work.SSGRoute.adicCompletionMapAt`, supplied by `Work.SSGRoute.exists_adicCompletion_algebra_compat`),
let `K' : IntermediateField (localFieldAt k A hA) (localClosureAt k A hA)` be finite Galois over
`k_v` and isomorphic to `K_w` over `k_v` (the output of `Work.SSGRoute.exists_localField_subfield`).

Then there is `eG : ↥(decompK (Place.ofFinite q)) ≃* (K' ≃ₐ[L₀] K')` — the composite of
`Work.SSGRoute.localAutHom_bijective` (with `NK.HassePrinciple.localAutHom_injective` for
uniqueness) with conjugation by the given `↥K' ≃ₐ[L₀] K_w` — such that NK's
`Work.SSGRoute.localUnitsK (Place.ofFinite q)` (whose action is *defined* as `localAutHom`) is
isomorphic, as a `Rep Coeff ↥(decompK (Place.ofFinite q))`, to the units `(↥K')ˣ` carrying the Galois
action of `K' ≃ₐ[L₀] K'` transported along `eG`.

This turns the *local field* coefficient module `K_wˣ` into the `Kˣ` of the intermediate field,
i.e. into the form produced by the continuous descent (`SSGRoute/ext_continuous_descent`).

Notes for the proof (verified by review): the carrier of `localUnitsK (Place.ofFinite q)` is
literally `Additive (Units (q.adicCompletion K))` (`Place.localField_ofFinite` is `rfl`), so there is
no carrier mismatch; the action is built only from the ring automorphism `localAutHom σ`, so it does
not depend on which `Algebra L₀ K_w` instance is in scope, and the isomorphism is
`ψ ∘ localAutHom σ ∘ ψ⁻¹` for `ψ : K_w ≅ K'` over `L₀`; the *one* obligation carried by the proof is
that each `localAutHom σ` is `L₀`-linear for the `adicCompletionMapAt` structure, which follows from
`localAut_continuous` + `NK.GlobalCFT.Galois.denseRange_algebraMap_localField` applied to
`localAut_algebraMap`. -/
theorem localUnitsK_iso_intermediateField (k : Type) (Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
    ∀ (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
        (Work.SSGRoute.localClosureAt k A hA))
      [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
      [IsGalois (Work.SSGRoute.localFieldAt k A hA) K'],
      Nonempty (↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K)) →
      ∃ eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
          (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'),
        Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
          Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
            (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))) := by
  intro K' _ _ hψ
  obtain ⟨ψ⟩ := hψ
  -- **(1) the group isomorphism `D_q ≃* Gal(K_w/k_v)`**, from the local Galois correspondence.
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Work.SSGRoute.primeUnder k A hA
  let eLoc : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (q.adicCompletion K ≃ₐ[Work.SSGRoute.localFieldAt k A hA] q.adicCompletion K) :=
    NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois (K := k) (L := ↥K) Q q hLies
  -- its underlying ring automorphism is NK's `localAutHom`
  have eLoc_ring : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)),
      (eLoc σ).toRingEquiv =
        Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite q) σ := fun σ =>
    (localAutHom_eq_isoLocalGalois (K := k) (L := ↥K) Q q hLies σ).symm
  -- **(2) conjugation by `ψ : K' ≃ₐ[L₀] K_w`**
  let eConj : (q.adicCompletion K ≃ₐ[Work.SSGRoute.localFieldAt k A hA] q.adicCompletion K) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') :=
    { toFun := fun f => ψ.trans (f.trans ψ.symm)
      invFun := fun g => ψ.symm.trans (g.trans ψ)
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp
      map_mul' := fun f g => by ext x; simp [AlgEquiv.mul_apply] }
  let eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') := eLoc.trans eConj
  have eG_apply : ∀ (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (y : ↥K'), (eG σ) y = ψ.symm ((eLoc σ) (ψ y)) := fun σ y => rfl
  have eLoc_apply : ∀ (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (z : q.adicCompletion K),
      (eLoc σ) z = Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite q) σ z := by
    intro σ z
    rw [← eLoc_ring σ]
    rfl
  refine ⟨eG, ?_⟩
  -- **(3) the `Coeff`-linear equivalence `K_wˣ ≃ K'ˣ`**
  let Ψ : (q.adicCompletion K)ˣ ≃* (↥K')ˣ := Units.mapEquiv ψ.symm.toMulEquiv
  have Ψ_coe : ∀ w : Additive (Units (q.adicCompletion K)),
      Units.val (Ψ (Additive.toMul w)) = ψ.symm (Units.val w) := fun w => rfl
  let Φ : Additive (Units (q.adicCompletion K)) ≃ₗ[SSGRoute.PTExt.Coeff]
      Additive (Units ↥K') :=
    { MulEquiv.toAdditive Ψ with
      map_smul' := fun n x => by
        show MulEquiv.toAdditive Ψ (n.down • x) = n.down • MulEquiv.toAdditive Ψ x
        exact (MulEquiv.toAdditive Ψ).toAddMonoidHom.map_zsmul n.down x }
  have Φ_ofMul : ∀ u : (q.adicCompletion K)ˣ, Φ (Additive.ofMul u) = Additive.ofMul (Ψ u) :=
    fun u => rfl
  have Φ_coe : ∀ w : Additive (Units (q.adicCompletion K)),
      Units.val (Φ w) = ψ.symm (Units.val w) := fun w => rfl
  -- the two representations at the level of their `ρ`
  have hρX : ∀ (g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (w : Additive (Units (q.adicCompletion K))),
      (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ g w
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) g (Additive.toMul w)) := fun g w => rfl
  have hρY : ∀ (τ : K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
      (w : Additive (Units ↥K')),
      (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
        (Additive (Units ↥K'))).ρ τ w
        = Additive.ofMul (Units.map (τ : ↥K' →* ↥K') (Additive.toMul w)) :=
    fun τ w => rfl
  refine ⟨Rep.mkIso (ρ := (SSGRoute.PTExt.localUnitsK (k := k)
        (NK.GlobalCFT.Place.ofFinite q)).ρ)
      (σ := (Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))).ρ)
      (Representation.Equiv.mk Φ ?_heq)⟩
  -- **(4) equivariance**, pointwise on the underlying units
  have heq_pt : ∀ (g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (w : Additive (Units (q.adicCompletion K))),
      Φ ((SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ g w)
        = (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
            (Additive (Units ↥K'))).ρ (eG g) (Φ w) := by
    intro g w
    have h1 : Φ ((SSGRoute.PTExt.localUnitsK (k := k)
        (NK.GlobalCFT.Place.ofFinite q)).ρ g w)
        = Additive.ofMul (Ψ (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) g (Additive.toMul w))) := by
      rw [hρX]
      rfl
    have h2 : (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
        (Additive (Units ↥K'))).ρ (eG g) (Φ w)
        = Additive.ofMul (Units.map (eG g : ↥K' →* ↥K') (Ψ (Additive.toMul w))) := by
      rw [show Φ w = Additive.ofMul (Ψ (Additive.toMul w)) from rfl]
      rw [hρY]
      rfl
    rw [h1, h2]
    apply Additive.ofMul.injective
    apply Units.ext
    have hL : Units.val (Ψ (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) g (Additive.toMul w)))
        = ψ.symm (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite q) g
            (Units.val w)) := by
      show ψ.symm (Units.val ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q)) g (Additive.toMul w))) = _
      rw [NK.HassePrinciple.coe_localUnitsEquiv]
      rfl
    have hR : Units.val (Units.map (eG g : ↥K' →* ↥K') (Ψ (Additive.toMul w)))
        = ψ.symm (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite q) g
            (Units.val w)) := by
      show (eG g) (Units.val (Ψ (Additive.toMul w))) = _
      rw [Ψ_coe, eG_apply, AlgEquiv.apply_symm_apply]
      exact congrArg ψ.symm (eLoc_apply g (Units.val w))
    exact hL.trans hR.symm
  intro g
  apply LinearMap.ext
  intro x
  exact heq_pt g x

end Work.SSGRoute
