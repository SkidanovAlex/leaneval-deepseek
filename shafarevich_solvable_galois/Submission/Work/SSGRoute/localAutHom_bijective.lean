import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open NumberField IsDedekindDomain

/-! ## Auxiliary bridges used below -/

/-- `RingEquiv.cast` is the transport `▸`. -/
theorem ringEquiv_cast_apply_eq {ι : Type*} {R : ι → Type*} [∀ i, Mul (R i)] [∀ i, Add (R i)]
    {i j : ι} (h : i = j) (x : R i) : RingEquiv.cast h x = h ▸ x := by
  cases h; rfl

/-- **`localAutHom` is `localAction`**: NK's local automorphism of `L_w` is the transport of the
canonical isomorphism `L_w ≃+* L_{σ w}` along `σ • w = w`. -/
theorem localAutHom_eq_localAction {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (w : NK.GlobalCFT.Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    NK.HassePrinciple.localAutHom (K := K) w σ =
      NK.GlobalCFT.Inclusion.Place.localAction (σ : L ≃ₐ[K] L) w
        (MulAction.mem_stabilizer_iff.mp σ.2) := by
  refine RingEquiv.ext (fun y => ?_)
  simp only [NK.HassePrinciple.localAutHom, MonoidHom.coe_mk, OneHom.coe_mk,
    NK.HassePrinciple.localAut,
    NK.GlobalCFT.Inclusion.Place.localAction_apply, RingEquiv.trans_apply,
    RingEquiv.cast_apply]
  exact ringEquiv_cast_apply_eq _ _

/-- **`localAutHom` computes the local Galois correspondence**: for a finite Galois extension
`L/K` of number fields, a prime `q` of `L` over `Q` of `K` and an element `σ` of the stabiliser of
the place `ofFinite q`, the NK local automorphism of `L_q` is the image of `σ` under the
isomorphism `D_q ≃* Gal(L_q/K_Q)`. -/
theorem localAutHom_eq_isoLocalGalois {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (σ : ↥(NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))) :
    NK.HassePrinciple.localAutHom (K := K) (NK.GlobalCFT.Place.ofFinite q) ⟨σ.1, σ.2⟩ =
      (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois (K := K) (L := L) Q q hq σ).toRingEquiv := by
  rw [NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois_apply]
  rw [localAutHom_eq_localAction]
  rw [NK.GlobalCFTdeep.localAction_eq_decompositionToAdicCompletion]

/-- **E7a place glue, step 2(a): NK's local automorphism map is onto the `k_v`-linear
automorphisms.**  With `𝔭 := Work.SSGRoute.primeUnder k A hA` and `q` a prime of `K` lying over it,
put the `k_v`-algebra structure on `K_w = q.adicCompletion K` coming from
`Work.SSGRoute.adicCompletionMapAt` (`RingHom.toAlgebra`; the compatibility data is supplied by
`Work.SSGRoute.exists_adicCompletion_algebra_compat`).  Then every `k_v`-linear automorphism of
`K_w` is `Work.SSGRoute.localAutHomAt k (Place.ofFinite q) σ` for some `σ` in the decomposition
group `↥(decompK (k := k) (Place.ofFinite q))`.

This is the surjectivity half of the local Galois correspondence for the finite place `q` — the
injectivity half is already on disk as `NK.HassePrinciple.localAutHom_injective`, and with
`|D_q| = e·f = [K_q : k_v]` it gives `D_q ≅ Gal(K_q/k_v)`.  It is what lets the `Rep`-level action
of `localUnitsK (Place.ofFinite q)` (defined through `localAutHom`) be transported to the Galois
action on the units of the intermediate field produced by
`Work.SSGRoute.exists_localField_subfield`. -/
theorem localAutHom_bijective (k : Type) (Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
    ∀ f : (q.adicCompletion K ≃ₐ[Work.SSGRoute.localFieldAt k A hA] q.adicCompletion K),
      ∃ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)),
        Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite q) σ = f.toRingEquiv := by
  intro f
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Work.SSGRoute.primeUnder k A hA
  let e := NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois (K := k) (L := ↥K) Q q hLies
  refine ⟨⟨(e.symm f).1, (e.symm f).2⟩, ?_⟩
  have h := localAutHom_eq_isoLocalGalois (K := k) (L := ↥K) Q q hLies (e.symm f)
  rw [h, MulEquiv.apply_symm_apply]

end Work.SSGRoute
