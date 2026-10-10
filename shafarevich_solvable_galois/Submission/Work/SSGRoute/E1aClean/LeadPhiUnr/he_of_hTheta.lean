import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The canonical embedding `φ = decompFieldHenselEmb k Ω K A hA q hAq halg : K^h →+* K_q` is
injective: it is a ring homomorphism from the field `K^h` into the completion `K_q`. -/
private lemma henselEmb_injective
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z) :
    Function.Injective
      (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg) :=
  RingHom.injective _

theorem he_of_hTheta
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
          ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (θ : Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (hθ : ∀ u : (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))ˣ,
        Rep.Hom.hom θ (Additive.ofMul u) = Additive.ofMul
          (Units.map (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom u)) :
    ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : ↥K),
      ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
        = ((τ : ↥K ≃ₐ[k] ↥K) x : Ω) := by
  -- `φ` is the canonical embedding `K^h →+* K_q` of `E1aClean/decompFieldHenselEmb`.
  -- The hypothesis `hθ` says that `θ`, whose values are pinned to `Units.map φ`, is a morphism of
  -- `D_q`-representations; unwinding it gives, for `u : (K^h)ˣ`,
  --   `φ ((e τ) u) = localAutHom τ (φ u)`.
  -- Since `φ` restricts to `algebraMap` on `K` (`decompFieldHenselEmb_algebraMap`) and
  -- `localAutHom τ` is `algebraMap`-equivariant (`localAut_algebraMap`), this reads
  --   `φ ((e τ) u) = φ (u')`  with `u' = ⟨τ x, _⟩`,
  -- and injectivity of `φ` (`RingHom.injective`) yields `(e τ) u = u'`, i.e. `τ` is the
  -- restriction of `e τ` to `K ⊆ K^h`.
  intro τ x
  by_cases hx : x = 0
  · subst hx
    have h0 : (⟨((0 : ↥K) : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A (0 : ↥K).2⟩ :
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) = 0 := Subtype.ext rfl
    rw [h0, map_zero]
    simp
  · have hxne : (⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ :
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) ≠ 0 := by
      intro h
      refine hx (Subtype.ext ?_)
      simpa using congrArg Subtype.val h
    let u : (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))ˣ :=
      Units.mk0 ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ hxne
    have h2 := Representation.IntertwiningMap.isIntertwining _ _
      (Rep.Hom.hom θ) τ (Additive.ofMul u)
    have h2' : (Rep.Hom.hom θ) (Additive.ofMul (Units.map (e τ).toMonoidHom u))
        = (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ
            ((Rep.Hom.hom θ) (Additive.ofMul u)) := h2
    have h2'' : Additive.ofMul (Units.map
          (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom
          (Units.map (e τ).toMonoidHom u))
        = (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ τ
            (Additive.ofMul (Units.map
              (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom u)) :=
      (hθ (Units.map (e τ).toMonoidHom u)).symm.trans
        (h2'.trans (congrArg (fun z => (SSGRoute.PTExt.localUnitsK (k := k)
          (NK.GlobalCFT.Place.ofFinite q)).ρ τ z) (hθ u)))
    have h3 : (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
          ((e τ) (u : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
        = NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
            ((Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
              (u : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))) := by
      have hh := congrArg (fun z : Additive (q.adicCompletion ↥K)ˣ =>
        ((Additive.toMul z : (q.adicCompletion ↥K)ˣ) : q.adicCompletion ↥K)) h2''
      exact hh
    have hu : (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
        (u : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))
        = algebraMap ↥K (q.adicCompletion ↥K) x := by
      show (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
        ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ = _
      exact Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap k Ω K A hA q hAq halg x
    have h4 : (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
          ((e τ) (u : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
        = algebraMap ↥K (q.adicCompletion ↥K) ((τ : ↥K ≃ₐ[k] ↥K) x) := by
      rw [h3, hu]
      exact NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) τ x
    have h5 : (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
          ((e τ) (u : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
        = (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg)
            ⟨(((τ : ↥K ≃ₐ[k] ↥K) x : ↥K) : Ω),
              Work.SSGRoute.E1aClean.le_henselField k Ω K A ((τ : ↥K ≃ₐ[k] ↥K) x).2⟩ := by
      rw [h4, Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap k Ω K A hA q hAq halg
        ((τ : ↥K ≃ₐ[k] ↥K) x)]
    have h6 : (e τ) (u : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))
        = ⟨(((τ : ↥K ≃ₐ[k] ↥K) x : ↥K) : Ω),
            Work.SSGRoute.E1aClean.le_henselField k Ω K A ((τ : ↥K ≃ₐ[k] ↥K) x).2⟩ :=
      henselEmb_injective k Ω K A hA q hAq halg h5
    exact congrArg Subtype.val h6

end Work.SSGRoute.E1aClean.LeadPhiUnr
