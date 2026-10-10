import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_fixes_decomp

namespace Work.SSGRoute.E1aClean

open scoped Pointwise

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# The image of the henselisation embedding is relatively algebraically closed

`decompFieldHenselEmb k Ω K A hA q hAq halg : K^h →+* K_q` is the canonical embedding of the
henselisation `K^h = Ω^{D_A ⊓ Gal(Ω/K)} = K·Ω^{D_A}` into the completion `K_q` of `K` at the prime
`q` cut out by the place `A` (see `E1aClean/decompFieldHenselEmb.lean`, where it is characterised by
`decompFieldHenselEmb_spec`: `algebraMap (φ x) = coInAdjoin x`).

This file proves the **arithmetic input** that the image of `φ` is *relatively algebraically
closed* in `K_q`: an element `z ∈ K_q` satisfying a nonzero polynomial equation with coefficients
in `φ(K^h)` is already in `φ(K^h)`.

The proof is the one given for the field-generic statement
`E1aClean.decompField_embeds_completion` (its third conjunct), transported to the `def`
`decompFieldHenselEmb`:

* transport the polynomial along `algebraMap ↥K Ω` and then along the canonical ring hom
  `coHom : Ω →+* M` into the adjoined completion `M = K_q · Ω`; the two routes
  `K^h → K_q → M` and `K^h → Ω → M` agree (`decompFieldHenselEmb_spec`);
* `Ω` is algebraically closed, so the transported polynomial has a root `y ∈ Ω` whose image in `M`
  is `algebraMap (q.adicCompletion ↥K) M z` (with `coHom ∘ algebraMap = algebraMap ∘ φ` this is
  exactly `eval` of the transported polynomial at `algebraMap z`);
* `y` lies in the henselisation, because its image in `M` lies in the image of the completion
  (`Work.SSGRoute.PT.mem_fixedField_of_coInAdjoin_mem_range`);
* finally `φ ⟨y, ·⟩ = z` because `algebraMap (q.adicCompletion ↥K) M` is injective.
-/

theorem decompFieldHenselEmb_relAlgClosed (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [IsSepClosure ↥K Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z) :
    ∀ z : q.adicCompletion ↥K,
      (∃ r : Polynomial ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A),
        r ≠ 0 ∧ Polynomial.eval₂
          (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg) z r = 0) →
      ∃ x : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A),
        Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg x = z := by
  classical
  haveI hAlgΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers q A hAqK
  have hmap_inj : Function.Injective (algebraMap (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)) :=
    RingHom.injective _
  intro z ⟨r, hr0, hr⟩
  -- the canonical ring hom `Ω →+* M` into the adjoined completion `M = K_q · Ω`
  let coHom : Ω →+* ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) :=
    { toFun := fun y => NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A y
      map_one' := NK.NeukirchUchida.coInAdjoin_one q A
      map_mul' := fun a b => NK.NeukirchUchida.coInAdjoin_mul q A a b
      map_zero' := NK.NeukirchUchida.coInAdjoin_zero q A
      map_add' := fun a b => NK.NeukirchUchida.coInAdjoin_add q A a b }
  -- the transported polynomial is nonzero
  have hp0 : (r.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (f := algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω)
      (fun a b h => Subtype.ext h)).mpr hr0
  -- the two routes into `M` agree
  have hcomp : coHom.comp (algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω) =
      (algebraMap (q.adicCompletion ↥K)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)).comp
        (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg) := by
    refine RingHom.ext fun a => ?_
    exact (Work.SSGRoute.E1aClean.decompFieldHenselEmb_spec k Ω K A hA q hAq halg a).symm
  -- hence `algebraMap (q.adicCompletion ↥K) M z` is a root of the transported polynomial
  have heval : ((r.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) Ω)).map
        coHom).eval
      (algebraMap (q.adicCompletion ↥K)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) z) = 0 := by
    rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, Polynomial.eval_map,
      Polynomial.eval₂_hom, ← Polynomial.eval₂_eq_eval_map, hr, map_zero]
  -- a root of it in `Ω`
  obtain ⟨y, hy⟩ := mem_range_of_eval_eq_zero_of_isAlgClosed coHom hp0 heval
  -- `y` lies in the henselisation
  have hyfix : y ∈ Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A := by
    change y ∈ IntermediateField.fixedField
      (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)
    rw [mem_fixedField_decomp_inf_ker_iff k Ω K A y]
    exact Work.SSGRoute.PT.mem_fixedField_of_coInAdjoin_mem_range q A
      (halg := halg) hAqK hW y ⟨z, hy⟩
  refine ⟨⟨y, hyfix⟩, ?_⟩
  -- and it is the preimage of `z`
  apply hmap_inj
  rw [Work.SSGRoute.E1aClean.decompFieldHenselEmb_spec k Ω K A hA q hAq halg ⟨y, hyfix⟩]
  exact hy

end

end Work.SSGRoute.E1aClean
