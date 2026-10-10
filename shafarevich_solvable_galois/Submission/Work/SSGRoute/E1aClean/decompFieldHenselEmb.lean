import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts

/-!
# The canonical embedding of the henselisation into the completion, as a `def`

`E1aClean.decompField_embeds_completion` proves the *existence* of a ring embedding
`φ : K^h = Ω^{D_A ⊓ Gal(Ω/K)} →+* K_q` which is the identity on `K` and whose image is relatively
algebraically closed in the completion.  Its construction runs through
`NK.NeukirchUchida.coInAdjoin`, whose type (like every statement about the adjoined completion
`M = K_q · Ω`) carries the **explicit** instance argument
`[Algebra (q.adicCompletion ↥K) (placeCompletion A)]` — `NK.NeukirchUchida.adjoinPlaceCompletion`
takes it as a binder — and through `NK.NeukirchUchida.adicCompletionToPlaceCompletion`, which needs
`[IsSepClosure ↥K Ω]`.  A proof-local `letI` therefore cannot be exported, and any lemma *stated* in
terms of the characterisation `algebraMap (φ x) = coInAdjoin x` (or of that `Algebra` structure) is
unstateable outside that proof.

This file extracts the construction into a `def` whose **type** mentions no `coInAdjoin`: the
instance arguments and the compatibility `halg` are plain arguments of the definition.  Lemmas
about the embedding (notably the arithmetic input `hfix` of
`Work.SSGRoute.E1aClean.localDictionary_natural_family`, "`φ(k^h) ⊆ k_v`") can then be stated — see
`decompFieldHenselEmb_fixes_decomp` at the end.

`decompFieldHenselEmb_spec` records the characterisation; it is the only place where `coInAdjoin`
reappears, and it is itself stated with the same explicit arguments.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Pointwise

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.defProp false
set_option maxHeartbeats 1600000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
variable [IsSepClosure ↥K Ω]

/-- **The value of the canonical embedding at one point**, as an existence statement: the element
of the completion whose image in `M = K_q · Ω` is `coInAdjoin x`.

Keeping this as a named definition (rather than an anonymous `have` inside the proof of
`decompFieldHenselEmb`) is what makes `decompFieldHenselEmb_spec` provable from outside: the
`Classical.choose_spec` of this very definition is its specification. -/
noncomputable def decompFieldHenselEmbVal (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (x : ↥(henselOverDecomp k Ω K A)) :
    ∃ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) z =
        NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (x : Ω) := by
  have hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers q A hAqK
  exact coInAdjoin_mem_range_algebraMap_of_forall_fixed k Ω K A q hAqK halg hW (x : Ω)
    ((mem_fixedField_decomp_inf_ker_iff_forall k Ω K A (x : Ω)).mp
      (show (x : Ω) ∈ IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)
        from x.2))

/-- **The canonical embedding of the henselisation into the completion.**

`decompFieldHenselEmb k Ω K A hA q hAq halg : K^h →+* K_q` is the map produced by
`E1aClean.decompField_embeds_completion`: it is the identity on `K` and satisfies
`algebraMap (φ x) = coInAdjoin x` (`decompFieldHenselEmb_spec`), which determines it uniquely.

The `Algebra` structure of the completion `placeCompletion A` over `q.adicCompletion ↥K` and its
compatibility `halg` with `NK.NeukirchUchida.adicCompletionToPlaceCompletion` are *arguments* here,
so that the type of the definition mentions no `coInAdjoin` and can be used in statements. -/
noncomputable def decompFieldHenselEmb (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z) :
    ↥(henselOverDecomp k Ω K A) →+* (q.adicCompletion ↥K) := by
  have hmap_inj : Function.Injective (algebraMap (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)) :=
    RingHom.injective _
  let γ : ↥(henselOverDecomp k Ω K A) → q.adicCompletion ↥K :=
    fun x => Classical.choose (decompFieldHenselEmbVal k Ω K A hA q hAq halg x)
  have γ_spec : ∀ x : ↥(henselOverDecomp k Ω K A),
      algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) (γ x) =
        NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (x : Ω) :=
    fun x => Classical.choose_spec (decompFieldHenselEmbVal k Ω K A hA q hAq halg x)
  exact
    { toFun := γ
      map_one' := by
        apply hmap_inj
        rw [γ_spec 1, map_one, IntermediateField.coe_one, NK.NeukirchUchida.coInAdjoin_one]
      map_mul' := by
        intro a b
        apply hmap_inj
        rw [map_mul, γ_spec (a * b), γ_spec a, γ_spec b, IntermediateField.coe_mul,
          NK.NeukirchUchida.coInAdjoin_mul]
      map_zero' := by
        apply hmap_inj
        rw [γ_spec 0, map_zero, IntermediateField.coe_zero, NK.NeukirchUchida.coInAdjoin_zero]
      map_add' := by
        intro a b
        apply hmap_inj
        rw [map_add, γ_spec (a + b), γ_spec a, γ_spec b, IntermediateField.coe_add,
          NK.NeukirchUchida.coInAdjoin_add] }

/-- **The characterisation of the canonical embedding**: `algebraMap (φ x) = coInAdjoin x`. -/
theorem decompFieldHenselEmb_spec (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (x : ↥(henselOverDecomp k Ω K A)) :
    algebraMap (q.adicCompletion ↥K)
        ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
        (decompFieldHenselEmb k Ω K A hA q hAq halg x)
      = NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (x : Ω) :=
  Classical.choose_spec (decompFieldHenselEmbVal k Ω K A hA q hAq halg x)

/-! **The canonical embedding fixes the decomposition field under the local action.**

This is the arithmetic input `hfix` of `Work.SSGRoute.E1aClean.henselEmb_equivariant`: the image of
`k^h = Ω^{D_A}` in the completion `K_q` is fixed by `localAutHom τ`, i.e. lies in `k_v`.
Mathematically: the completion of the decomposition field is the completion of `k`.  The statement
is delegated (file `E1aClean/decompFieldHenselEmb_fixes_decomp.lean`): it is now stateable because
the embedding is a `def` with the `Algebra`/`IsSepClosure`/`halg` data as plain arguments. -/

end

end Work.SSGRoute.E1aClean
