import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat

namespace Work.SSGRoute.E1aClean

theorem decompFieldHenselEmb_algebraMap (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (x : ↥K) :
    Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg
        ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩
      = algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) x := by
  -- The map `algebraMap (q.adicCompletion ↥K) ↥(adjoinPlaceCompletion q A)` out of a field into a
  -- nontrivial ring is injective; it suffices to compare the two sides after applying it, where the
  -- characterisation `decompFieldHenselEmb_spec` turns the left-hand side into `coInAdjoin`.
  have hmap_inj : Function.Injective (algebraMap (q.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)) :=
    RingHom.injective _
  -- The compatibility of `coInAdjoin` with the diagonal embedding of `K`: an element of `K` has the
  -- same image in the adjoined completion whether it is pushed through `Ω` or through its
  -- `q`-adic completion.
  have hlink : ∀ c : ↥K,
      NK.NeukirchUchida.coInAdjoin (K := ↥K) (K' := Ω) q A (algebraMap ↥K Ω c) =
        algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) := by
    intro c
    apply Subtype.ext
    rw [NK.NeukirchUchida.coe_coInAdjoin]
    rw [show ((algebraMap (q.adicCompletion ↥K)
          ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) : ↥(NK.NeukirchUchida.adjoinPlaceCompletion
            (K := ↥K) (K' := Ω) q A)) : NK.NeukirchUchida.placeCompletion A) =
        algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)
          (algebraMap ↥K (q.adicCompletion ↥K) c) from rfl]
    rw [halg, NK.NeukirchUchida.adicCompletionToPlaceCompletion_algebraMap]
  apply hmap_inj
  rw [Work.SSGRoute.E1aClean.decompFieldHenselEmb_spec k Ω K A hA q hAq halg
        ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩]
  exact hlink x

end Work.SSGRoute.E1aClean
