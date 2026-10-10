import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.ExtChain.exists_primeUnder_hAq
import Submission.Work.SSGRoute.PT.e1aBetaCan_hAq_decomp_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

theorem exists_place_under_isFinPlace (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∀ x : NumberField.RingOfIntegers K,
        x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) ∧
      (SSGRoute.decomp k A).map (SSGRoute.res k K) =
        SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q) := by
  -- The prime `q` of `𝓞 K` below `A`: the lying-over condition on `q` is
  -- `Work.SSGRoute.ExtChain.exists_primeUnder_hAq`.
  obtain ⟨q, hq⟩ :=
    Work.SSGRoute.ExtChain.exists_primeUnder_hAq (k := k) (Ω := Ω) K A hA
  refine ⟨q, hq, ?_⟩
  -- The restriction of the decomposition group is the decomposition group of `q`:
  -- `Work.SSGRoute.PT.e1aBetaCan_hAq_decomp_map` applied to the lying-over condition `hq`.
  exact Work.SSGRoute.PT.e1aBetaCan_hAq_decomp_map k Ω K A hA q hq

end Work.SSGRoute.PT
