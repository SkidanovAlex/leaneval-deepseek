import Mathlib
import Submission.NK.Indecomposed.Defs
import Submission.NK.LocalDecomposition.Basic

universe u

namespace NK.Indecomposed

/-- **The local groups of a decomposition group over its own prime.**

Let `A` be a place of `K'` over the finite prime `𝔭` of `K`, and let `V` be a local group of the
decomposition group `D_A` at a place over `𝔭`, i.e. `V = D_A ⊓ D_{A'}` for some place `A'` of `K'`
over `𝔭`.  Then either `A'` is the same place as `A` — and then `V = D_A` — or the two places are
distinct and `V = ⊥`, because the decomposition groups of distinct places intersect trivially
(`NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne`, CoNF XII (12.1.3)).

In particular the local groups of `D_A` over `𝔭` are only `D_A` and `⊥`; this is the group-theoretic
content of "the decomposition group is either the whole local group or trivial at its own prime". -/
theorem mem_localGroupSubgroupsOver_stabSubgroup {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    {V : Subgroup Gal(K'/K)}
    (hV : V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K')
      (NK.BrauerTwist.stabSubgroup A) 𝔭) :
    V = NK.BrauerTwist.stabSubgroup A ∨ V = ⊥ := by
  obtain ⟨A', hA'⟩ := hV
  rcases eq_or_ne A'.1 A with h | h
  · left
    obtain rfl : A'.1 = A := h
    simpa using hA'.symm
  · right
    have hA'ne : A'.1.comap (algebraMap K K') ≠ ⊤ := by
      rw [A'.2, ← h𝔭]
      exact hA
    have hbot := NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne (Ne.symm h) hA hA'ne
    rw [← hA']
    exact hbot

end NK.Indecomposed
