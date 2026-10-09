import Mathlib
import Submission.Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Filter IsDedekindDomain Topology Set

namespace Commons.NumberTheory.NumberField.Set

/-- **A finite set of primes has Dirichlet density zero.**

For a number field `K` and a finite set `S` of nonzero prime ideals of `𝓞 K`, the partial sum
`∑_{𝔭 ∈ S} N𝔭^{-s}` is bounded (it is at most `#S`, by
`NumberField.Set.primeIdealZetaSum_le_card_of_finite`), while the denominator
`∑_𝔭 N𝔭^{-s}` tends to `+∞` as `s → 1⁺`
(`Commons.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT`); hence the ratio tends to `0`. -/
theorem hasDirichletDensity_zero_of_finite {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S.Finite) :
    NumberField.Set.HasDirichletDensity S 0 := by
  unfold NumberField.Set.HasDirichletDensity
  refine tendsto_bdd_div_atTop_nhds_zero
    (b := 0) (B := (S.ncard : ℝ)) ?_ ?_
    (tendsto_primeIdealZetaSum_univ_nhdsGT K)
  · exact Eventually.of_forall fun s => NumberField.Set.primeIdealZetaSum_nonneg S s
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact NumberField.Set.primeIdealZetaSum_le_card_of_finite (S := S) hS (by
      have : (1 : ℝ) < s := hs
      linarith)

end Commons.NumberTheory.NumberField.Set
