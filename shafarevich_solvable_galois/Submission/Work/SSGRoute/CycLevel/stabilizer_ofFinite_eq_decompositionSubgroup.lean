import Mathlib
import Submission.Work.SSGRoute.CycLevel.CycLevelImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- **The stabiliser of a finite place is its decomposition subgroup.**

For a finite Galois extension `L/K` of number fields and a prime `q` of `𝓞 L`, the stabiliser of
`Place.ofFinite q` in `Gal(L/K)` (for the `NK.GlobalCFT.Place` action) is the decomposition group
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroup q` (for the commons action on
primes).  Both are `{σ | σ • q = q}`; the two actions are identified by
`NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff` together with
`NK.GlobalCFT.Place.smul_ofFinite` and `NK.GlobalCFT.Place.ofFinite_inj`.

(The same statement, for a tower `k ⊆ K ⊆ E`, is already proved in this workspace as
`Work.SSGRoute.eb_stab_eq_decomp_aux` / the twin in `Submission/Work/SSGRoute/E8Helpers.lean`;
specialising `K := k` gives this statement.) -/
theorem stabilizer_ofFinite_eq_decompositionSubgroup {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q) =
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q := by
  ext σ
  rw [MulAction.mem_stabilizer_iff,
    NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff,
    NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]

end Work.SSGRoute.CycLevel
