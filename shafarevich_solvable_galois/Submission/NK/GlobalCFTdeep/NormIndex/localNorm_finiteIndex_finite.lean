import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.NormIndex

theorem localNorm_finiteIndex_finite {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hq : q.asIdeal.LiesOver Q.asIdeal) : (NK.GlobalCFT.Place.localNormFinite q Q hq).range.FiniteIndex := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Finite ((Q.adicCompletion K)ˣ ⧸
      (NK.GlobalCFT.Place.localNormFinite q Q hq).range) :=
    Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
      (K := K) (L := L) Q q hq
  exact Subgroup.finiteIndex_of_finite_quotient

end NK.GlobalCFTdeep.NormIndex
