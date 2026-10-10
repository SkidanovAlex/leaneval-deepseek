import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.LocalFields.Residue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

theorem residueMap_ker {K : Type*} [Field K] [NumberField K]
    (v : Work.LocalFields.FinitePrime K) :
    RingHom.ker (Work.LocalFields.residueMap v) = v.asIdeal := by
  ext x
  -- `residueMap v x = 0` iff the image of `x` in `𝒪_v` is a nonunit, i.e. has valuation `< 1`
  rw [RingHom.mem_ker, residueMap_apply, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  -- the image of `x : 𝓞 K` in the completion is `x` itself
  change Valued.v ((x : K) : Completion K v) < 1 ↔ x ∈ v.asIdeal
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_lt_one_iff_mem x

end Work.LocalFields
