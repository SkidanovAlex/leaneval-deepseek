/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The kernel of the residue map is the prime `v`

For a finite prime `v` of a number field `K`, the reduction map
`Work.LocalFields.residueMap v : 𝓞 K →+* κ_v` (reduce in `𝒪_v` and then modulo the maximal
ideal) has kernel exactly `v.asIdeal`.

Indeed, an integral element `x : 𝓞 K` maps to `0` in the residue field `κ_v = 𝒪_v/𝔪_v` iff its
image in `𝒪_v` is not a unit, i.e. iff its `v`-adic valuation is `< 1`; and by
`IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem` this happens exactly when
`x ∈ v.asIdeal`.

Together with `Work.LocalFields.residueMap_surjective` this gives the canonical isomorphism
`𝓞 K ⧸ v ≃+* κ_v` (`Work.LocalFields.residueEquiv`) and hence the finiteness of the residue
field of the completion.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
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
