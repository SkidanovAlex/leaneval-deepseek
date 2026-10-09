import Mathlib
import Submission.Work.SSGRoute.local_lifting_setup
import Submission.Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The residue field at a finite place has characteristic `resCharAt`

Let `k` be a number field, `Ω` a field with an algebra structure over `k`, and `A ≤ Ω` a valuation
subring whose restriction to `k` is a *finite* place (`SSGRoute.IsFinPlace k A`).  Write
`𝔭 = Submission.NeukirchUchida.primeOf A hA` for the prime of `𝓞 k` below `A` and
`p = NK.TameStructureDeep.Tame.resCharAt 𝔭` for its residue characteristic.  We prove

  `CharP (IsLocalRing.ResidueField ↥A) p`,

i.e. that the residue field of the valuation ring of `Ω` at the place `A` has characteristic `p`.

The residue field is `↥A ⧸ 𝔪_A`, so `(n : ResidueField ↥A) = 0` iff `(n : ↥A)` lies in the maximal
ideal, i.e. iff `(n : ↥A)` is *not* a unit.  The arithmetic input
`isUnit_natCast_iff_not_dvd_resCharAt` says precisely that `(n : ↥A)` is a unit iff `p ∤ n`, which
turns the characterisation into the defining property of `CharP`.
-/

namespace Work.SSGRoute

theorem charP_residueField_isFinPlace
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    CharP (IsLocalRing.ResidueField ↥A)
      (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA)) := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (IsLocalRing.residue ↥A) n, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact (not_iff_not.mpr (isUnit_natCast_iff_not_dvd_resCharAt k Ω A hA n)).trans not_not

end Work.SSGRoute
