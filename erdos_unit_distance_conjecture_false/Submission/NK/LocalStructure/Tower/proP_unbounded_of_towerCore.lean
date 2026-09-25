import Mathlib
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalStructure.Tower.hasUnboundedTowerRank_of_numIndexSubgroups_tower

namespace NK.LocalStructure.Tower

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

theorem proP_unbounded_of_towerCore {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TowerRankCore K 𝔭 K' p) :
    NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(K'/𝔭.adicCompletion K)) :=
  hasUnboundedTowerRank_of_numIndexSubgroups_tower h.hp h.abelian_tower

end NK.LocalStructure.Tower
