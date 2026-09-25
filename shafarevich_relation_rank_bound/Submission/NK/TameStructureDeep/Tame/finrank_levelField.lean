import Mathlib
import Submission.NK.TameStructureDeep.Degree.unramifiedLevels
import Submission.NK.TameStructureDeep.Degree.Equality
import Submission.NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one

namespace NK.TameStructureDeep.Tame

/-- **The degree of an unramified level.**  For `κ = K_𝔭` with residue field of cardinality `q`, the level `levelField 𝔭 d = κ⟮ζ_{q ^ d - 1}⟯` has `κ`-dimension `d`.

Immediate from `NK.TameStructureDeep.Degree.finrank_adjoin_eq_orderOf` applied to `levelRoot 𝔭 d` (a primitive `(q ^ d - 1)`-th root of unity, with `p ∤ q ^ d - 1` by `not_residueChar_dvd_levelN`) together with `NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one`. -/
theorem finrank_levelField {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (d : ℕ) (hd : d ≠ 0) :
    Module.finrank (𝔭.adicCompletion K) ↥(NK.TameStructureDeep.Degree.levelField (K' := K') 𝔭 d) = d := by
  have hdeg := NK.TameStructureDeep.Degree.finrank_adjoin_eq_orderOf (K := K) (K' := K') 𝔭
    (NK.TameStructureDeep.Degree.levelN_ne_zero (K := K) 𝔭 d hd)
    (NK.TameStructureDeep.Degree.not_residueChar_dvd_levelN (K := K) 𝔭 d hd)
    (NK.TameStructureDeep.Degree.levelRoot_isPrimitiveRoot (K := K) (K' := K') 𝔭 d hd)
  rw [NK.TameStructureDeep.Degree.levelField, hdeg]
  exact NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one (K := K) 𝔭 d hd

end NK.TameStructureDeep.Tame
