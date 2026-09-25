import Mathlib
import Submission.NK.ReconstructEndgame.Basic

/-!
# The `ℚ`-algebra form of Shimizu's Lemma 4f.2 agrees with the plain form

`NK.ReconstructEndgame.RankStrictMonoLevelInputGenDerived K K' ℓ` (see `Basic.lean`) is
*definitionally* `NK.Reconstruct.RankStrictMonoLevelInputGen K' ℓ` with the `ℚ`-algebra structure
on `K'` replaced by the canonical one `NK.ReconstructEndgame.ratAlgebra K K'` derived from the
number field `K`, and with the derived `IsSepClosure ℚ K'` instance supplied by `letI`.

The two forms are therefore logically equivalent: there is at most one `ℚ`-algebra structure on the
field `K'` (`Subsingleton (Algebra ℚ K')`, since the `algebraMap` out of the prime field `ℚ` is
unique and the `•` is determined by it), so the two `letI`-shadowed instances can be identified by
`Subsingleton.elim`, and the `IsSepClosure`/`IsGalois` data are propositions and hence
proof-irrelevant.  This lemma is the bridge that lets a caller state the Shimizu rank input in the
plain `NK.Reconstruct` vocabulary (with the ambient `Algebra ℚ K'` instance) and use it where
`RankStrictMonoLevelInputGenDerived` is expected, and conversely.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.ReconstructEndgame

theorem rankStrictMonoLevelInputGen_congr (K K' : Type*) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Algebra ℚ K'] [IsSepClosure ℚ K'] (ℓ : ℕ)
    [Fact ℓ.Prime] :
    NK.Reconstruct.RankStrictMonoLevelInputGen K' ℓ ↔
      RankStrictMonoLevelInputGenDerived K K' ℓ := by
  unfold RankStrictMonoLevelInputGenDerived
  constructor <;> intro h <;> convert h using 2 <;> exact Subsingleton.elim _ _

end NK.ReconstructEndgame
