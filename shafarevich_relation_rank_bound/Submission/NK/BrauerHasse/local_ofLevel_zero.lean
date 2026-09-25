import Mathlib
import Submission.NK.BrauerHasse.Profinite

set_option autoImplicit false

universe u

namespace NK.BrauerHasse

/-- **`0` is a class of every local level.**  The zero of `LocalH2 p U A` is by definition the
image of the zero of the bottom local level `LocalLevelH2 p U A ⊥`; since the local inflation map
`localLevelMap` is a morphism of `Coeff p`-modules it carries `0` to `0`, so the inflation of the
zero class of any level `L` down to the level `⊥` is the same class.  In other words, the
structure maps `LocalH2.ofLevel` are compatible with the distinguished zero elements. -/
theorem local_ofLevel_zero {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) {U : Subgroup Gal(K'/K)} (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LocalH2.ofLevel p U A L (0 : NK.BrauerHasse.LocalLevelH2 p U A L) = 0 := by
  -- Compare `L` with the bottom level, at which the zero of the colimit is defined.
  rw [show (0 : LocalLevelH2 p U A L) =
      localLevelMap p U A (bot_le : (⊥ : FiniteGaloisIntermediateField K K') ≤ L)
        (0 : LocalLevelH2 p U A ⊥) from (map_zero _).symm]
  exact LocalH2.ofLevel_levelMap (p := p) (U := U) (A := A) bot_le (0 : LocalLevelH2 p U A ⊥)

end NK.BrauerHasse
