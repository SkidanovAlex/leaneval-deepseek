import Mathlib
import Submission.NK.BrauerHasse.Profinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

universe u

namespace NK.BrauerHasse

/-- **`0` is a class of every level.**  The zero of `H2Profinite p U` is by definition the image of
the zero of the bottom level `LevelH2 p U ⊥`; since the transition map `levelMap` is a morphism of
`Coeff p`-modules it carries `0` to `0`, so the inflation of the zero class of any level `L` down
to the level `⊥` is the same class.  In other words, the structure maps `H2Profinite.ofLevel L`
are compatible with the distinguished zero elements. -/
theorem ofLevel_zero {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {p : ℕ} {U : Subgroup Gal(K'/K)}
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.H2Profinite.ofLevel L (0 : NK.BrauerHasse.LevelH2 p U L) = 0 := by
  -- Compare `L` with the bottom level, at which the zero of the colimit is defined.
  have key : H2Profinite.ofLevel L (0 : LevelH2 p U L) =
      H2Profinite.ofLevel (⊥ : FiniteGaloisIntermediateField K K')
        (0 : LevelH2 p U ⊥) := by
    rw [← H2Profinite.ofLevel_levelMap (p := p) (U := U) (L := ⊥) (L' := L) bot_le
      (0 : LevelH2 p U ⊥)]
    simp [levelMap]
  rw [key]
  rfl

end NK.BrauerHasse
