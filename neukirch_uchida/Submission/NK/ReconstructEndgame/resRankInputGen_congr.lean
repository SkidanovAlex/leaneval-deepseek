import Mathlib
import Submission.NK.ReconstructEndgame.Basic

namespace NK.ReconstructEndgame

/-- **The `ℚ`-algebra forms of Shimizu's rank computation agree with the plain forms.**

`ResRankInputGenDerived K K' ℓ` is `NK.Reconstruct.ResRankInputGen K' ℓ` stated with the `ℚ`-algebra
structure `ratAlgebra K K'` on `K'` (and the derived instance `IsSepClosure ℚ K'`) supplied by
`letI`; the plain form uses whatever `Algebra ℚ K'` and `IsSepClosure ℚ K'` are in scope.  The two
are the same proposition: any two `ℚ`-algebra structures on a commutative ring have the same
`algebraMap` (there is a unique ring homomorphism `ℚ →+* K'`) and the same `smul`
(`r • x = algebraMap ℚ K' r * x`), and the remaining fields of the structures are propositions, so
the instances are equal by `Subsingleton.elim`; the `IsSepClosure`/`IsGalois` instances are
propositions and hence proof-irrelevant. -/
theorem resRankInputGen_congr (K K' : Type*) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Algebra ℚ K'] [IsSepClosure ℚ K'] (ℓ : ℕ)
    [Fact ℓ.Prime] :
    NK.Reconstruct.ResRankInputGen K' ℓ ↔
      ResRankInputGenDerived K K' ℓ := by
  unfold ResRankInputGenDerived
  constructor <;> intro h <;> convert h using 2 <;> exact Subsingleton.elim _ _

end NK.ReconstructEndgame
