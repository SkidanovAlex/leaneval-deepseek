import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.HassePrinciple.Norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The licensed cyclic input**: the Hasse norm theorem for cyclic extensions of number fields
(in the index form of the reciprocity isomorphism and in the norm form), together with the Herbrand
quotient of the idèle class group for cyclic extensions.

Both fields are statements about *cyclic* extensions of number fields and their norm groups; they
are the two classical inputs of the Hasse–Brauer–Noether theorem, and this chapter derives the
Hasse principle from them. -/
structure CyclicHasseInput : Prop where
  /-- **The Hasse norm theorem for cyclic extensions of number fields** (`Norm.lean`): the index
  formula `[C_K : N_{L/K} C_L] = [L : K]` and the local–global principle for norms
  `Kˣ ∩ N 𝕀_L = N Lˣ`. -/
  hasse_norm : HasseNormTheorem.{0}
  /-- **The Herbrand quotient of the idèle class group for cyclic extensions**:
  `h(Gal(L/K), C_L) = [L : K]` (Milne, *CFT*, Thm 4.3). -/
  herbrand : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L], IsCyclic (L ≃ₐ[K] L) → HerbrandQuotient K L

end NK.HassePrinciple
