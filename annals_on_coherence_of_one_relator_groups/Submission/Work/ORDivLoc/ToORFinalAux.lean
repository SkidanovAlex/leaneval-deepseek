/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The type of node N6's input, and the identification with `Work.ORFinal`

`Work.ORDivLoc.N6EngineInput` is the (long) type of the input taken from the JZLA20 engine: the
construction `Work.ORHughesFree.Section6.thm61Step_nonempty` over `ℂ`, for every group `G₀`, every
positive definite `∗`-regular ring `U` with a faithful Sylvester rank function, and every epic
`∗`-compatible `φ : ℂ[G₀] →+* U` satisfying `IsHughesFreeEnv φ`.  It is named here so that the
statements of `Final.lean` and `ToORFinal.lean` are readable.  This file also records the
identification of `Work.ORDivLoc.DivLoc`/`DivOn` with the definitions of `Work.ORFinal`.
-/
import Submission.Work.ORDivLoc.Final
import Submission.Work.ORFinal.AnalyticInput

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORDivLoc

/-- **Node N6's input**: the construction of the induction environment `Thm61Step` over `ℂ` (this
is `Work.ORHughesFree.Section6.thm61Step_nonempty`).  Note that `U` is an arbitrary positive
definite `∗`-regular ring with a faithful rank function, `G₀` an arbitrary group, and `φ` a
`∗`-compatible epic ring homomorphism with `IsHughesFreeEnv φ` ([JZLA20, Proposition 3.11]). -/
def N6EngineInput : Prop :=
  ∀ {G₀ : Type} [Group G₀] [Work.ORHughesFree.LocallyIndicable G₀] {U : Type} [Ring U]
    [StarRing U] [Work.ORHughesFree.IsStarRegular U],
    Work.ORHughesFree.IsPositiveDefiniteStarRegular U →
    ∀ (φ : MonoidAlgebra ℂ G₀ →+* U) (rkU : Work.ORHughesFree.SylvesterRank U),
      rkU.IsFaithful →
    Work.ORHughesFree.IsEpic φ → Work.ORHughesFree.StarCompatible φ →
    Work.ORHughesFree.IsHughesFreeEnv φ →
    ∀ H₀ : Subgroup G₀, H₀.FG → H₀ ≠ ⊥ →
      Nonempty (Work.ORHughesFree.Thm61Step ℂ G₀ U φ H₀)

end Work.ORDivLoc
