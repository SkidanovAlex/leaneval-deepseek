import Mathlib
import Submission.Work.CORE3.D23.Core23A
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.J4U3V18Aux.KCentralizesFittingU
import Submission.Work.CORE3.SevenFittingActionInvariance

namespace Work.CORE3.D23

/-- **L1 of GW design pass 23 §A** (Bender 1981, p. 223, the parenthetical "`[Ĥ,s]` centralizes
`F(U)`"), in the unfolded form of `Work.CORE3.D23.InvolActionUniformProp`: two involutions
`r₁, r₂` of `Ĥ ∖ O₂(Ĥ)` act identically on `F(U) = fittingIn B.U`.

Route.  `D.inv` gives `I_{F(U)}(r) = K` (`K ≤ F(U)` by `D.hall.1`); Bender 1.5(ii) (`I.T.c15`,
applied to the `2'`-group `F(U)`) gives `|C_{F(U)}(r)| = |F(U) : K| =: n`, and `n` is coprime to
`|K|` (`D.hall.2`); `K` is central in `F(U)` (`Work.CORE3.J4U3V18Aux.KCentralizesFittingU`);
hence `F(U) = K × C_{F(U)}(r)` with `C_{F(U)}(r) = {f ∈ F(U) | f ^ n = 1}`, which does not depend
on `r`; writing `f = k * c`, the action is `r * f * r⁻¹ = k⁻¹ * c` for either `r`.

**Status.**  As written this is *literally* the theorem
`Work.CORE3.SevenFittingActionInvariance` already proved in this workspace (`Submission/Work/
CORE3/SevenFittingActionInvariance.lean`): same types, same hypothesis list `Case1Inputs`,
`BenderCtx`, `BenderSetup`, `Case1 B`, `Case1bData B`, two involutions of `Ĥ ∖ O₂(Ĥ)`, same
conclusion `s * x * s⁻¹ = s' * x * s'⁻¹` on `F(U) = fittingIn B.U`.  So the proof below is the
citation of that result, which is itself built on the sorry-free in-tree ingredients named in
the route above (`Case1bData.inv`, `I.T.c15`, `KCentralizesFittingU`); the only axioms it rests
on are `propext`, `Classical.choice`, `Quot.sound`.  (The route quoted above is the
`F(U) = K × C_{F(U)}(r)`-decomposition proof; `SevenFittingActionInvariance` instead goes
through the per-prime Hall dichotomy `O_q(U) ≤ K` or `O_q(U) ⊓ K = ⊥`, which gives the same
statement.) -/
theorem InvolActionUniform (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (r₁ r₂ : G)
    (hr₁H : r₁ ∈ B.Hhat) (hr₁2 : orderOf r₁ = 2) (hr₁V : r₁ ∉ Work.GW2.pCoreIn 2 B.Hhat)
    (hr₂H : r₂ ∈ B.Hhat) (hr₂2 : orderOf r₂ = 2) (hr₂V : r₂ ∉ Work.GW2.pCoreIn 2 B.Hhat)
    (f : G) (hf : f ∈ Work.GW2.fittingIn B.U) :
    r₁ * f * r₁⁻¹ = r₂ * f * r₂⁻¹ :=
  Work.CORE3.SevenFittingActionInvariance G I h B h1 D
    hr₁H hr₁2 hr₁V hr₂H hr₂2 hr₂V f hf

/-- The bundled `Prop` form of the same statement, i.e. exactly the hypothesis
`hL1 : InvolActionUniformProp` that the consumer `Work.CORE3.D23.J4U3V18s` expects. -/
theorem involActionUniformProp : InvolActionUniformProp :=
  fun G _ _ I h B h1 D r₁ r₂ hr₁H hr₁2 hr₁V hr₂H hr₂2 hr₂V f hf =>
    InvolActionUniform G I h B h1 D r₁ r₂ hr₁H hr₁2 hr₁V hr₂H hr₂2 hr₂V f hf

end Work.CORE3.D23
