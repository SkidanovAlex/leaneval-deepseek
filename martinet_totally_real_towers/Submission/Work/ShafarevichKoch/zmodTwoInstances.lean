import Mathlib
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ConCohomology.All

/-!
# `Work.ShafarevichKoch.zmodTwoInstances` -- the (trivial) action on `𝔽₂` as an instance

The sibling chapter `Submission/Work/RelatorRank/CohomologyH2.lean` provides the *trivial*
`Γ`-action on `𝔽₂ = ℤ/2` as a `def` (`Work.RelatorRank.f2TrivialAction Γ`), so that every statement
about `H²(Γ, 𝔽₂)` has to carry a `letI`/`letI`-binder.  Since `Aut(ℤ/2) = 1`, **every**
`DistribMulAction` of a group on `ℤ/2` is trivial (`Work.ShafarevichKoch.smul_zmodTwo_eq`), so
making this action an *instance* is harmless; we do it here (locally, in this directory: instances
are scoped by imports, so no other chapter of the workspace is affected) so that the statements of
`README.md` §33.5 -- the inflation/colimit machinery for `H²_cont(Γ, 𝔽₂)` -- can be written without
explicit instance binders.
-/

set_option linter.unusedVariables false

namespace Work.ShafarevichKoch

/-- The trivial action of a group on `𝔽₂` as an instance. -/
instance instDistribMulActionZModTwo (Γ : Type*) [Group Γ] : DistribMulAction Γ (ZMod 2) :=
  Work.RelatorRank.f2TrivialAction Γ

/-- With the trivial (instance) action, `𝔽₂` is a discrete `Γ`-module in the sense of continuous
cohomology. -/
instance instIsDiscreteGModuleZModTwo (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    Work.ConCohomology.IsDiscreteGModule Γ (ZMod 2) :=
  Work.RelatorRank.f2Discrete Γ

/-- The compatibility of the (trivial) actions on `𝔽₂` along any group homomorphism: this is the
`hcomp` hypothesis of the inflation `Work.ShafarevichKoch.H2Infl`. -/
theorem zmodTwo_compatible (Γ : Type*) [Group Γ] (σ : Γ) (m : ZMod 2) :
    σ • m = σ • m := rfl

end Work.ShafarevichKoch
