import Mathlib
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Serre.CellStep.Defs
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.discPairIso
import Submission.Work.Serre.CellStep.ModelReduction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.CellStep

/-- **The per-cell model statement.**  For a Serre fibration `p : E → B`, a map `τ : D^{n+2} → B`
whose fibres over the image of `τ` are homologically `φ`-connected, the map of pairs
`(τ^*E, τ^*E|_{csSh}) → (csB, csSh)` — i.e. `Work.Serre.csModelMap n p τ` — is an isomorphism on
integral homology in degrees `< (n+2) + φ`.

This is the content of `Work.Serre.CellStep.csModelIso_of_discIso` (a chain of transfers reducing
the model pair to the disc pair `(D^{n+2}, S^{n+1})`) combined with the disc statement
`Work.Serre.CellStep.discPairIso`. -/
theorem csModelIso (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.RatHurewicz.cellDisk n, B)) (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.cellDisk n, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.cellDisk n,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre p (τ y)))
        (ModuleCat.of ℤ ℤ)))
    (i : ℕ) (hi : i < (n + 2) + φ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.csModelMap n p τ) i) :=
  csModelIso_of_discIso p hp τ i (discPairIso n p hp τ φ hfib h0 i hi)

end Work.Serre.CellStep
