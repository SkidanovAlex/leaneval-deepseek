import Mathlib
import Submission.Work.Gen.eSymClass
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.TautTwist
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The vocabulary of the Chern-root relation of a direct sum

For a complex bundle `W` of rank `m` over `B` and the projectivisation `P(W)` with tautological line
`ℓ = Work.LerayHirsch.tautLine W`, the proof of the Chern-root relation

  `∏_i (π^*c₁(M i) - ζ) = 0`   in `H^{2n}(P(W))`, `W = lineSumCore n M`,

runs through the twist `ℓ^* ⊗ π^*W` of `Work.Gen.chernRoot_twistTop`: it vanishes in top degree
(`Work.Gen.chernRoot_twistTop`), and it splits as the sum of the `n` line bundles
`ℓ^* ⊗ π^*M i`, whose top Chern class is the product of the first Chern classes.

This module fixes the two abbreviations of that argument:

* `Work.Gen.twistTaut W L = ℓ^* ⊗ π^*L` — one summand of the twisted sum, a line bundle over `P(W)`;
* `Work.Gen.twistTautTop W = ℓ^* ⊗ π^*W` — the whole twist, of rank `m`.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- **One summand of the twisted sum**: for a complex bundle `W` of rank `m` over `B`, the line
bundle `ℓ^* ⊗ π^*L` over `P(W)`, where `ℓ = tautLine W` is the tautological line bundle and
`π = projMap W`. -/
abbrev twistTaut {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {ιL : Type} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL) :
    VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace W) (EuclideanSpace ℂ (Fin 1))
      ((ι × Fin m) × ιL) :=
  Work.LerayHirsch.twistCore (Work.Gen.dualLineCore (Work.LerayHirsch.tautLine W))
    (Work.Thom.bundleComap L (Work.LerayHirsch.projMap W))

/-- **The twisted sum** `ℓ^* ⊗ π^*W` over `P(W)`, of rank `m`.  For `m = m' + 1` this is
`Work.LerayHirsch.tautTwist W`, the bundle whose top Chern class vanishes
(`Work.Gen.chernRoot_twistTop`). -/
abbrev twistTautTop {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace W) (EuclideanSpace ℂ (Fin m))
      ((ι × Fin m) × ι) :=
  Work.LerayHirsch.twistCore (Work.Gen.dualLineCore (Work.LerayHirsch.tautLine W))
    (Work.Thom.bundleComap W (Work.LerayHirsch.projMap W))

/-- `Work.Gen.twistTautTop` is the twist `Work.LerayHirsch.tautTwist`. -/
theorem twistTautTop_eq_tautTwist {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    twistTautTop W = Work.LerayHirsch.tautTwist W := rfl

end

end Work.Gen
