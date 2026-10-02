import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.LerayHirsch.Chapter
import Submission.Work.Kunneth.kunnethCoh_value
import Submission.Work.Kunneth.zeta_qTriv
import Submission.Work.Kunneth.lerayHirschFull_trivial_assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

/-- **Leray–Hirsch for the trivial bundle over an arbitrary base**, i.e. the Künneth base case
`Work.LerayHirsch.KunnethCP` in its trivial-bundle form: for `Z = ε^m` over `B`,
`H^*(P(Z)) = H^*(B × ℂP^{m-1})` is free over `H^*(B)` on `1, ζ, …, ζ^{m-1}`, i.e. the maps
`(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` (`lhMap`, `lhMapOdd`) are bijective in every degree.

The proof is the assembly `Work.Kunneth.lerayHirschFull_trivial_assembly`, fed with

* `Work.Kunneth.kunnethCoh_value` — the cohomological Künneth theorem with its cross-product value
  rule (so that `H^*(B × P(ε^m over pt))` is `∏_{p+q} H^p(B) ⊗ H^q(P(ε^m over pt))` along
  `π₁^*(−) ⌣ π₂^*(−)`, `Submission/Work/Kunneth/CohKunneth/`),
* `Work.Kunneth.zeta_qTriv` — the geometric bridge
  `qTriv^*(ζ(ε^m over pt)) = ζ(ε^m over B)` for the "class of the fibre coordinate"
  `qTriv : P(ε^m over B) → P(ε^m over pt)` (`Submission/Work/Kunneth/zetaBridgeDefs.lean`),

together with the point case `Work.Kunneth.lerayHirschFull_point` (the ζ-powers generate
`H^*(ℂP^{m-1})`), used inside the assembly. -/
theorem lerayHirschFull_trivial (m : ℕ) (B : Type) [TopologicalSpace B] [Nonempty B] :
    Work.LerayHirsch.LerayHirschFull
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) :=
  lerayHirschFull_trivial_assembly kunnethCoh_value zeta_qTriv m B

end Work.Kunneth
