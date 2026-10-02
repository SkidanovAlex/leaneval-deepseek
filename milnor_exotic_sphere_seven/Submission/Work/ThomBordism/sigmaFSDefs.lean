import Mathlib
import Submission.Work.ThomBordism.sigmaExplicit
import Submission.Work.ThomBordism.OrthFrame.Cocycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the **frame-sign** (canonical) sign cocycle `sigmaFS`

`Work.ThomBordism.Gauss.sigma` is defined (`gaussDefs.lean`) as

  `sigma E ND i x = (Classical.choose (framePairSign_cocycle E ND)) i.1 x * framePairSign E ND i x`

whose first factor `ρ := Classical.choose (framePairSign_cocycle E ND)` is an **opaque** witness of
the tangent-frame sign cocycle: its specification (`= ±1`, continuous on the chart sources, product
the sign of the transition Jacobian) is invariant under `ρ ↦ -ρ`, so `Gauss.sigma`, `Gauss.gauge`,
`Gauss.gframe`, `Gauss.padGaussFunM` and hence the *coorientation of every level set of the source
construction* carry an uncontrolled global sign (session 33's `sigmaUpToLocalSign`).  The *explicit*
witness used inside the proof of `framePairSign_cocycle` is `FrameSigns.frameSign V`, the sign of the
chart frame against the **given** fundamental class `V.c`
(`FrameSigns/frameSign_eq_of_isCoordBall.lean`, `Charts.lean`).

This file names the corresponding explicit cocycle `sigmaFS` and its corrected normal frame
`gframeFS`, so that the (provable, non-opaque) statements about the *canonical* orientation can be
stated.  The two non-formal ingredients — the cocycle clause
`(frameSign · fps)_i · (frameSign · fps)_j = sign (det frameChange)` and the telescoping
`pairSign (flipTan (frameSign)) gframeFS = 1` — are delegated separately (they are the whole content;
everything else below is the definition and its unfolding).

## Main definitions

* `Work.ThomBordism.sigmaFS` — the explicit sign cocycle `frameSign V i.1 x * framePairSign E ND i x`
  on `ND.D.baseSet i` (and `1` outside);
* `Work.ThomBordism.gframeFS` — the corrected normal frame `Hmat (sigmaFS) · orthFrame`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.ThomBordism.Grassmann
open Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The explicit (canonical) sign cocycle**: `frameSign V i.1 x · framePairSign E ND i x` on the
base set of the chart `i`, and the junk value `1` outside.  Its first factor is the sign of the
*chart tangent frame* against the given fundamental class `V.c` (`FrameSigns.frameSign`), i.e. the
explicit witness used inside the proof of `Work.ThomBordism.framePairSign_cocycle` — as opposed to the
opaque `Classical.choose` of that theorem that `Gauss.sigma` uses. -/
def sigmaFS (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    CoverIdx V k → V.pt → ℝ :=
  fun i x => by
    classical
    exact if _ : x ∈ ND.D.baseSet i then
      FrameSigns.frameSign V i.1 x * framePairSign E ND i x
    else 1

/-- The defining formula of `sigmaFS` on a base set. -/
theorem sigmaFS_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    sigmaFS E ND i x = FrameSigns.frameSign V i.1 x * framePairSign E ND i x := by
  rw [sigmaFS, dif_pos hx]

/-- **The corrected normal frame of the canonical cocycle**: `Hmat (sigmaFS) · orthFrame`. -/
def gframeFS (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : Fin k → Work.Tubular.Euc (8 + k) :=
  Gauss.frameAct (Gauss.Hmat (sigmaFS E ND i x)) (Work.Tubular.orthFrame E ND i x)

/-- The defining relation of `gframeFS`. -/
theorem gframeFS_rel (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) :
    ∀ b, gframeFS E ND i x b
      = ∑ b', Gauss.Hmat (sigmaFS E ND i x) b' b • Work.Tubular.orthFrame E ND i x b' :=
  fun b => rfl

end

end Work.ThomBordism
