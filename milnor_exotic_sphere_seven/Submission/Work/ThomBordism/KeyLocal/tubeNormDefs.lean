import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.gtdGaussCandidate

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The objects of the tube-level normal reading

The last mile compares the restriction of the canonical class to the part of the tube over a chart
of the normal datum with the pullback of `stdModelGen k` along the coordinate reading of the normal
vector.  This file supplies the two objects of that comparison:

* `padComplChart` — the chart of the normal oriented Grassmannian `G̃r_k(ℝ^{k+10})` "dual" to the
  tangential chart index `i = (i₀, S₀)`: the coordinates complementary to `S₀` (embedded into the
  padded ambient `ℝ^{k+10}`).  On the part of the tube lying over `ND.D.baseSet i` the Gauss plane
  is transverse to the complementary coordinates of `S₀`, so this is a *single* chart containing the
  whole family of Gauss planes (see `frameMatrix_padComplChart_padGFrame_det_ne_zero`).
* `tubeFrame` — the Stiefel point of the σ-corrected frame `padGFrame` of the datum chart `i` at the
  foot of a point of the tube base set.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

/-- **The chart of the normal Grassmannian dual to the tangential chart index `i`**: the
complementary coordinates `S₀ᶜ` of the tangential chart `i.2`, transported into the padded ambient
`ℝ^{k+10}`. -/
def padComplChart {V : Work.ThomBordism.Man8} {k : ℕ} (i : CoverIdx V k) : ChartIdx k 10 :=
  ⟨i.2.1ᶜ.map ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩, by
    rw [Finset.card_map, chartIdx_compl_card i.2]⟩

/-- **The Stiefel point of the σ-corrected normal frame of the datum chart `i` at the foot of a
point of the tube base set.** -/
def tubeFrame {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) : Stiefel k 10 :=
  ⟨padGFrame E ND i (NormalTotal.proj (C.inv y.1.1)),
    padGFrame_orthonormal E ND i y.2⟩

theorem tubeFrame_val {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    (tubeFrame E C ND i y).1 = padGFrame E ND i (NormalTotal.proj (C.inv y.1.1)) := rfl

/-- The plane of the tube frame is the Gauss plane at the foot. -/
theorem ogMk_tubeFrame {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    ogMk k 10 (tubeFrame E C ND i y) = padGaussFun E ND (NormalTotal.proj (C.inv y.1.1)) := by
  change ogMk k 10 (tubeFrame E C ND i y) = padGaussFun E ND (tubeFoot E C y.1)
  rw [padGaussFun_eq E ND i y.2]
  exact congrArg (ogMk k 10) (Subtype.ext rfl)

end

end Work.ThomBordism.KeyLocal
