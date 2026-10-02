import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.ambientLocalDefs2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The open chart ball and the chart neighbourhood of `0`

Vocabulary for `Work.ThomBordism.localChartClass_ne_zero`.

* `chartOpenBall E ε` — the **open `ε`-disc bundle** of the normal bundle `ν` of the embedding
  `E : V ↪ ℝ^{8+k}`, i.e. the set of points `p` with `‖vec p‖ < ε`.  On it the radial capping is the
  identity and the tubular map is a homeomorphism onto the open tube.
* `chartNbhd E C x` — the **chart neighbourhood of `0`**: the translate by `-E.e x` of the open tube
  of a `TubeChart C`, i.e. `{y | y + E.e x ∈ C.openTube}`.  It is an open neighbourhood of `0`, and
  the capped chart map `p ↦ chartAffine E x (cap E ε p)` restricts to a homeomorphism of pairs
  `(chartOpenBall E ε, chartOpenBall E ε ∖ {0_x}) → (chartNbhd E C x, chartNbhd E C x ∖ {0})`.
-/

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The **open `ε`-disc bundle** of the normal bundle of `E`. -/
def chartOpenBall (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    Set (Work.Tubular.NormalTotal E) :=
  {p | Work.Tubular.normalNorm E p < ε}

@[simp] theorem mem_chartOpenBall (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ε : ℝ) (p : Work.Tubular.NormalTotal E) :
    p ∈ chartOpenBall E ε ↔ Work.Tubular.normalNorm E p < ε := Iff.rfl

/-- The **chart neighbourhood of `0`**: the translate by `-E.e x` of the open tube. -/
def chartNbhd (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) : Set (Work.Tubular.Euc (8 + k)) :=
  {y | y + E.e x ∈ C.openTube}

@[simp] theorem mem_chartNbhd (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) (y : Work.Tubular.Euc (8 + k)) :
    y ∈ chartNbhd E C x ↔ y + E.e x ∈ C.openTube := Iff.rfl

end

end Work.ThomBordism
