/-
# The chart pieces of the cusp development

Vocabulary for the proof of the openness of the cusp chart (`mbarLow_open`, `mbarLow_openTop`):
the *pieces* covering the preimage of the chart image.

For a cusp `v`, a cube `a : Fin 48` of that cusp, a lattice offset `k : Fin 3 → ℤ` and an open set
`B ⊆ E4` of source coordinates (the "box" of the chart, e.g. `cuspChartBox v c δ` or
`cuspBoxTop v c δ`), the *piece* is

  `piece v a k B = {x : ZMod 2 × Q̄ | x.1 = cubeBit a ∧ ∃ q ∈ pieceSrc v a k B,
       x.2.1 = cellPt v a k q}`,

where `cellPt v a k q = chartKlein a (mkE4 (uhsXj q - lamV v k) (q 3))` is the chart of the cube `a`
at the *unfolded* coordinate `uhsXj q - lamV v k`, and `pieceSrc v a k B` is `B` together with the
one-unit thickening of the closed cube `cubeBox a` around that coordinate.

Every source point of `B` lies in the piece of its canonical cell (`cubeOf v (uhsXj q)`); the pieces
are open in `X̄` (`chartKlein_image_open`), they are contained in the preimage of the chart image
(by induction on the coordinates at the *upper* walls of the cube), and their union contains that
preimage (by induction on the coordinates at the *lower* walls, so that the class of a value is
covered by the pieces of the repeatedly reflected cells).
-/
import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.FoldInst.Quotient
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-- The **unfolded chart** of the cell `(a,k)`. -/
def cellPt (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4) : CuspE4 :=
  chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))

/-- The **source set of the piece** of the cell `(a,k)`: the points of `B` whose unfolded
coordinate lies in the one-unit thickening of the closed cube `cubeBox a`. -/
def pieceSrc (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (B : Set CuspE4) : Set CuspE4 :=
  {q | q ∈ B ∧ ∀ j : Fin 3,
      (Cusp.cubeCorner a j : ℝ) - 1 ≤ (uhsXj q - cuspCert.lamV v k) j
    ∧ (uhsXj q - cuspCert.lamV v k) j ≤ (Cusp.cubeCorner a j : ℝ) + 2}

/-- The **piece** of the chart cover. -/
def piece (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (B : Set CuspE4) : Set CuspXbar :=
  {x | x.1 = cubeBit a ∧ ∃ q, q ∈ pieceSrc v a k B ∧ x.2.1 = cellPt v a k q}

/-- The **region of the chart**: the points of `B` at or below the ceiling. -/
def chartRegion (B : Set CuspE4) : Set CuspE4 :=
  B ∩ {q : CuspE4 | q 3 ≤ Cusp.beta (xOf4 q)}

/-- The **preimage of the image of the region** in `X̄`. -/
def regionPre (v : Fin 5) (B : Set CuspE4) : Set CuspXbar :=
  FoldInst.mk ⁻¹' (mbarLow v '' chartRegion B)

theorem regionPre_eq (v : Fin 5) (B : Set CuspE4) :
    regionPre v B = {y : CuspXbar | ∃ q ∈ chartRegion B, FoldInst.rel (cuspLowPt v q) y} := by
  ext y
  constructor
  · intro hy
    obtain ⟨q, hq, hqy⟩ := hy
    exact ⟨q, hq, Quotient.exact hqy⟩
  · rintro ⟨q, hq, hrel⟩
    exact ⟨q, hq, Quotient.sound hrel⟩

end Work.RTOwed
