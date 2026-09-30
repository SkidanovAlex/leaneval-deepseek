/-
# The unslabbed collar box `cuspBoxTop` is open

`cuspBoxTop v c δ` is the box of side `2δ` around `c` in the UHS coordinate `x`, with height in the
window `(s₁, sTop)`, and *no* condition on the meridian coordinate `outerU v x`:

`cuspBoxTop v c δ = {q | (∀ i, |xOf q i − c i| < δ) ∧ s₁ < q 3 ∧ q 3 < sTop}`.

Every condition is a *strict* inequality between continuous functions of `q`: the coordinates
`q ↦ q i` of `E4 = ℝ⁴` are continuous (`continuous_coord4_cbi`), and `xOf` (`(x,s) ↦ x`) is
continuous (`continuous_xOf_cbi`), so each coordinate `q ↦ xOf q i` is (`continuous_xOf_apply_cbi`).
Hence the box is a finite intersection of preimages of open intervals, i.e. open.  This is the same
computation as `isOpen_cuspBoxInterior` and `isOpen_cuspChartBox`, with the slab and ceiling
conditions dropped and the upper height `sJ` replaced by `sTop`.
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.isOpen_cuspChartBox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology
open scoped Real InnerProductSpace

namespace Work.Cusp

theorem isOpen_cuspBoxTop (v : Fin 5) (c : E3) (δ : ℝ) : IsOpen (cuspBoxTop v c δ) := by
  -- The three horizontal coordinate conditions, as a finite intersection.
  have hbox : IsOpen {q : E4 | ∀ i, |xOf q i - c i| < δ} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt ((continuous_xOf_apply_cbi i).sub continuous_const).abs continuous_const
  -- The two height conditions.
  have h1 : IsOpen {q : E4 | s1 < q 3} :=
    isOpen_lt continuous_const (continuous_coord4_cbi 3)
  have h2 : IsOpen {q : E4 | q 3 < sTop} :=
    isOpen_lt (continuous_coord4_cbi 3) continuous_const
  have hdecomp : cuspBoxTop v c δ
      = {q : E4 | (∀ i, |xOf q i - c i| < δ)} ∩ {q : E4 | s1 < q 3}
        ∩ {q : E4 | q 3 < sTop} := by
    ext q
    simp only [cuspBoxTop, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hdecomp]
  exact (hbox.inter h1).inter h2

end Work.Cusp
