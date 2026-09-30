/-
# The open chart box of the collar chart is open

`cuspChartBox v c δ` is the target of the collar chart of the `v`-th cusp: the box of side `2δ` in
`x`, heights in `(s₁, s_J)` and the *strict* slab `0 < outerU v x < 1` of the `σ_v`-direction:

`cuspChartBox v c δ = {q | (∀ i, |xOf q i − c i| < δ) ∧ s₁ < q 3 ∧ q 3 < s_J
                           ∧ 0 < outerU v (xOf q) ∧ outerU v (xOf q) < 1}`.

Every condition is a *strict* inequality between continuous functions of `q`: the coordinates
`q ↦ q i` of `E4 = ℝ⁴` are continuous, `xOf` (`(x,s) ↦ x`) is continuous, and so is `outerU v`
(a fixed linear functional of `x`, `outerU_continuous`).  Hence the box is a finite intersection of
preimages of open intervals, i.e. open.  This is the same computation as
`isOpen_cuspBoxInterior`, with the ceiling condition dropped.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.outerU_continuous
import Submission.Work.Cusp.isOpen_cuspBoxInterior

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.Cusp

theorem isOpen_cuspChartBox (v : Fin 5) (c : E3) (δ : ℝ) : IsOpen (cuspChartBox v c δ) := by
  -- The three horizontal coordinate conditions, as a finite intersection.
  have hbox : IsOpen {q : E4 | ∀ i, |xOf q i - c i| < δ} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt ((continuous_xOf_apply_cbi i).sub continuous_const).abs continuous_const
  -- The height conditions.
  have h1 : IsOpen {q : E4 | s1 < q 3} :=
    isOpen_lt continuous_const (continuous_coord4_cbi 3)
  have h2 : IsOpen {q : E4 | q 3 < sJ} :=
    isOpen_lt (continuous_coord4_cbi 3) continuous_const
  -- The perimeter-slab conditions.
  have hU : Continuous fun q : E4 => outerU v (xOf q) :=
    (outerU_continuous v).comp continuous_xOf_cbi
  have h4 : IsOpen {q : E4 | 0 < outerU v (xOf q)} := isOpen_lt continuous_const hU
  have h5 : IsOpen {q : E4 | outerU v (xOf q) < 1} := isOpen_lt hU continuous_const
  have hdecomp : cuspChartBox v c δ
      = {q : E4 | (∀ i, |xOf q i - c i| < δ)} ∩ {q : E4 | s1 < q 3} ∩ {q : E4 | q 3 < sJ}
        ∩ {q : E4 | 0 < outerU v (xOf q)} ∩ {q : E4 | outerU v (xOf q) < 1} := by
    ext q
    simp only [cuspChartBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hdecomp]
  exact (((hbox.inter h1).inter h2).inter h4).inter h5

end Work.Cusp
