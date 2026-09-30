/-
# The open source of the collar chart is open

The target of the collar cusp chart of the `v`-th cusp (`Work.Cusp.Charts.cuspBoxInterior`) is the
part of the open box `cuspBox v c δ` which lies strictly above the ceiling `s = β(x)` and strictly
inside the slab `0 < outerU v x < 1` of the `σ_v`-direction:

`cuspBoxInterior v c δ = {q | (∀ i, |xOf q i − c i| < δ) ∧ s₁ < q 3 ∧ q 3 < s_J
                              ∧ 0 < outerU v (xOf q) ∧ outerU v (xOf q) < 1 ∧ β (xOf q) < q 3}`.

Every condition is a *strict* inequality between continuous functions of `q`: the coordinates
`q ↦ q i` of `E4 = ℝ⁴` are continuous, `xOf` (`(x,s) ↦ x`) is continuous, and so are `outerU v`
(a fixed linear functional of `x`, `outerU_continuous`) and the ceiling `β` (`beta_continuous`,
continuous in spite of `Int.fract` because the triangle wave `off` is).  Hence the box interior is
a finite intersection of preimages of open intervals, i.e. open.

(For the `∀ i` part note `Fin 3` is finite, so the intersection over the three coordinates is
finite.)
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.outerU_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.Cusp

/-- Coordinates of `E4 = ℝ⁴` are continuous. -/
theorem continuous_coord4_cbi (i : Fin 4) : Continuous (fun q : E4 => q i) :=
  PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i

/-- The horizontal part `xOf q` is a continuous map `E4 → E3`. -/
theorem continuous_xOf_cbi : Continuous (fun q : E4 => xOf q) := by
  unfold xOf
  fun_prop

/-- Each coordinate of the horizontal part `xOf q` is continuous. -/
theorem continuous_xOf_apply_cbi (i : Fin 3) : Continuous (fun q : E4 => xOf q i) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp continuous_xOf_cbi

/-- **The requested statement: the open source of the collar chart is open.** -/
theorem isOpen_cuspBoxInterior (v : Fin 5) (c : E3) (δ : ℝ) :
    IsOpen (cuspBoxInterior v c δ) := by
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
  -- The perimeter-slab and ceiling conditions.
  have hU : Continuous fun q : E4 => outerU v (xOf q) :=
    (outerU_continuous v).comp continuous_xOf_cbi
  have hb : Continuous fun q : E4 => beta (xOf q) :=
    beta_continuous.comp continuous_xOf_cbi
  have h4 : IsOpen {q : E4 | 0 < outerU v (xOf q)} := isOpen_lt continuous_const hU
  have h5 : IsOpen {q : E4 | outerU v (xOf q) < 1} := isOpen_lt hU continuous_const
  have h6 : IsOpen {q : E4 | beta (xOf q) < q 3} :=
    isOpen_lt hb (continuous_coord4_cbi 3)
  have hdecomp : cuspBoxInterior v c δ
      = {q : E4 | (∀ i, |xOf q i - c i| < δ)} ∩ {q : E4 | s1 < q 3} ∩ {q : E4 | q 3 < sJ}
        ∩ {q : E4 | 0 < outerU v (xOf q)} ∩ {q : E4 | outerU v (xOf q) < 1}
        ∩ {q : E4 | beta (xOf q) < q 3} := by
    ext q
    simp only [cuspBoxInterior, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hdecomp]
  exact ((((hbox.inter h1).inter h2).inter h4).inter h5).inter h6

end Work.Cusp
