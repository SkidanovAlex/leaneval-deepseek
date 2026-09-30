/-
# Auxiliary facts about the source of the polar chart on `M̂`

`polarBoxSect v c k W` (`Work.Cusp.Assembly`) is the source of the `(c,k)`-th polar chart of the
`v`-th filling piece inside `M̂`: the polar box, a local section `W` of the cover `ℝ² → (ℝ/ℤ)²`
in the `w`-coordinates, the radial bound `r < r_J`, and the angle pinning of the `(c,k)`-th wedge.

This file collects the "book-keeping" facts about it that the chart construction needs:

* `polarBoxSect_eq_polarTargetS`: with
  `polarBoxSectBase v W = {q ∈ polarBox | w(q) ∈ W ∧ q 0 < r_J}`, the source is exactly the
  *target* of the `(c,k)`-th shifted polar chart with box `B = polarBoxSectBase v W`;
* `isOpen_polarBoxSect`, `isOpen_polarBoxSectBase`: both sets are open;
* `nrm_cuspInvInner_lt_one_polarBoxSect`: the layer parameter of `cuspInvInner v q` is `< 1`, i.e.
  the inverse chart lands in the *interior* of the filling piece for `q` in the source.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner

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

/-- The box `B` of the `(c,k)`-th polar chart whose target is `polarBoxSect v c k W`: the polar
box, the section `W` in the `w`-coordinates, and the radial bound `r < r_J`. -/
def polarBoxSectBase (v : Fin 5) (W : Set E2) : Set E4 :=
  {q | q ∈ polarBox ∧ (!₂[q 2, q 3] : E2) ∈ W ∧ q 0 < rJ}

/-- The `w`-coordinates of a point of `E4`. -/
def wCoord (q : E4) : E2 := !₂[q 2, q 3]

theorem wCoord_apply (q : E4) : wCoord q = !₂[q 2, q 3] := rfl

theorem continuous_wCoord : Continuous wCoord := by
  unfold wCoord; fun_prop

/-- `polarBoxSectBase v W` is open for open `W`: the conditions are `q ∈ polarBox`,
`w(q) ∈ W` (preimage of the open `W` under the continuous `wCoord`) and `q 0 < r_J`. -/
theorem isOpen_polarBoxSectBase (v : Fin 5) (W : Set E2) (hW : IsOpen W) :
    IsOpen (polarBoxSectBase v W) := by
  have h1 : IsOpen {q : E4 | wCoord q ∈ W} := hW.preimage continuous_wCoord
  have h2 : IsOpen {q : E4 | q 0 < rJ} :=
    isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0) continuous_const
  have h : polarBoxSectBase v W
      = polarBox ∩ {q : E4 | wCoord q ∈ W} ∩ {q : E4 | q 0 < rJ} := by
    ext q
    simp only [polarBoxSectBase, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_setOf_eq,
      wCoord_apply]
    tauto
  rw [h]
  exact (isOpen_polarBox.inter h1).inter h2

/-- **The source of the `(c,k)`-th polar chart is the target of the shifted polar chart with box
`polarBoxSectBase v W`** (the two sets have literally the same defining conditions, in a different
association). -/
theorem polarBoxSect_eq_polarTargetS (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2) :
    polarBoxSect v c k W = polarTargetS v c k (polarBoxSectBase v W) := by
  ext q
  simp only [polarBoxSect, polarTargetS, polarBoxSectBase, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  tauto

/-- **The source of the `(c,k)`-th polar chart is open.** -/
theorem isOpen_polarBoxSect (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2) (hW : IsOpen W) :
    IsOpen (polarBoxSect v c k W) := by
  rw [polarBoxSect_eq_polarTargetS]
  exact isOpen_polarTargetS v c k _ (isOpen_polarBoxSectBase v W hW)

/-- **The inverse polar chart lands in the interior of the filling piece on the source**: for
`q ∈ polarBoxSect v c k W` the layer parameter `nrm (cuspInvInner v q).1 = q 0 / (2 r_J)` is
`< 1/2 < 1` because `q 0 < r_J`. -/
theorem nrm_cuspInvInner_lt_one_polarBoxSect (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2)
    (q : E4) (hq : q ∈ polarBoxSect v c k W) : nrm (cuspInvInner v q).1 < 1 := by
  have hq0 : q 0 < rJ := hq.2.2.1
  have hq0pos : 0 < q 0 := by have h := hq.1.1; linarith
  have h2rJ : (0 : ℝ) < 2 * rJ := by rw [rJ]; norm_num
  have hle : q 0 ≤ rJ := le_of_lt hq0
  show nrm (cuspInvInner v q).1 < 1
  simp only [cuspInvInner]
  rw [if_pos hle, nrm_smul_bndOfU (by positivity) _]
  rw [div_lt_one h2rJ]
  have hrJ : (2 : ℝ) * rJ = 6 := by norm_num [rJ]
  linarith

end Work.Cusp
