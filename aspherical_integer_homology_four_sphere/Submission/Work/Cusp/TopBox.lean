/-
# The *unslabbed* collar chart family: the box and the layer interval

The slabbed collar box `cuspChartBox v c δ` (`Work.Cusp.Assembly`) carries the strict slab
`0 < outerU v x < 1` of the `σ_v`-coordinate and the height window `(s₁, s_J)`.  Both restrictions
are fatal for the cover of the collar of the filling piece:

* the meridian parameter of the lifts of a point of `M̂` on the truncation torus is
  `outerU ≡ u(p) (mod 1)`, where `u(p)` is the perimeter parameter of the filling point, so a point
  with `u(p) = 0` — one of the four *corner* directions `(±1,±1)` of the square — has **no** lift in
  the slab `(0,1)`;
* the junction `‖p‖∞ = 1/2` has UHS height exactly `s_J` (`r = r_J`), which the *open* window
  `(s₁, s_J)` does not contain, while the polar charts are pinned to `r < r_J`.

This file fixes the vocabulary of the family which does cover the collar, exactly as blueprint §1
describes the cusp chart ("an open box of side `< 1` in `x`"):

* `cuspBoxTop v c δ` — the box of side `2δ` in `x` with heights in `(s₁, sTop)` and **no** slab.
  With `δ ≤ 1/2` the box has sup-norm extent `≤ 1`, which is what the injectivity of the collar
  coordinate needs (no two of its points differ by a nonzero lattice vector);
* `cuspSourceTop v c δ` — the part of the box on or above the ceiling `s = β(x)` (the *collar* of
  the filling piece, in cusp coordinates);
* `cuspAnchor v c = outerU v c − 1/2` and the intervals `layerA`, `layerDomI a`, `layerUpDom a` —
  the `(u,t)`-domain of the layer chart.  The `σ`-coordinate of a point of `cuspBoxTop v c δ` lies
  in `(outerU v c − 1/2, outerU v c + 1/2) = layerA (cuspAnchor v c)` (the box moves in the
  `σ`-direction by at most `δ ≤ 1/2`), and the layer parameter `t = ‖(cuspInvOuter v q).1‖∞`
  recovered from a point of the collar source satisfies `layerLo < t ≤ 1` with
  `layerLo = 1/4` (`Work.Cusp.cuspInvOuter_nrm_Top`).

The layer window `(layerLo, 1] = (1/4,1]` is *wider* than the collar stratum `(1/2,1]`: because the
height window reaches above the junction `s_J`, the box also contains points whose recovered layer
parameter is below `1/2` (they are points of the filling piece in the polar region; a chart is of
course allowed to cover more than the layer it is named after).  What matters is that `t` stays
strictly above `layerLo > 0`, which is what makes the layer chart `layerPtI` an open embedding of
`layerDomI a` (its range is `{layerLo < ‖·‖∞ ≤ 1}` minus one ray).

The two numerical properties of `sTop = 33/20` are in `Work.Cusp.TopWindow`.
-/
import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real InnerProductSpace

namespace Work.Cusp

/-! ### The unslabbed collar box and the layer intervals -/

/-- **The (unslabbed) collar chart box of the `v`-th cusp**: the open box of side `2δ` around `c` in
the UHS coordinate `x`, with height in the window `(s₁, sTop)`, and *no* condition on the meridian
coordinate `outerU v x`.  It is the box of blueprint §1 for the collar chart. -/
def cuspBoxTop (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | (∀ i, |xOf q i - c i| < δ) ∧ s1 < q 3 ∧ q 3 < sTop}

/-- **The collar source of the unslabbed collar chart**: the points of the box on or above the
ceiling `s = β(x)`, i.e. the part of the filling piece whose cusp coordinates are the UHS
coordinates of the box. -/
def cuspSourceTop (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | q ∈ cuspBoxTop v c δ ∧ beta (xOf q) ≤ q 3}

/-- **The anchor of the meridian interval** of the collar box `cuspBoxTop v c δ`: the box meets the
interval `(outerU v c − 1/2, outerU v c + 1/2)` of the meridian coordinate, which is
`layerA (cuspAnchor v c)`. -/
def cuspAnchor (v : Fin 5) (c : E3) : ℝ := outerU v c - 1/2

/-- The open interval `(a, a+1)` of the meridian parameter: the domain of the layer chart with
anchor `a`. -/
def layerA (a : ℝ) : Set ℝ := Set.Ioo a (a+1)

/-- **The lower end of the layer window**: `layerLo = 1/4`.  Every point of the collar source
recovers a layer parameter `> layerLo` (`Work.Cusp.cuspInvOuter_nrm_Top`), and `layerLo > 0` is what
makes the layer chart an embedding whose range is open in the square (the range has to stay away from
the core `0`, where the perimeter parameter is discontinuous). -/
def layerLo : ℝ := 1/4

/-- The layer parameter interval `(layerLo, ∞)` of the *up* collar (used to reach the plane-level
chart before restricting to the square). -/
def layerUpJ : Set ℝ := Set.Ioi layerLo

/-- The domain of the plane-level layer chart with anchor `a`: `u ∈ (a,a+1)`, `t ∈ (layerLo,∞)`. -/
def layerUpDom (a : ℝ) : Set (ℝ × ℝ) := layerA a ×ˢ layerUpJ

/-- **The domain of the layer chart with anchor `a`**: meridian parameter `u ∈ (a, a+1)` and layer
parameter `t ∈ (layerLo, 1]`. -/
def layerDomI (a : ℝ) : Set (ℝ × ℝ) := {z | z.1 ∈ layerA a ∧ layerLo < z.2 ∧ z.2 ≤ 1}

/-- The plane-level layer chart with anchor `a`: `(u,t) ↦ t • bndOfU u`, on
`(a,a+1) × (layerLo,∞)`. -/
def layerPtUpA (a : ℝ) (z : {z : ℝ × ℝ // z ∈ layerUpDom a}) : E2 :=
  z.1.2 • bndOfU z.1.1

/-- The layer point `t • bndOfU u` of the plane, for `u ∈ (a,a+1)`, `t ∈ (layerLo,1]`. -/
def layerPtE (a : ℝ) (z : {z : ℝ × ℝ // z ∈ layerDomI a}) : E2 :=
  z.1.2 • bndOfU z.1.1

/-- **The layer chart with anchor `a`**, as a map into the filling square: `(u,t) ↦ t • bndOfU u`.
It is the chart which covers the *corner directions* `u ∈ ℤ` of the collar, and it is an open
embedding (`isOpenEmbedding_layerPtI`). -/
def layerPtI (a : ℝ) (z : {z : ℝ × ℝ // z ∈ layerDomI a}) : Work.Space.SquarePt :=
  ⟨layerPtE a z, by
    obtain ⟨-, h2, h3⟩ := z.2
    have ht : 0 < z.1.2 := lt_trans (by norm_num [layerLo]) h2
    have hn : nrm (layerPtE a z) = z.1.2 := by
      rw [layerPtE, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos ht]
    have hle : nrm (layerPtE a z) ≤ 1 := by rw [hn]; exact h3
    exact ⟨le_trans (abs_le_nrm _ 0) hle, le_trans (abs_le_nrm _ 1) hle⟩⟩

/-- The layer parameter of a layer point is its second coordinate. -/
theorem nrm_layerPtE (a : ℝ) {z : ℝ × ℝ} (hz : z ∈ layerDomI a) :
    nrm (layerPtE a ⟨z, hz⟩) = z.2 := by
  obtain ⟨-, h2, -⟩ := hz
  rw [layerPtE, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos (lt_trans (by norm_num [layerLo]) h2)]

/-- The underlying point of `layerPtI` is `layerPtE`. -/
theorem coe_layerPtI (a : ℝ) (z : {z : ℝ × ℝ // z ∈ layerDomI a}) :
    ((layerPtI a z : Work.Space.SquarePt) : E2) = layerPtE a z := rfl

/-! ### The `(u,y)`-box of the collar source -/

/-- **The box of `(u,y)`-coordinates of the range of the collar coordinate**: the points `(u,y)`
whose reconstructed cusp coordinate `cuspX v u y` lies in the box of side `2δ` around `c`. -/
def cuspTopBox2 (v : Fin 5) (c : E3) (δ : ℝ) : Set (ℝ × E2) :=
  {w | ∀ i, |(cuspX v w.1 w.2) i - c i| < δ}

/-- The `(u,y)`-coordinates of a point of the layer target, forgetting the layer parameter `t`. -/
def cuspTopCoords (a : ℝ) (p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2) : ℝ × E2 :=
  ((p.1 : ℝ × ℝ).1, p.2)

end Work.Cusp
