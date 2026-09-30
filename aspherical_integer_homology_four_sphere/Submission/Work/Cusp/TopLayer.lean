/-
# The collar coordinate of the unslabbed family

The collar coordinate of the `v`-th cusp on the **unslabbed** collar box writes a point `q` of the
collar source `cuspSourceTop v c δ` (on or above the ceiling, heights in `(s₁, sTop)`) in the
coordinates

  `(u, t, y) = (outerU v (xOf q), ‖(cuspInvOuter v q).1‖∞, outerY v (xOf q))`,

the first two bundled as an element of the layer domain
`layerDomI (cuspAnchor v c) = (outerU v c − 1/2, outerU v c + 1/2) × (1/4, 1]`:

* `outerU_mem_layerA`: the box moves by at most `δ ≤ 1/2` in the meridian direction, so its meridian
  parameter lies in the interval `(outerU v c − 1/2, outerU v c + 1/2)`;
* `cuspInvOuter_nrm_Top`: the recovered layer parameter lies in `(1/4, 1]`.

The map is an open embedding (`isOpenEmbedding_cuspTopF`), with continuous inverse `cuspTopInv`
(the reassembly `(u,t,y) ↦ (cuspX v u y, collarHeight t (β (cuspX v u y)))`), and its range is the
preimage of the open `(u,y)`-box `cuspTopBox2 v c δ`.

The point of the collar coordinate is that the *upper branch* of the collar chart of `M̂`

  `cuspTopUp = (layerPtI (cuspAnchor v c) × (tor ∘ mod)) ∘ cuspTopF`

factors through the layer chart `layerPtI (cuspAnchor v c)` of the filling square — the chart which
covers the **corner directions** `u ∈ ℤ` of the square, and which the slabbed family cannot reach.
-/
import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.outerU_axis
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvOuter_heightTop
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.Assembly
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-- **The collar coordinate of the unslabbed family**, as a map into the layer domain
`layerDomI (cuspAnchor v c) × E2`. -/
def cuspTopF (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q : {q : E4 // q ∈ cuspSourceTop v c δ}) :
    {z : ℝ × ℝ // z ∈ layerDomI (cuspAnchor v c)} × E2 :=
  (⟨(outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1),
      ⟨outerU_mem_layerA v c δ hδ (q := q.1) q.2.1,
       (cuspInvOuter_nrm_Top v c δ q.1 q.2).1,
       (cuspInvOuter_nrm_Top v c δ q.1 q.2).2⟩⟩,
   outerY v (xOf q.1))

/-- The first (`(u,t)`) coordinate of the collar coordinate. -/
theorem cuspTopF_fst (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q : {q : E4 // q ∈ cuspSourceTop v c δ}) :
    ((cuspTopF v c δ hδ q).1 : ℝ × ℝ) = (outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1) := rfl

/-- The second (`y`) coordinate of the collar coordinate. -/
theorem cuspTopF_snd (v : Fin 5) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q : {q : E4 // q ∈ cuspSourceTop v c δ}) :
    (cuspTopF v c δ hδ q).2 = outerY v (xOf q.1) := rfl

/-- **The inverse of the collar coordinate**: reassemble the point of `E4` from `(u,t,y)` by
`x = cuspX v u y` and the collar height `s = collarHeight t (β (cuspX v u y))`. -/
def cuspTopInv (v : Fin 5) (a : ℝ)
    (p : {z : ℝ × ℝ // z ∈ layerDomI a} × E2) : E4 :=
  mkE4 (cuspX v (p.1 : ℝ × ℝ).1 p.2)
    (collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v (p.1 : ℝ × ℝ).1 p.2)))

/-- **The upper branch of the collar chart of `M̂`**, in the coordinates of the filling piece: the
layer point `layerPtI (cuspAnchor v c)` of the layer domain and the torus coordinate obtained by
reducing the phase modulo `ℤ²`. -/
def cuspTopUp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q : {q : E4 // q ∈ cuspSourceTop v c δ}) : Work.Space.SquarePt × a.Torus v :=
  (layerPtI (cuspAnchor v c) (cuspTopF v c δ hδ q).1,
   D.tor.symm (fun i => (((cuspTopF v c δ hδ q).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- **`cuspTopUp` is the composite `(layerPtI × (tor ∘ mod)) ∘ cuspTopF`**, hence open (and an open
map) as soon as its factors are. -/
theorem cuspTopUp_eq_comp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    cuspTopUp a v D c δ hδ =
      (Prod.map (layerPtI (cuspAnchor v c))
          (fun y : E2 => D.tor.symm (fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ))))) ∘
        (cuspTopF v c δ hδ) := rfl

end Work.Cusp
