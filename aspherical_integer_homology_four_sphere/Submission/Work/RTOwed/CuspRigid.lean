/-
# The rigidity of the cusp chart of `M̄` (interface layer)

`Work.Cusp.CuspGlueData` is the *qualitative* interface of the cusp chapter: it records that
`mbarLow` is a chart of the hyperbolic piece on every collar box, and the coordinate formula of the
gluing.  It is deliberately weak: any `mbarLow` composed with a homeomorphism of `M̄` supported
below the ceiling satisfies it, and for such a chart the cross transitions to the fold charts are
not smooth.

This file adds the *rigidity* of the concrete chart, in the same spirit as the fold block: the
lattice periodicity, the fibre of the chart, and the fact that its composite with every fold chart
is locally a single Möbius transformation of the upper half space model.

```lean
structure CuspRigid (g : Work.RTInstance.GlueHomeo) (v : Work.Cusp.Cusp)
    (D : Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v) : Prop where
  periodic  : ∀ (q : E4) (L : E3), latVec v L → D.mbarLow (q + liftE4 L) = D.mbarLow q
  fibre     : ... mbarLow q = mbarLow q' → latVec v (xOf q' - xOf q) ∧ q' 3 = q 3
  foldLocal : ... ∃ V ∋ q open, ∃ B Lorentz, foldChart i (mbarLow q') = mobius B q' on V
```

The three fields are exactly what the cross transitions `Work.RTInstance.CrossData` and the
collar–collar transitions need: `foldLocal` gives the local Möbius form of every cross transition
(hence smoothness and isometry, by `Work.HypModel.mobius_contDiffOn`/`mobius_isometry`), `fibre`
makes the collar–collar transitions locally constant lattice translations, and `periodic` describes
their sources.

The inhabitants of the three fields are proved for the **concrete** chart `Work.RTOwed.mbarLow`
(composed with the concrete gluing `Work.RTOwed.glueData`).
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.cuspGlueData
import Submission.Work.RTOwed.cuspChartWallReflect
import Submission.Work.RTOwed.chartKlein_self_facet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Matrix
open scoped Matrix

namespace Work.RTOwed

open Work.FoldInst

/-- The lift of a horizontal lattice vector to `E4`. -/
def liftE4 (L : Work.Cusp.E3) : Work.Cusp.E4 := !₂[L 0, L 1, L 2, 0]

lemma liftE4_apply (L : Work.Cusp.E3) (j : Fin 4) :
    liftE4 L j = if h : (j : ℕ) < 3 then L ⟨j, h⟩ else 0 := by
  fin_cases j <;> simp [liftE4]

/-- The reflection of the `t`-th *horizontal* coordinate of an upper half space point
(`t : Fin 3` indexes the coordinates `0,1,2`). -/
def reflCoord (t : Fin 3) : Work.Cusp.E4 → Work.Cusp.E4 :=
  Work.FoldInst.reflCoords ({t} : Finset (Fin 3))

lemma reflCoord_apply (t : Fin 3) (z : Work.Cusp.E4) (j : Fin 4) :
    reflCoord t z j = if h : (j : ℕ) < 3 then
      (if (⟨j, h⟩ : Fin 3) = t then -1 else 1) * z j else z j := by
  rw [reflCoord, Work.FoldInst.reflCoords_apply]
  by_cases h : (j : ℕ) < 3
  · rw [dif_pos h, dif_pos h]
    congr 1
    by_cases hj : (⟨j, h⟩ : Fin 3) = t <;> simp [hj]
  · rw [dif_neg h, dif_neg h]

/-- The reflection of the `k`-th horizontal coordinate of an upper half space point in the wall
`{z k = c}` (the height and the other coordinates are unchanged). -/
def reflWall4 (k : Fin 3) (c : ℝ) (z : Work.Cusp.E4) : Work.Cusp.E4 :=
  WithLp.toLp 2 fun j => if (j : ℕ) = (k : ℕ) then 2 * c - z j else z j

lemma reflWall4_apply (k : Fin 3) (c : ℝ) (z : Work.Cusp.E4) (j : Fin 4) :
    reflWall4 k c z j = if (j : ℕ) = (k : ℕ) then 2 * c - z j else z j := rfl

lemma reflWall4_comm (k : Fin 3) (c : ℝ) (x : CuspE3) (s : ℝ) :
    reflWall4 k c (mkE4 x s) = mkE4 (reflWall k c x) s := by
  apply PiLp.ext
  intro j
  fin_cases k <;> fin_cases j <;>
    simp [reflWall4_apply, reflWall_apply, mkE4] <;> ring

@[simp] lemma reflWall4_height (k : Fin 3) (c : ℝ) (z : Work.Cusp.E4) :
    reflWall4 k c z 3 = z 3 := by
  rw [reflWall4_apply]
  have h : ((3 : Fin 4) : ℕ) ≠ (k : ℕ) := by have := k.isLt; omega
  rw [if_neg h]

/-- **The rigidity of the cusp chart of `M̄` at one cusp.**  The three facts that the cross
transitions and the collar–collar transitions of the atlas of `M̂` need, and which are *not*
implied by the qualitative interface `Work.Cusp.CuspGlueData`:
`Λ_v`-periodicity, the fibre of the chart on the chimney, and the local Möbius form of the composite
with a fold chart. -/
structure CuspRigid (g : Work.RTInstance.GlueHomeo) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v) : Prop where
  /-- **(F1)** `Λ_v`-periodicity: the chart is invariant under the lattice translations. -/
  periodic : ∀ (q : Work.Cusp.E4) (L : Work.Cusp.E3), latVec v L →
    D.mbarLow (q + liftE4 L) = D.mbarLow q
  /-- **(F2)** The fibre of the chart on the chimney is exactly a `Λ_v`-orbit: two points of the
  region below the ceiling with the same image differ by a lattice vector, and have the same
  height. -/
  fibre : ∀ {q q' : Work.Cusp.E4}, 11 / 10 ≤ q 3 → q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q) →
    11 / 10 ≤ q' 3 → q' 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q') →
    D.mbarLow q = D.mbarLow q' →
    latVec v (Work.Cusp.xOf q' - Work.Cusp.xOf q) ∧ q' 3 = q 3
  /-- **(F3)** The composite of the chart with a fold chart is locally **one** Möbius transformation
  of the upper half space model -- exactly the shape of the fold block's `localModel`. -/
  foldLocal : ∀ (i : Fin 98) {q : Work.Cusp.E4}, 11 / 10 < q 3 →
    q 3 < Work.Cusp.beta (Work.Cusp.xOf q) →
    D.mbarLow q ∈ (Work.FoldInst.foldChart i).source →
    ∃ (V : Set Work.Cusp.E4) (B : Matrix (Fin 5) (Fin 5) ℝ),
      IsOpen V ∧ q ∈ V ∧ Work.HypModel.IsLorentzMat B ∧
        ∀ q' ∈ V, D.mbarLow q' ∈ (Work.FoldInst.foldChart i).source →
          Work.FoldInst.foldChart i (D.mbarLow q') = Work.HypModel.mobius B q'

end Work.RTOwed
