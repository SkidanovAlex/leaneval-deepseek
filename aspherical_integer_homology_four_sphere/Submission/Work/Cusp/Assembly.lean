/-
# The cusp charts on the assembled space `M̂` (interface layer)

This file states, against the *abstract* assembly `Work.Space.Assembly` of the area `SPACE`, the form
in which the cusp charts and the cover theorem reach the assembled space `M̂`.

## What is here

The assembly datum provides `M̄`, the five torus factors `Torus v` of the filling pieces, the closed
cusp boundary `Tset ⊆ M̄`, the gluing `glue : Tset ≃ₜ {q : Σ v, SquarePt × Torus v // q ∈ FillingBdry}`
and the assembled space `Mhat = (M̄ ⊔ Σ v, SquarePt × Torus v)/~₃` with the injections `incMbar`,
`incW`.  On top of it this file adds

* the layer sets `collarLayer`, `polarLayer`, `coreLayer` (conditions on the layer parameter `nrm`
  only) and the open chart box `cuspChartBox v c δ` of the collar chart;
* `CuspGlueData a v`: the *coordinate description of the gluing* — the cusp chart `mbarLow` of the
  hyperbolic piece in the chimney (fields: continuity, injectivity and openness of its image on the
  region below the ceiling, and that the ceiling lies on `Tset`), the ceiling map `mbarPt`, and the
  identification `glue_eq`: the ceiling point over `u σ_v + y` is glued to the filling boundary point
  with perimeter parameter `u` and torus coordinates `y`.  Its fields are the concrete deliverables of
  the areas `FOLD` (the cusp chart of `M̄`) and `CUSP` (the formulas of this chapter) for the real `Q̄`;
* `cuspCoordM a v D c δ : cuspChartBox v c δ → M̂`, the coordinate inclusion of the collar chart: the
  point of the chimney of `M̄` below the ceiling, the point of the filling piece above it.

The chapter then proves (in the modules next to this one)

* `exists_tauHomeo`: `ℝ³/Λ_v ≃ₜ {(x + Λ_v, β x)}`, i.e. the cusp torus is the graph of the (descended)
  ceiling — the coordinate form of `τ_v : ℝ³/Λ_v ≃ₜ T_v`;
* `cuspCoordM_continuous`, `cuspCoordM_injective` (for a box of side `2δ ≤ 1`, which is what makes
  the `(u,y)`-coordinates of `x` unique);
* `cover_univ`: **the cover theorem on `M̂`** — if the fold charts cover `M̄ ∖ Tset`, then the fold
  sources together with the collar, polar and core layers of the five filling pieces cover `M̂`.

## What is left to the assembly

To turn `cuspCoordM` into an `OpenPartialHomeomorph a.Mhat E4` (the contract's `cuspChart` on `M̂`)
one needs, on top of continuity and injectivity, that the image of `cuspCoordM` is open in `M̂` and
that the inverse is continuous on it; equivalently that `cuspCoordM` is an open embedding.  These two
inputs come from `CuspGlueData` (`mbarLow_open` for the below-ceiling part, the quotient openness
criterion `Assembly.isOpen_iff_sum` for the above-ceiling part) and are then packaged by
`Topology.IsOpenEmbedding.toOpenPartialHomeomorph`.  The polar and core charts of `M̂` are obtained the
same way from `exists_polarChartS`/`exists_coreChart` after intersecting the box `B` with a local
section of the quotient `ℝ² → (ℝ/ℤ)²` (a small `w`-box), which is why the chart targets of this
chapter are stated on the `(p,y)`-cover.
-/
import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.cuspInvOuter_mem_Sq
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
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

/-- The collar layer of a filling piece: `‖p‖∞ ≥ 1/2` (the cusp stratum, including the glued
boundary `‖p‖∞ = 1`). -/
def collarLayer (T : Type*) : Set (Work.Space.SquarePt × T) :=
  {q | 1/2 ≤ nrm (q.1 : E2)}

/-- The polar layer of a filling piece: `‖p‖∞ > 1/24`. -/
def polarLayer (T : Type*) : Set (Work.Space.SquarePt × T) :=
  {q | 1/24 < nrm (q.1 : E2)}

/-- The core layer of a filling piece: `‖p‖∞ < 1/12`. -/
def coreLayer (T : Type*) : Set (Work.Space.SquarePt × T) :=
  {q | nrm (q.1 : E2) < 1/12}

/-- The point of `E4` with horizontal part `x` and height the ceiling `β x`. -/
def ceilingPt (x : E3) : E4 := !₂[x 0, x 1, x 2, beta x]

/-- The **open** chart box of the collar chart on `M̂`: an open box of side `2δ` in `x`, heights in
`(s₁, s_J)`, and the strict slab `0 < outerU v x < 1` (so that the cusp coordinate `x` determines
the perimeter coordinate `u` and the two torus coordinates uniquely).  No condition on the ceiling:
the box crosses `s = β(x)`, which is what makes the collar chart meet the gluing. -/
def cuspChartBox (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | (∀ i, |xOf q i - c i| < δ) ∧ s1 < q 3 ∧ q 3 < sJ ∧
    0 < outerU v (xOf q) ∧ outerU v (xOf q) < 1}

/-- The coordinate description of the gluing `~₃` at one cusp, in the coordinates of this chapter.

The fields split into the two sides of the gluing.  `mbarLow` is the *cusp chart of the hyperbolic
piece* in the chimney over the truncation torus (the point of `M̄` with UHS coordinates `q`, for `q`
below the ceiling `s ≤ β(x)`): it is a chart, i.e. injective with open image on the region below the
ceiling (`mbarLow_cont`, `mbarLow_inj`, `mbarLow_open`), and on the ceiling it lands on the truncation
torus (`ceiling_mem`).  `mbarPt` is the ceiling composed with the cusp coordinate, kept for
convenience.  `glue_eq` is the identification itself: the ceiling point over `u σ_v + y` is glued to
the filling boundary point with perimeter parameter `u` and torus coordinates `y`.

These are the concrete deliverables of the areas `FOLD` (the cusp chart of `M̄`) and `CUSP` (the
coordinate formulas) for the real `Q̄`; everything proved from them is the chart construction on
`M̂`. -/
structure CuspGlueData (a : Work.Space.Assembly) (v : Work.Space.Cusp) where
  /-- The identification of the `v`-th torus factor with the two torus coordinates `(ℝ/ℤ)²`. -/
  tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))
  /-- The cusp chart of `M̄` in the chimney: the point of `M̄` with UHS coordinates `q`. -/
  mbarLow : E4 → a.Mbar
  /-- It is continuous on the chimney region of every box. -/
  mbarLow_cont : ∀ (c : E3) (δ : ℝ),
    ContinuousOn mbarLow {q : E4 | q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)}
  /-- It is injective there. -/
  mbarLow_inj : ∀ (c : E3) (δ : ℝ), δ ≤ 1/2 →
    Set.InjOn mbarLow {q : E4 | q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)}
  /-- Its image is open in `M̄`. -/
  mbarLow_open : ∀ (c : E3) (δ : ℝ),
    IsOpen (mbarLow '' {q : E4 | q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)})
  /-- **It is a chart of `M̄`** on the part of every box that lies below the ceiling: an open
  embedding into `M̄` (continuity, injectivity, and the inverse continuous on the image).  This is
  FOLD's collar chart of the hyperbolic piece in cusp coordinates. -/
  mbarLow_isEmbedding : ∀ (c : E3) (δ : ℝ), δ ≤ 1/2 →
    Topology.IsOpenEmbedding
      (fun q : {q : E4 // q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)} => mbarLow q)
  /-- **Points strictly below the ceiling are in the open piece**: the chimney of the cusp chart
  meets the cusp boundary `Tset` only at the ceiling.  This is what makes the collar chart's image
  open in `M̂` (together with `isOpen_iff_sum`). -/
  mbarLow_not_Tset : ∀ (c : E3) (δ : ℝ) {q : E4}, q ∈ cuspChartBox v c δ →
    q 3 < beta (xOf q) → mbarLow q ∉ a.Tset
  /-- The points of the ceiling lie on the truncation torus. -/
  ceiling_mem : ∀ (c : E3) (δ : ℝ) {q : E4}, q ∈ cuspChartBox v c δ →
    q 3 = beta (xOf q) → mbarLow q ∈ a.Tset
  /-- **The chart of `M̄` on the *unslabbed* collar box.**  The same chart of the hyperbolic piece,
  on the slab-free box `cuspBoxTop v c δ` (side `2δ` in `x`, heights in `(s₁, sTop)`), below the
  ceiling.  This is the analogue of `mbarLow_cont` for the collar family which covers the corner
  directions of the square. -/
  mbarLow_contTop : ∀ (c : E3) (δ : ℝ),
    ContinuousOn mbarLow {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)}
  /-- It is injective there (for `δ ≤ 1/2`, so that the box meets no translate of `Λ_v`). -/
  mbarLow_injTop : ∀ (c : E3) (δ : ℝ), δ ≤ 1/2 →
    Set.InjOn mbarLow {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)}
  /-- Its image is open in `M̄`. -/
  mbarLow_openTop : ∀ (c : E3) (δ : ℝ),
    IsOpen (mbarLow '' {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)})
  /-- **It is a chart of `M̄`** on the part of every unslabbed box lying below the ceiling. -/
  mbarLow_isEmbeddingTop : ∀ (c : E3) (δ : ℝ), δ ≤ 1/2 →
    Topology.IsOpenEmbedding
      (fun q : {q : E4 // q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)} => mbarLow q)
  /-- **Points strictly below the ceiling of the unslabbed box are in the open piece**. -/
  mbarLow_not_TsetTop : ∀ (c : E3) (δ : ℝ) {q : E4}, q ∈ cuspBoxTop v c δ →
    q 3 < beta (xOf q) → mbarLow q ∉ a.Tset
  /-- The ceiling point over a cusp coordinate `x`. -/
  mbarPt : E3 → a.Mbar
  /-- It is the value of the chart at the ceiling. -/
  mbarPt_eq : ∀ (x : E3), mbarPt x = mbarLow (ceilingPt x)
  /-- The ceiling points lie on the truncation torus. -/
  mbarPt_mem : ∀ x, mbarPt x ∈ a.Tset
  /-- **The gluing, in coordinates**: the ceiling point over `u σ_v + y` is the point of the filling
  boundary with perimeter parameter `u` and torus coordinates `y`. -/
  glue_eq : ∀ (u : ℝ) (y : E2),
    a.glue ⟨mbarPt (cuspX v u y), mbarPt_mem _⟩ =
      ⟨⟨v, (⟨bndOfU u, by
            simpa only [Work.Space.Sq, Sq] using bndOfU_mem u⟩,
            (tor.symm (fun i => (y i : AddCircle (1 : ℝ)))))⟩, by
          simp only [Work.Space.FillingBdry, Set.mem_setOf_eq, Work.Space.sqNorm]
          exact nrm_bndOfU u⟩

/-- **The coordinate inclusion of the collar chart on `M̂`.**  For a cusp coordinate `q` in the
chart box: below the ceiling (`s < β x`) it is the point of the chimney of the hyperbolic piece
`M̄`, at or above it the point of the filling piece obtained by inverting the outer chart. -/
def cuspCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspChartBox v c δ}) : a.Mhat :=
  if h : q.1 3 < beta (xOf q.1) then a.incMbar (D.mbarLow q.1)
  else
    have hsrc : q.1 ∈ cuspSource v c δ :=
      ⟨⟨q.2.1, q.2.2.1, q.2.2.2.1, le_of_lt q.2.2.2.2.1, q.2.2.2.2.2⟩, not_lt.mp h⟩
    a.incW v
      ((⟨(cuspInvOuter v q.1).1, by
          simpa only [Work.Space.Sq, Sq] using
            cuspInvOuter_mem_Sq v c δ q.1 hsrc⟩ : Work.Space.SquarePt),
        D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- **The coordinate inclusion of the *unslabbed* collar chart on `M̂`.**  Same as `cuspCoordM` but
for the slab-free box `cuspBoxTop v c δ`: below the ceiling the point of the chimney of `M̄`, at or
above it the point of the filling piece recovered by the outer chart.  The recovered point lies in
`Sq` by `cuspInvOuter_mem_SqTop` (its layer parameter is in `(1/4,1]`,
`cuspInvOuter_nrm_Top`), and there is *no* meridian slab: the meridian parameter
`outerU v (xOf q)` may be any real number. -/
def cuspCoordMTop (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspBoxTop v c δ}) : a.Mhat :=
  if h : q.1 3 < beta (xOf q.1) then a.incMbar (D.mbarLow q.1)
  else
    a.incW v
      ((⟨(cuspInvOuter v q.1).1, by
          simpa only [Work.Space.Sq, Sq] using
            cuspInvOuter_mem_SqTop v c δ q.1 ⟨q.2, not_lt.mp h⟩⟩ : Work.Space.SquarePt),
        D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- The target box of the core chart on `M̂`: the core disk `r < 1/2` intersected with a `w`-box `W`
(a local section of the quotient `ℝ² → (ℝ/ℤ)²` in the `w`-coordinates). -/
def coreBoxSect (W : Set E2) : Set E4 :=
  {q | Real.sqrt (q 0 ^ 2 + q 1 ^ 2) < 1/2 ∧ (!₂[q 2, q 3] : E2) ∈ W}

/-- **The coordinate inclusion of the core chart on `M̂`**: the point of the filling piece obtained
by inverting the core chart. -/
def coreCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2)
    (q : {q : E4 // q ∈ coreBoxSect W}) : a.Mhat :=
  a.incW v
    ((⟨(cuspInvCore v q.1).1, by
        have h := cuspInvCore_mem_coreStratum v q.1 (by
          simp only [coreBox, Set.mem_setOf_eq]
          exact q.2.1)
        simp only [coreStratum, Set.mem_setOf_eq] at h
        have h1 : nrm (cuspInvCore v q.1).1 < 1 := by linarith
        exact ⟨le_trans (abs_le_nrm _ 0) (le_of_lt h1),
          le_trans (abs_le_nrm _ 1) (le_of_lt h1)⟩⟩ : Work.Space.SquarePt),
      tor.symm (fun i => (((cuspInvCore v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- The target box of the `(c,k)`-th polar chart on `M̂`: the polar box intersected with a `w`-box
`W` (a local section of `ℝ² → (ℝ/ℤ)²`) and with the angle pinning of the `(c,k)`-th wedge. -/
def polarBoxSect (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2) : Set E4 :=
  {q | q ∈ polarBox ∧ (!₂[q 2, q 3] : E2) ∈ W ∧ q 0 < rJ ∧
    uqOf v q - c ∈ Set.Ico 0 1 ∧
    Int.fract (uqOf v q - c) ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}

/-- **The coordinate inclusion of the `(c,k)`-th polar chart on `M̂`.** -/
def polarCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (q : {q : E4 // q ∈ polarBoxSect v c k W}) : a.Mhat :=
  a.incW v
    ((⟨(cuspInvInner v q.1).1, by
        have h1 : q.1 ∈ polarBox := q.2.1
        have h2 : q.1 0 ≤ rJ := le_of_lt q.2.2.2.1
        have h := cuspInvInner_mem_polarStratum v q.1 h1 h2
        simp only [polarStratum, Set.mem_setOf_eq] at h
        refine ⟨le_trans (abs_le_nrm _ 0) ?_, le_trans (abs_le_nrm _ 1) ?_⟩ <;>
          linarith [h.2]⟩ : Work.Space.SquarePt),
      tor.symm (fun i => (((cuspInvInner v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

end Work.Cusp
