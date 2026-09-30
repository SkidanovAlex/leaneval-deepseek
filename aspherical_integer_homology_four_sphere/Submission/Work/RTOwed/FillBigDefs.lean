/-
# The "junction" filling charts of `M̂`: the definitions

The filling diagrams of `M̂` (item 2 of the contract) are the charts of the filling pieces whose
layers are `ChartLayer.uhs` (collar), `ChartLayer.warped` (polar) and `ChartLayer.flat` (core).

The transition analysis of the atlas shows that the collar and the polar families *must not*
overlap: the UHS model is the metric of the filling piece in the UHS coordinates only where the
profile of the filling matches the hyperbolic rate, i.e. on the region `r ≥ rJ` (`r` the metric
radial coordinate), while the warped model is the metric in the *polar* coordinates on all of the
filling piece.  Any chart whose source meets the junction layer `r = rJ` (`‖p‖∞ = 1/2`,
`β`-height `= s_J`) therefore has to be *polar valued* and `warped` layered, and has to cross the
junction: `Work.RTOwed.rBig`.

This file defines those charts, called **junction charts**:

* `jBox v cU k W kx δ` — the box of the chart, in the polar coordinates `(r,θ,w₁,w₂)`:
  `1/2 < r < 17/5`, the wedge pinning `uqOf v q ∈ (cU + k/4, cU + (k+1)/4)` of the perimeter
  coordinate (which pins the lift of the perimeter direction), the `w`-section condition
  `(q₂,q₃) ∈ W` (which pins the lift of the torus coordinates), and the collar box condition
  `|x(q) - kx| < δ` on the horizontal part `x(q)` of `polarToUHS v q` (which is what the collar
  coordinate inclusion needs, and which is bounded on the layers, so that finitely many `kx` cover);
* `jCoordM a v D tor cU k W kx δ` — the coordinate inclusion of the box:

  * for `r ≤ rJ` it is the inverse of the polar chart, `incW v ∘ cuspInvInner`;
  * for `r ≥ rJ` it is the collar coordinate inclusion `cuspCoordMTop` composed with `polarToUHS`,
    i.e. the point of `M̂` with UHS coordinates `polarToUHS v q`.

  The two branches agree on the junction `r = rJ`, because there the layer parameter is `1/2`, where
  the polar and the UHS charts describe the same point.  The value map of the resulting chart is the
  *polar coordinate* `Θ_v` of the point, on the whole source (this is what makes the transitions
  between two junction charts (lift) translations, and their transitions to the fold charts Möbius
  transformations through `polarToUHS` and the rigidity `Work.RTOwed.CuspRigid.foldLocal`).
-/
import Mathlib
import Submission.Work.RTOwed.CuspRigid
import Submission.Work.Cusp.ChartTop
import Submission.Work.Cusp.polarToUHS_ThetaPolar
import Submission.Work.RTOwed.instGlue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace

namespace Work.RTOwed

open Work.Cusp

/-- **The upper end of the radial window of the junction charts.**  `17/5 = 3.4` is below
`R₀ − log s₁ = 7/2 − log (11/10)`: this is what makes the *collar* branch of the junction coordinate
inclusion land in the box `cuspBoxTop` of the collar chart (its height window is `(s₁, sTop)`).
The junction charts cover the collar layer `r ∈ [rJ, R₀ − log β_min] ⊂ [3, 3.3]`. -/
def rBig : ℝ := 17 / 5

/-- **The box of a junction filling chart**, in the polar coordinates `q = (r,θ,w₁,w₂)`.

* `1/4 < q 0 < rBig`: the radial window (it crosses the junction `q 0 = rJ = 3` and it covers the
  whole polar layer `1/4 < q 0 < 3`; it also meets the core charts' sources `r < 1/2`, which is why
  the polar-to-Cartesian transition of `Work.RTOwed.jCore_iso` is needed);
* `q₂,q₃ ∈ W`: the pinning of the torus lift (`hsec`);
* the wedge condition on the perimeter coordinate `uqOf v q` (the pinning of the perimeter lift);
* `|x(q) − kx| < δ` where `x(q)` is the horizontal part of `polarToUHS v q`: the collar box
  condition, needed by the collar branch. -/
def jBox (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ) : Set E4 :=
  {q | 1 / 4 < q 0 ∧ q 0 < rBig ∧ (!₂[q 2, q 3] : E2) ∈ W ∧
      uqOf v q - cU ∈ Set.Ico 0 1 ∧
      Int.fract (uqOf v q - cU) ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4) ∧
      (∀ i, |xOf (polarToUHS v q) i - kx i| < δ)}

/-- The `polarBox` part of the junction box: `1/4 < q 0 < rJ + 1`. -/
theorem jBox_subset_polarBox (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2)
    (kx : E3) (δ : ℝ) : jBox v cU k W kx δ ⊆ polarBox := by
  intro q hq
  obtain ⟨h1, h2, -⟩ := hq
  have h4 : q 0 < 4 := by
    simp only [rBig] at h2
    linarith
  refine ⟨by linarith [h1], ?_⟩
  simp only [rJ]
  linarith


/-! ### The two numerical facts that make the collar branch land in the collar box -/

/-- `xOf (polarToUHS v q) = x` where `x` is the horizontal part of `polarToUHS v q`. -/
theorem polarToUHS_three (v : Work.Space.Cusp) (q : E4) :
    (polarToUHS v q) 3 = Real.exp (R0 - q 0) := rfl

/-- `R₀ − 17/5 = 1/10`. -/
theorem R0_sub_rBig : R0 - rBig = 1 / 10 := by
  simp only [R0, rBig]
  norm_num

/-- `log (11/10) < 1/10`, hence `s₁ = 11/10 < e^{1/10}`. -/
theorem exp_one_tenth_gt_s1 : s1 < Real.exp (1 / 10 : ℝ) := by
  have hpos : (0:ℝ) < 11/10 := by norm_num
  have hlog : Real.log (11/10) < 1/10 := by
    have h := Real.log_lt_sub_one_of_pos hpos (by norm_num : (11/10 : ℝ) ≠ 1)
    norm_num at h ⊢
    linarith
  have := (Real.log_lt_iff_lt_exp hpos).mp hlog
  simpa [s1] using this

/-- **The collar branch of a junction chart lands in the collar box.**  If `q 0 > rJ` then
`polarToUHS v q ∈ cuspBoxTop v kx δ` as soon as the horizontal box condition holds. -/
theorem polarToUHS_mem_cuspBoxTop (v : Work.Space.Cusp) (kx : E3) (δ : ℝ) {q : E4}
    (hbox : ∀ i, |xOf (polarToUHS v q) i - kx i| < δ) (hr : rJ < q 0) (hub : q 0 < rBig) :
    polarToUHS v q ∈ cuspBoxTop v kx δ := by
  refine ⟨hbox, ?_, ?_⟩
  · -- `s₁ < e^{R₀−q 0}`
    have h1 : R0 - q 0 > 1/10 := by
      have := R0_sub_rBig
      linarith
    have h2 : Real.exp (1/10 : ℝ) < Real.exp (R0 - q 0) := Real.exp_lt_exp.mpr h1
    have := lt_trans exp_one_tenth_gt_s1 h2
    simpa [polarToUHS] using this
  · -- `e^{R₀−q 0} < sTop`
    have h1 : Real.exp (R0 - q 0) < Real.exp (R0 - rJ) :=
      Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (R0 - rJ) = sJ := by simp only [sJ, rJ, R0]; norm_num
    rw [h2] at h1
    exact lt_trans h1 sJ_lt_sTop

/-- **The coordinate inclusion of a junction chart**: the point of `M̂` with polar coordinates `q`.

For `q 0 ≤ rJ` this is the inverse of the polar chart (the point of the filling piece of layer
parameter `q 0 / (2 rJ) ≤ 1/2`); for `q 0 > rJ` it is the point of `M̂` with UHS coordinates
`polarToUHS v q` (the collar coordinate inclusion of `Work.Cusp.ChartTop`).  The two branches agree
on `q 0 = rJ`. -/
noncomputable def jCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v)
    (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ)
    (q : {q : E4 // q ∈ jBox v cU k W kx δ}) : a.Mhat :=
  if h : q.1 0 ≤ rJ then
    a.incW v
      ((⟨(cuspInvInner v q.1).1, by
          have h1 : q.1 ∈ polarBox := jBox_subset_polarBox v cU k W kx δ q.2
          have hstr := cuspInvInner_mem_polarStratum v q.1 h1 h
          simp only [polarStratum, Set.mem_setOf_eq] at hstr
          refine ⟨le_trans (abs_le_nrm _ 0) ?_, le_trans (abs_le_nrm _ 1) ?_⟩ <;>
            linarith [hstr.2]⟩ : Work.Space.SquarePt),
        D.tor.symm (fun i => (((cuspInvInner v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))
  else
    cuspCoordMTop a v D kx δ ⟨polarToUHS v q.1, by
      obtain ⟨-, hub, -, -, -, hbox⟩ := q.2
      exact polarToUHS_mem_cuspBoxTop v kx δ hbox (not_le.mp h) hub⟩


/-- **The pinning data of a junction chart**: the wedge pinning of the perimeter coordinate
(`cU`, `k`), the section box `W` of the `w`-coordinates (with the injectivity condition `hsec`), the
horizontal box `(kx, δ)` of the collar branch, and the condition `δ ≤ 1/2` which makes the collar
coordinate inclusion an open embedding. -/
structure JPin (a : Work.Space.Assembly) (v : Work.Space.Cusp) where
  /-- The shift of the perimeter cut. -/
  cU : ℝ
  /-- The wedge index of the perimeter coordinate. -/
  k : Fin 4
  /-- The section box of the `w`-coordinates. -/
  W : Set E2
  /-- The centre of the horizontal box of the collar branch. -/
  kx : E3
  /-- The radius of the horizontal box of the collar branch. -/
  δ : ℝ
  /-- The box radius is at most `1/2`. -/
  hδ : δ ≤ 1 / 2
  /-- The section box is open. -/
  hW : IsOpen W
  /-- **The section condition**: the `w`-coordinates determine the cusp coordinates modulo `ℤ²`. -/
  hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y'

namespace JPin

variable {a : Work.Space.Assembly} {v : Work.Space.Cusp}

/-- The box of the junction chart with the pinning data `P`. -/
def box (P : JPin a v) : Set E4 := jBox v P.cU P.k P.W P.kx P.δ

/-- The coordinate inclusion of the junction chart with the pinning data `P`. -/
noncomputable def coordM (P : JPin a v) (D : Work.Cusp.CuspGlueData a v)
    (q : {q : E4 // q ∈ P.box}) : a.Mhat :=
  jCoordM a v D P.cU P.k P.W P.kx P.δ ⟨q.1, q.2⟩

end JPin

end Work.RTOwed
