/-
# Auxiliary vocabulary for the collar chart on `M̂` (and its layer-direction chart)

This file fixes the small vocabulary shared by the proof that the collar coordinate
`cuspCoordM a v D c δ` (`Work.Cusp.Assembly`) is an open embedding of the chart box
`cuspChartBox v c δ` into `M̂`.

The collar coordinate splits, below the ceiling `s = β x`, into the chart of the chimney
(`D.mbarLow`) and, above it, into the point of the filling piece recovered by `cuspInvOuter`.  It is
the *upper* branch which carries the analytic content: writing a point of the closed chart box above
the ceiling as `q = (x, s)` with `x = xOf q`, the recovered filling point is

  `cuspInvOuter v q = (t • bndOfU (outerU v x), outerY v x)`,

`t = ‖·‖∞` being the recovered layer parameter.  In other words the upper branch is the composite

  `cuspCoordUp = (layerPtSq × tor ∘ π) ∘ cuspCollarF`

of

* `cuspCollarF`: the point `q` of the collar source, viewed through its `(u,t,y)`-coordinates
  `(outerU v (xOf q), ‖(cuspInvOuter v q).1‖∞, outerY v (xOf q))` — an open embedding, because the
  map `x ↦ (outerU v x, outerY v x)` is a linear isomorphism `E3 ≅ ℝ × E2`
  (`cuspX_outerU_outerY`, `outerU_cuspX`, `outerY_cuspX`) and `t ↦ s = collarHeight t (β x)` is a
  homeomorphism of `(1/2,1]` onto `[β x, s_J)`;
* `layerPtSq`: the layer-direction chart `(u,t) ↦ t • bndOfU u` of the square, an open embedding of
  `(0,1) × (1/2,1]` onto `{p : ‖p‖∞ > 1/2} ∖ {(t,t) | 1/2 < t ≤ 1}` (the perimeter parameter `u` and
  the layer parameter `‖p‖∞` are coordinates of the square, `nrm_u_injOn`);
* the projection `(p,y) ↦ (p, tor.symm (y mod ℤ²))` of the cover, which is open (a product of the
  identity with the quotient map `E2 → (ℝ/ℤ)²`).

The names of this file are used by `Submission/Work/Cusp/isOpenEmbedding_layerPtSq.lean` and
`Submission/Work/Cusp/isOpenEmbedding_cuspCollarF.lean`.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.cuspInvOuter_mem_cuspStratum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### The layer-direction chart of the square -/

/-- The domain of the layer-direction chart of the collar: perimeter parameter `u ∈ (0,1)` (the
`s`-coordinate of the cusp chart is pinned to the slab `0 < outerU v x < 1`) and layer parameter
`t ∈ (1/2,1]` (the collar stratum of the filling piece). -/
def collarLayerDom : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ z.1 < 1 ∧ 1/2 < z.2 ∧ z.2 ≤ 1}

/-- The layer point `t • bndOfU u` of the square: layer parameter `z.2` in the direction
`bndOfU z.1` of the boundary. -/
def layerPt (z : ℝ × ℝ) : E2 := z.2 • bndOfU z.1

/-- The layer-direction chart of the collar, as a map into the square. -/
def layerPtSq (z : {z : ℝ × ℝ // z ∈ collarLayerDom}) : Work.Space.SquarePt :=
  ⟨layerPt z.1, by
    obtain ⟨-, -, h2, h3⟩ := z.2
    have ht : 0 < z.1.2 := lt_trans (by norm_num) h2
    have hn : nrm (layerPt z.1) = z.1.2 := by
      rw [layerPt, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos ht]
    have hle : nrm (layerPt z.1) ≤ 1 := by rw [hn]; exact h3
    exact ⟨le_trans (abs_le_nrm _ 0) hle, le_trans (abs_le_nrm _ 1) hle⟩⟩

/-- The layer parameter of the layer point is the second coordinate. -/
theorem nrm_layerPt {z : ℝ × ℝ} (hz : z ∈ collarLayerDom) : nrm (layerPt z) = z.2 := by
  obtain ⟨-, -, h2, -⟩ := hz
  rw [layerPt, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos (lt_trans (by norm_num) h2)]

/-- The perimeter parameter of the layer point is the first coordinate. -/
theorem u_layerPt {z : ℝ × ℝ} (hz : z ∈ collarLayerDom) : u (layerPt z) = z.1 := by
  have h0 : 0 < z.1 := hz.1
  have h1 : z.1 < 1 := hz.2.1
  have h2 : 1/2 < z.2 := hz.2.2.1
  have ht : 0 < z.2 := lt_trans (by norm_num) h2
  have hbnd : bnd (layerPt z) = bndOfU z.1 := by
    rw [bnd, nrm_layerPt hz, layerPt, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  rw [u, hbnd, uPerim_bndOfU, (Int.fract_eq_self).mpr ⟨le_of_lt h0, h1⟩]

/-! ### The collar source of the chart box and its `(u,t,y)`-coordinates -/

/-- **The collar source** of the chart box: the points of the closed chart box on or above the
ceiling with the perimeter coordinate in `(0,1)`.  It is the domain of the upper branch of the
collar coordinate. -/
def cuspCollarSource (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | q ∈ cuspSource v c δ ∧ 0 < outerU v (xOf q)}

theorem cuspCollarSource_subset_chartBox (v : Fin 5) (c : E3) (δ : ℝ) :
    cuspCollarSource v c δ ⊆ cuspChartBox v c δ := by
  rintro q ⟨⟨hbox, -⟩, hu⟩
  exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, hu, hbox.2.2.2.2⟩

/-- **The `(u,t,y)`-coordinates of a point of the collar source**: the perimeter coordinate
`outerU v (xOf q)`, the recovered layer parameter `‖(cuspInvOuter v q).1‖∞` and the phase
`outerY v (xOf q)`. -/
def cuspCollarF (v : Fin 5) (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspCollarSource v c δ}) :
    {z : ℝ × ℝ // z ∈ collarLayerDom} × E2 :=
  (⟨(outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1),
      ⟨q.2.2, q.2.1.1.2.2.2.2,
       (cuspInvOuter_mem_cuspStratum v c δ q.1 q.2.1).1,
       (cuspInvOuter_mem_cuspStratum v c δ q.1 q.2.1).2⟩⟩,
   outerY v (xOf q.1))

theorem cuspCollarF_fst (v : Fin 5) (c : E3) (δ : ℝ)
    (q : {q : E4 // q ∈ cuspCollarSource v c δ}) :
    (cuspCollarF v c δ q).1.1 = (outerU v (xOf q.1), nrm (cuspInvOuter v q.1).1) := rfl

theorem cuspCollarF_snd (v : Fin 5) (c : E3) (δ : ℝ)
    (q : {q : E4 // q ∈ cuspCollarSource v c δ}) :
    (cuspCollarF v c δ q).2 = outerY v (xOf q.1) := rfl

/-- **The recovered layer point is the layer point of its own coordinates**: on the collar source
the first component of `cuspInvOuter` is `‖·‖∞ • bndOfU (outerU v (xOf q))`, so that the
`(u,t)`-chart `layerPt` reproduces it. -/
theorem cuspInvOuter_fst_eq_smul (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSource v c δ) :
    (cuspInvOuter v q).1 = nrm (cuspInvOuter v q).1 • bndOfU (outerU v (xOf q)) := by
  obtain ⟨hbox, hβ⟩ := hq
  obtain ⟨-, hs1, hsJ, -, -⟩ := hbox
  set b : ℝ := beta (xOf q) with hb
  set t : ℝ := 1 + (Real.log (q 3) - Real.log b) /
      (2 * (Real.log b - Real.log sJ)) with ht
  have hbpos : 0 < b := by rw [hb]; exact beta_pos _
  have hb_le : b ≤ q 3 := by rw [hb]; exact hβ
  have hb_lt_sJ : b < sJ := lt_of_le_of_lt hb_le hsJ
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have ht_pos : 0 < t := by
    rw [ht, hb]
    have hDpos : 0 < Real.log sJ - Real.log (beta (xOf q)) := by
      have h := Real.log_lt_log (beta_pos (xOf q)) (by rwa [hb] at hb_lt_sJ)
      linarith
    have hAD : Real.log (q 3) - Real.log (beta (xOf q))
        < Real.log sJ - Real.log (beta (xOf q)) := by
      have h := Real.log_lt_log hq3pos hsJ; linarith
    have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q)))) := by ring
    rw [hden, div_neg]
    have hlt : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) < 1/2 := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (Real.log sJ - Real.log (beta (xOf q))))]
      linarith
    linarith
  have hpe : (cuspInvOuter v q).1 = t • bndOfU (outerU v (xOf q)) := by
    rw [ht, hb]; rfl
  rw [hpe, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos ht_pos]

/-- **The recovered layer parameter is `1` on the ceiling.**  For a point of the cusp box with
`q 3 = β (xOf q)` the logarithm correction in `cuspInvOuter` vanishes. -/
theorem cuspInvOuter_nrm_eq_one_of_ceiling (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hbox : q ∈ cuspBox v c δ) (hceil : q 3 = beta (xOf q)) :
    nrm (cuspInvOuter v q).1 = 1 := by
  obtain ⟨-, hs1, hsJ, -, -⟩ := hbox
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hb_lt_sJ : beta (xOf q) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hne : Real.log (beta (xOf q)) - Real.log sJ ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt (Real.log_lt_log hbpos hb_lt_sJ))
  have hpe : (cuspInvOuter v q).1
      = (1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log (beta (xOf q)) - Real.log sJ))) •
        bndOfU (outerU v (xOf q)) := rfl
  rw [hpe, hceil, sub_self, zero_div, add_zero, one_smul, nrm_bndOfU]

/-- **The upper branch of the collar coordinate**: the point of the `v`-th filling piece of `M̂`
recovered from a point of the collar source, through its `(u,t,y)`-coordinates. -/
def cuspCoordUp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspCollarSource v c δ}) :
    Work.Space.SquarePt × a.Torus v :=
  (layerPtSq (cuspCollarF v c δ q).1,
   D.tor.symm (fun i => (((cuspCollarF v c δ q).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- **`cuspCoordUp` is the composite `(layerPtSq × tor ∘ π) ∘ cuspCollarF`**, hence open as soon as
its two factors are. -/
theorem cuspCoordUp_eq_comp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) :
    cuspCoordUp a v D c δ =
      (Prod.map layerPtSq
          (fun y : E2 => D.tor.symm (fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ))))) ∘
        (cuspCollarF v c δ) := rfl

/-- **The upper branch is the point of the filling piece recovered by `cuspInvOuter`.** -/
theorem cuspCoordUp_eq (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspCollarSource v c δ}) :
    cuspCoordUp a v D c δ q =
      ((⟨(cuspInvOuter v q.1).1, cuspInvOuter_mem_Sq v c δ q.1 q.2.1⟩ : Work.Space.SquarePt),
       D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
  unfold cuspCoordUp layerPtSq layerPt
  refine Prod.ext (Subtype.ext ?_) ?_
  · exact (cuspInvOuter_fst_eq_smul v c δ q.1 q.2.1).symm
  · rfl


/-- The points of a subtype of `E4` whose underlying point lies in a given set of `E4`; this is the
trace of a chart box (or of one of its pieces) on an open set of `E4`. -/
def subOfSet {p : E4 → Prop} (S : Set E4) : Set {x : E4 // p x} := {z | (z.1 : E4) ∈ S}

theorem subOfSet_eq_preimage {p : E4 → Prop} (S : Set E4) :
    subOfSet (p := p) S = (Subtype.val : {x : E4 // p x} → E4) ⁻¹' S := rfl

end Work.Cusp
