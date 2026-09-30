/-
# The collar coordinate `cuspCollarF` of the filling piece: inverse and target box

`cuspCollarF v c δ` (`Work.Cusp.CuspChartAux`) is the point of the collar source
`cuspCollarSource v c δ` of the chart box, written in its `(u,t,y)`-coordinates: the perimeter
coordinate `u = outerU v (xOf q)`, the recovered layer parameter `t = ‖(cuspInvOuter v q).1‖∞`
and the phase `y = outerY v (xOf q)`.

This file fixes the vocabulary of the *inverse* picture, in which the collar coordinate is seen as
a homeomorphism onto its range:

* `mkE4 x s`: the point of `E4` with horizontal part `x ∈ E3` and height `s`;
* `cuspCollarBox v c δ`: the open box
  `{(u,y) | ∀ i, |(cuspX v u y) i − c i| < δ}` of the *recovered* cusp coordinates — the range of
  `cuspCollarF` is exactly the set of `(u,t,y)` whose `(u,y)`-part lies in this box (`t` being
  already confined to `(1/2,1]` by the type of the target);
* `cuspCollarInv v`: the formula for the inverse of the collar coordinate, which reassembles the
  point of `E4` from `(u,t,y)` by `x = cuspX v u y` and `s = collarHeight t (β x)`.

The names here are used by the modules proving `Continuous (cuspCollarInv v)`,
`Continuous (cuspCollarF v c δ)`, `cuspCollarInv v (cuspCollarF v c δ q) = q`,
`p ∈ range (cuspCollarF v c δ) ↔ (p.1.1, p.2) ∈ cuspCollarBox v c δ` and
`IsOpen (cuspCollarBox v c δ)`, which assemble into
`isOpenEmbedding_cuspCollarF`.
-/
import Mathlib
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.cuspInvOuter_mem_cuspStratum
import Submission.Work.Cusp.cuspInvOuter_continuousOn
import Submission.Work.Cusp.cuspInvOuter_height
import Submission.Work.Cusp.collarHeight_mem
import Submission.Work.Cusp.collarHeight_one
import Submission.Work.Cusp.collarHeight_strictAntiOn
import Submission.Work.Cusp.collarHeight_inv
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.s1_lt_betaMin
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.outerU_continuous
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### The point of `E4` with a given horizontal part and height -/

/-- The point of `E4` with horizontal part `x` and height `s` (`E4` is `ℝ³ × ℝ`). -/
def mkE4 (x : E3) (s : ℝ) : E4 := !₂[x 0, x 1, x 2, s]

@[simp] theorem xOf_mkE4 (x : E3) (s : ℝ) : xOf (mkE4 x s) = x := by
  ext i
  fin_cases i <;> simp [mkE4, xOf]

@[simp] theorem mkE4_apply_three (x : E3) (s : ℝ) : mkE4 x s 3 = s := by
  simp [mkE4]

/-- A point of `E4` is its horizontal part together with its height. -/
theorem mkE4_xOf_three (q : E4) : mkE4 (xOf q) (q 3) = q := by
  ext i
  fin_cases i <;> simp [mkE4, xOf]

/-! ### Continuity of the coordinate constructions -/

/-- `(a x, b x)` is continuous when `a` and `b` are. -/
theorem continuous_vec2 {X : Type*} [TopologicalSpace X] {a b : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => (!₂[a x, b x] : E2)) := by
  have h : Continuous fun x => (![a x, b x] : Fin 2 → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp h

/-- `(a x, b x, c x)` is continuous when `a`, `b` and `c` are. -/
theorem continuous_vec3 {X : Type*} [TopologicalSpace X] {a b c : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => (!₂[a x, b x, c x] : E3)) := by
  have h : Continuous fun x => (![a x, b x, c x] : Fin 3 → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-- `(a x, b x, c x, d x)` is continuous when `a`, `b`, `c` and `d` are. -/
theorem continuous_vec4 {X : Type*} [TopologicalSpace X] {a b c d : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun x => (!₂[a x, b x, c x, d x] : E4)) := by
  have h : Continuous fun x => (![a x, b x, c x, d x] : Fin 4 → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
    · simpa using hd
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp h

/-- **`mkE4` is continuous in its two arguments.** -/
theorem continuous_mkE4 {X : Type*} [TopologicalSpace X] {a : X → E3} {b : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => mkE4 (a x) (b x)) := by
  unfold mkE4
  refine continuous_vec4 ?_ ?_ ?_ hb
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp ha
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp ha
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp ha

/-- **The cusp coordinate `cuspX v u y = u σ_v + y₂λ₂ + y₃λ₃` is continuous in `(u,y)`.** -/
theorem continuous_cuspX (v : Fin 5) : Continuous (fun w : ℝ × E2 => cuspX v w.1 w.2) := by
  unfold cuspX cuspY
  fun_prop

/-- **`outerY v` is continuous** (it is linear in the cusp coordinate). -/
theorem continuous_outerY (v : Fin 5) : Continuous (fun x : E3 => outerY v x) := by
  unfold outerY outerU kappaCoord
  refine continuous_vec2 ?_ ?_
  · fun_prop
  · fun_prop

/-! ### The collar box and the inverse collar coordinate -/

/-- **The box of `(u,y)`-coordinates of the range of the collar coordinate**: the points whose
recovered cusp coordinate `cuspX v u y` lies in the box of side `2δ` around `c`. -/
def cuspCollarBox (v : Fin 5) (c : E3) (δ : ℝ) : Set (ℝ × E2) :=
  {w | ∀ i, |(cuspX v w.1 w.2) i - c i| < δ}

/-- **The `(u,y)`-coordinates of a point of the collar target**: its perimeter coordinate and its
phase, forgetting the layer parameter `t ∈ (1/2,1]`. -/
def cuspCollarCoords (p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2) : ℝ × E2 :=
  ((p.1 : ℝ × ℝ).1, p.2)

/-- The `(u,y)`-coordinates are continuous. -/
theorem continuous_cuspCollarCoords : Continuous cuspCollarCoords := by
  unfold cuspCollarCoords
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_subtype_val.comp continuous_fst).fst
  · exact continuous_snd

/-- **The inverse of the collar coordinate**: from the `(u,t,y)`-coordinates reassemble the point
of `E4` with horizontal part `cuspX v u y` and height `collarHeight t (β (cuspX v u y))`. -/
def cuspCollarInv (v : Fin 5) (p : {z : ℝ × ℝ // z ∈ collarLayerDom} × E2) : E4 :=
  mkE4 (cuspX v (p.1 : ℝ × ℝ).1 p.2)
    (collarHeight (p.1 : ℝ × ℝ).2 (beta (cuspX v (p.1 : ℝ × ℝ).1 p.2)))

/-- **The collar box is open**: it is cut out by the continuous conditions
`|(cuspX v u y) i − c i| < δ`. -/
theorem isOpen_cuspCollarBox (v : Fin 5) (c : E3) (δ : ℝ) :
    IsOpen (cuspCollarBox v c δ) := by
  have hc : Continuous (fun w : ℝ × E2 => cuspX v w.1 w.2) := continuous_cuspX v
  have : cuspCollarBox v c δ
      = ⋂ i : Fin 3, {w : ℝ × E2 | |(cuspX v w.1 w.2) i - c i| < δ} := by
    ext w
    simp [cuspCollarBox]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  have hcont : Continuous (fun w : ℝ × E2 => (cuspX v w.1 w.2) i - c i) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hc).sub continuous_const
  have hpre : {w : ℝ × E2 | |(cuspX v w.1 w.2) i - c i| < δ}
      = (fun w : ℝ × E2 => (cuspX v w.1 w.2) i - c i) ⁻¹' Set.Ioo (-δ) δ := by
    ext w
    simp [abs_lt]
  rw [hpre]
  exact isOpen_Ioo.preimage hcont

/-! ### The recovered layer parameter on the collar source, as an explicit formula -/

/-- **The recovered layer parameter of `cuspInvOuter` on the collar source is the explicit
height formula** `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`.  The box conditions
`s < s_J` and `β(x) < s_J` make this number `≥ 1/2`, hence positive, so that the sup norm of
`t • bndOfU …` is `t` itself (`nrm_smul`, `nrm_bndOfU`). -/
theorem cuspInvOuter_nrm_fst_eq (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSource v c δ) :
    nrm (cuspInvOuter v q).1
      = 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log (beta (xOf q)) - Real.log sJ)) := by
  obtain ⟨hbox, hceil⟩ := hq
  obtain ⟨-, hs1, hsJ, -, -⟩ := hbox
  set b : ℝ := beta (xOf q) with hb
  set T : ℝ := 1 + (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) with hT
  have hbpos : 0 < b := by rw [hb]; exact beta_pos _
  have hb_lt_sJ : b < sJ := by
    rw [hb]; exact lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hpe : (cuspInvOuter v q).1 = T • bndOfU (outerU v (xOf q)) := by
    rw [hT, hb]; rfl
  have hden : 2 * (Real.log b - Real.log sJ) < 0 := by
    have h := Real.log_lt_log hbpos hb_lt_sJ
    linarith
  have hnum : Real.log (q 3) - Real.log sJ ≤ 0 := by
    have h := Real.log_le_log hq3pos (le_of_lt hsJ)
    linarith
  have hTpos : 0 < T := by
    have hD : (2 : ℝ) * (Real.log b - Real.log sJ) ≠ 0 := by
      intro h0
      have : Real.log b - Real.log sJ = 0 := by linarith [h0]
      linarith [hden]
    have h1 : T - 1/2 = (Real.log (q 3) - Real.log sJ) / (2 * (Real.log b - Real.log sJ)) := by
      rw [hT]
      rw [show (1 : ℝ) + (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) - 1/2
          = 1/2 + (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) by ring]
      rw [show (1/2 : ℝ) = (Real.log b - Real.log sJ) / (2 * (Real.log b - Real.log sJ)) by
        rw [eq_div_iff hD]; ring]
      rw [← add_div]
      congr 1
      ring
    have h2 : 0 ≤ (Real.log (q 3) - Real.log sJ) / (2 * (Real.log b - Real.log sJ)) :=
      div_nonneg_of_nonpos hnum (le_of_lt hden)
    linarith
  rw [hpe, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos hTpos, hT, hb]

end Work.Cusp
