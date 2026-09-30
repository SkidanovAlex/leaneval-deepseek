/-
# The core chart of `M̂` at a cusp, with a local `w`-section `W`

`Work.Cusp.coreCoordM` (`Work.Cusp.Assembly`) is the coordinate inclusion of the core chart of the
`v`-th filling piece into the assembled space `M̂`:

  `coreCoordM a v tor W q = incW v (p(q), [y(q)])`,

where `(p(q), y(q)) = cuspInvCore v q` is the point of the cover `E2 × E2` of the filling piece
whose Cartesian core coordinates are `q`, and `[y(q)]` is the class of the two torus coordinates in
`T_v` (transported by the homeomorphism `tor : a.Torus v ≃ₜ (Fin 2 → AddCircle 1)`).

The point `q` runs over the *core box section*

  `coreBoxSect W = {q : E4 | √(q 0² + q 1²) < 1/2 ∧ (q 2, q 3) ∈ W}`

of the core box, `W ⊆ E2` being an open box of the `w`-coordinates — a *local section* of the
covering `E2 → (ℝ/ℤ)²` in the sense of the hypothesis `hsec`: two points of `E2` whose `wOf`-images
lie in `W` and whose classes in `(ℝ/ℤ)²` agree must be equal.

This file proves that `coreCoordM a v tor W` is an *open embedding* of `coreBoxSect W` into `M̂` and
delivers the resulting chart:

  `∃ Φ : OpenPartialHomeomorph a.Mhat E4, Φ.source = range (coreCoordM a v tor W) ∧
     Φ.target = coreBoxSect W ∧ ∀ q ∈ coreBoxSect W, Φ (coreCoordM a v tor W q) = q`.

## The pieces of the proof

* the class map `cls : E2 → (ℝ/ℤ)²` and the projection `fillProjM` of the cover onto the filling
  piece are *open* maps, being products of the open quotient map `ℝ → ℝ/ℤ` with itself
  (`ccm_isOpenMap_cls`, `ccm_isOpenMap_fillProj`);
* the inverse chart `ccmCoreInv` (i.e. `cuspInvCore` followed by the inclusion of the core stratum
  in the square) is continuous, and its image of the core box section is exactly the open set of the
  cover on which the core coordinates lie in `coreBoxSect W` (`ccmCoreInv_image_eq`); this gives that
  `coreCoordM` is an open map (`ccm_isOpenMap_coreCoordM`);
* the injection `hsec` makes `fillProjM` injective on that set, hence `coreCoordM` injective
  (`ccm_coreCoordM_injective`);
* the layer parameter of a point of the cover with core coordinates in the core box has sup norm
  `< 1` (`ccm_nrm_lt_one`), so its image in `M̂` avoids the glued boundary `‖p‖∞ = 1`; that is what
  makes the image of an open set of the interior of the filling piece open in `M̂`
  (`ccm_isOpen_incW_image`).

The chart is then `(IsOpenEmbedding.toOpenPartialHomeomorph)` of `coreCoordM`, inverted, and
composed with the open embedding `coreBoxSect W ↪ E4`.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.ThetaCore_cuspInvCore
import Submission.Work.Cusp.cuspInvCore_ThetaCore
import Submission.Work.Cusp.ThetaCore_add_int
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.cuspInvCore_continuousOn
import Submission.Work.Cusp.ThetaCore_continuous
import Submission.Work.Cusp.isOpen_coreBox
import Submission.Work.Cusp.isOpen_nrm_lt
import Submission.Work.Space.Split

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

namespace CoreChartM

/-! ### The core box section -/

/-- The section `coreBoxSect W` of the core box lies in the core box. -/
theorem ccm_coreBoxSect_subset_coreBox (W : Set E2) : coreBoxSect W ⊆ coreBox := fun _ hq => hq.1

/-- **The core box section is open** as soon as the `w`-box `W` is: it is the intersection of the
open core box (`isOpen_coreBox`) with the preimage of `W` under the (continuous) map
`q ↦ (q 2, q 3) : E4 → E2`. -/
theorem ccm_isOpen_coreBoxSect (W : Set E2) (hW : IsOpen W) : IsOpen (coreBoxSect W) := by
  have h2 : IsOpen {q : E4 | (!₂[q 2, q 3] : E2) ∈ W} := hW.preimage (by fun_prop)
  exact isOpen_coreBox.inter h2

/-! ### The `w`-coordinates of the inverse core chart -/

/-- `wOf v y` as the pair of its two coordinates. -/
lemma ccm_cons_wOf_eq (v : Fin 5) (y : E2) : (!₂[wOf v y 0, wOf v y 1] : E2) = wOf v y := by
  ext i; fin_cases i <;> rfl

/-- The `w`-coordinates of the `y`-part of the inverse core chart are the last two coordinates
themselves. -/
lemma ccm_wOf_cuspInvCore (v : Fin 5) (q : E4) :
    wOf v (cuspInvCore v q).2 = (!₂[q 2, q 3] : E2) := by
  rw [show (cuspInvCore v q).2 = invY v (!₂[q 2, q 3] : E2) from by
        simp [cuspInvCore, cuspInvInner], wOf_invY]

/-- The last two coordinates of the core chart are the `w`-coordinates of `y`. -/
lemma ccm_thetaCore_coord23 (v : Fin 5) (p y : E2) :
    (!₂[(ThetaCore v p y) 2, (ThetaCore v p y) 3] : E2) = wOf v y := by
  simp [ThetaCore, ccm_cons_wOf_eq]

/-- For a point of the cover whose core coordinates lie in the core box section, the
`w`-coordinates of `y` lie in `W`. -/
lemma ccm_wOf_mem (v : Fin 5) {W : Set E2} {p y : E2}
    (h : ThetaCore v p y ∈ coreBoxSect W) : wOf v y ∈ W := by
  have h2 := h.2
  rwa [ccm_thetaCore_coord23 v p y] at h2

/-! ### Injectivity of `coreCoordM` -/

/-- **`coreCoordM` is injective on the core box section.**  The inclusion `incW v` of the filling
piece is injective, so two points with the same image have the same layer point `p` and the same
class of `y` in the torus; the section hypothesis `hsec` then forces `y = y'`, and `ThetaCore`
recovers `q` from `(p, y)`. -/
theorem ccm_coreCoordM_injective (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Function.Injective (coreCoordM a v tor W) := by
  intro q q' h
  have h1 := a.incW_injective v (by simpa only [coreCoordM] using h)
  have hfst : (cuspInvCore v q.1).1 = (cuspInvCore v q'.1).1 := by
    have := congrArg (fun x : Work.Space.SquarePt × a.Torus v => ((x.1 : Work.Space.SquarePt) : E2)) h1
    simpa using this
  have hsnd : (fun i => ((cuspInvCore v q.1).2 i : AddCircle (1 : ℝ)))
      = (fun i => ((cuspInvCore v q'.1).2 i : AddCircle (1 : ℝ))) := by
    have h2 : tor.symm (fun i => ((cuspInvCore v q.1).2 i : AddCircle (1 : ℝ)))
        = tor.symm (fun i => ((cuspInvCore v q'.1).2 i : AddCircle (1 : ℝ))) :=
      congrArg (fun x : Work.Space.SquarePt × a.Torus v => x.2) h1
    have h3 := congrArg tor h2
    simpa using h3
  have hy : (cuspInvCore v q.1).2 = (cuspInvCore v q'.1).2 :=
    hsec _ _ (by rw [ccm_wOf_cuspInvCore]; exact q.2.2)
      (by rw [ccm_wOf_cuspInvCore]; exact q'.2.2) (fun i => congrFun hsnd i)
  have hp : cuspInvCore v q.1 = cuspInvCore v q'.1 := Prod.ext hfst hy
  have hqq : q.1 = q'.1 := by
    have h4 := congrArg (fun z : E2 × E2 => ThetaCore v z.1 z.2) hp
    simpa [ThetaCore_cuspInvCore v q.1 (ccm_coreBoxSect_subset_coreBox W q.2),
           ThetaCore_cuspInvCore v q'.1 (ccm_coreBoxSect_subset_coreBox W q'.2)] using h4
  exact Subtype.ext hqq

/-! ### The class map `E2 → (ℝ/ℤ)²` and the projection of the cover -/

/-- The class of a real pair in `(ℝ/ℤ)²`. -/
abbrev ccmCls (y : E2) : (Fin 2 → AddCircle (1 : ℝ)) := fun i => ((y i : ℝ) : AddCircle (1 : ℝ))

theorem ccm_continuous_cls : Continuous ccmCls := by fun_prop

/-- **The class map `E2 → (ℝ/ℤ)²` is open**: it is the product of the two open quotient maps
`ℝ → AddCircle 1` (which are local homeomorphisms, `AddCircle.isLocalHomeomorph_coe`) with the
identity of `E2 = PiLp 2 (Fin 2 → ℝ)`. -/
theorem ccm_isOpenMap_cls : IsOpenMap ccmCls := by
  have hcoe : IsOpenMap (fun x : ℝ => ((x : ℝ) : AddCircle (1 : ℝ))) :=
    (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).isOpenMap
  have hpi : IsOpenMap (Pi.map (fun _ : Fin 2 => (fun x : ℝ => ((x : ℝ) : AddCircle (1 : ℝ))))) :=
    IsOpenMap.piMap (fun _ => hcoe) (by simp)
  have hop : IsOpenMap (fun y : E2 => y.ofLp) :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isOpenMap
  exact hpi.comp hop

/-- The projection of the cover `E2 × E2` of the `v`-th filling piece onto the filling piece: the
layer point is the point of the square, the torus coordinates are reduced modulo `ℤ²`. -/
abbrev ccmFillProj (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    Work.Space.SquarePt × E2 → Work.Space.SquarePt × a.Torus v :=
  Prod.map id (tor.symm ∘ ccmCls)

theorem ccm_continuous_fillProj (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) : Continuous (ccmFillProj a v tor) :=
  continuous_fst.prodMk ((tor.symm.continuous.comp ccm_continuous_cls).comp continuous_snd)

/-- **The projection of the cover onto the filling piece is open**: it is the product of the
identity of the square with the open map `tor.symm ∘ ccmCls`. -/
theorem ccm_isOpenMap_fillProj (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) : IsOpenMap (ccmFillProj a v tor) :=
  IsOpenMap.prodMap (IsOpenMap.id (X := Work.Space.SquarePt))
    ((tor.symm.isOpenMap).comp ccm_isOpenMap_cls)

/-! ### The core section of the cover -/

/-- The part of the cover `E2 × E2` of the filling piece whose core coordinates lie in the core
box section `coreBoxSect W`. -/
abbrev ccmCoreSect (v : Fin 5) (W : Set E2) : Set (Work.Space.SquarePt × E2) :=
  {z | ThetaCore v (z.1 : E2) z.2 ∈ coreBoxSect W}

/-- The core chart as a map on the cover: `(p, y) ↦ Θ_v(p, y)`. -/
abbrev ccmCoreTheta (v : Fin 5) : Work.Space.SquarePt × E2 → E4 :=
  fun z => ThetaCore v (z.1 : E2) z.2

theorem ccm_continuous_coreTheta (v : Fin 5) : Continuous (ccmCoreTheta v) :=
  (ThetaCore_continuous v).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- **The core section of the cover is open.** -/
theorem ccm_isOpen_coreSect (v : Fin 5) (W : Set E2) (hW : IsOpen W) :
    IsOpen (ccmCoreSect v W) :=
  (ccm_isOpen_coreBoxSect W hW).preimage (ccm_continuous_coreTheta v)

/-! ### The inverse core chart on the cover -/

/-- The layer point of the inverse core chart lies in the square (its sup norm is `< 1/12`). -/
lemma ccm_cuspInvCore_mem_sq (v : Fin 5) (W : Set E2) (q : {q : E4 // q ∈ coreBoxSect W}) :
    (cuspInvCore v q.1).1 ∈ Work.Space.Sq := by
  have h := cuspInvCore_mem_coreStratum v q.1 (ccm_coreBoxSect_subset_coreBox W q.2)
  simp only [coreStratum, Set.mem_ofPred_eq] at h
  have h1 : nrm (cuspInvCore v q.1).1 < 1 := by linarith
  exact ⟨le_trans (abs_le_nrm _ 0) (le_of_lt h1), le_trans (abs_le_nrm _ 1) (le_of_lt h1)⟩

/-- The layer point of the inverse core chart, as a point of the square. -/
abbrev ccmCoreSqPt (v : Fin 5) (W : Set E2) (q : {q : E4 // q ∈ coreBoxSect W}) :
    Work.Space.SquarePt :=
  ⟨(cuspInvCore v q.1).1, ccm_cuspInvCore_mem_sq v W q⟩

/-- **The inverse core chart on the cover**: `q ↦ (p(q), y(q))`. -/
abbrev ccmCoreInv (v : Fin 5) (W : Set E2) (q : {q : E4 // q ∈ coreBoxSect W}) :
    Work.Space.SquarePt × E2 :=
  (ccmCoreSqPt v W q, (cuspInvCore v q.1).2)

theorem ccm_continuous_cuspInvCore_subtype (v : Fin 5) (W : Set E2) :
    Continuous (fun q : {q : E4 // q ∈ coreBoxSect W} => cuspInvCore v q.1) :=
  (cuspInvCore_continuousOn v).comp_continuous continuous_subtype_val
    (fun q => ccm_coreBoxSect_subset_coreBox W q.2)

theorem ccm_continuous_coreSqPt (v : Fin 5) (W : Set E2) : Continuous (ccmCoreSqPt v W) :=
  Continuous.subtype_mk (continuous_fst.comp (ccm_continuous_cuspInvCore_subtype v W))
    (ccm_cuspInvCore_mem_sq v W)

theorem ccm_continuous_coreInv (v : Fin 5) (W : Set E2) : Continuous (ccmCoreInv v W) :=
  (ccm_continuous_coreSqPt v W).prodMk
    (continuous_snd.comp (ccm_continuous_cuspInvCore_subtype v W))

lemma ccm_coreInv_mem_coreSect (v : Fin 5) (W : Set E2)
    (q : {q : E4 // q ∈ coreBoxSect W}) : ccmCoreInv v W q ∈ ccmCoreSect v W := by
  show ThetaCore v (cuspInvCore v q.1).1 (cuspInvCore v q.1).2 ∈ coreBoxSect W
  rw [ThetaCore_cuspInvCore v q.1 (ccm_coreBoxSect_subset_coreBox W q.2)]
  exact q.2

/-- `ccmCoreInv` is a left inverse of the core chart on the core section. -/
lemma ccm_coreInv_inv (v : Fin 5) (W : Set E2) (z : Work.Space.SquarePt × E2)
    (hz : z ∈ ccmCoreSect v W) : ccmCoreInv v W ⟨ccmCoreTheta v z, hz⟩ = z := by
  have h := cuspInvCore_ThetaCore v (z.1 : E2) z.2
  have h1 : (ccmCoreInv v W ⟨ccmCoreTheta v z, hz⟩).1 = z.1 :=
    Subtype.ext (congrArg (fun w : E2 × E2 => w.1) h)
  have h2 : (ccmCoreInv v W ⟨ccmCoreTheta v z, hz⟩).2 = z.2 :=
    congrArg (fun w : E2 × E2 => w.2) h
  exact Prod.ext h1 h2

/-- The image of the inverse core chart is exactly the core section of the cover. -/
lemma ccm_range_coreInv (v : Fin 5) (W : Set E2) :
    range (ccmCoreInv v W) = ccmCoreSect v W := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩; exact ccm_coreInv_mem_coreSect v W q
  · intro hz; exact ⟨_, ccm_coreInv_inv v W z hz⟩

/-- **`coreCoordM` is the composite of the inverse core chart, the projection of the cover and the
inclusion of the filling piece.** -/
lemma ccm_coreCoordM_eq_comp (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) :
    coreCoordM a v tor W = a.incW v ∘ ccmFillProj a v tor ∘ ccmCoreInv v W := by
  funext q
  simp only [coreCoordM, ccmFillProj, ccmCoreSqPt, Prod.map, Function.comp_def]
  congr 1

/-- **The image of an open set of the core coordinates under the inverse chart is open in the
cover**: it is the intersection of the core section of the cover with the preimage of the open set
under the core chart. -/
lemma ccm_coreInv_image_eq (v : Fin 5) (W : Set E2) (A' : Set E4) :
    ccmCoreInv v W '' ((↑) ⁻¹' A') = ccmCoreSect v W ∩ (ccmCoreTheta v) ⁻¹' A' := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨ccm_coreInv_mem_coreSect v W q, ?_⟩
    show ThetaCore v (cuspInvCore v q.1).1 (cuspInvCore v q.1).2 ∈ A'
    rw [ThetaCore_cuspInvCore v q.1 (ccm_coreBoxSect_subset_coreBox W q.2)]
    exact hq
  · rintro ⟨hz, hzA⟩
    exact ⟨⟨ccmCoreTheta v z, hz⟩, hzA, ccm_coreInv_inv v W z hz⟩

/-! ### The layer parameter of the core section -/

/-- **A point of the cover whose core coordinates lie in the core box has sup norm `< 1`.**  In the
core box the radial coordinate is `< 1/2`, while a layer parameter `≥ 1/2` has radial coordinate
`R₀ − log (collarS) ≥ R₀ − 1/2 = 3` because the collar height is at most `s_J = e^{1/2}`. -/
theorem ccm_nrm_lt_one {v : Fin 5} {p y : E2} (h : ThetaCore v p y ∈ coreBox) : nrm p < 1 := by
  set r := radial v p y with hr
  set θ := thetaAng v p y with hθ
  have h0 : (ThetaCore v p y) 0 = r * Real.cos θ := by simp [ThetaCore, hr, hθ]
  have h1 : (ThetaCore v p y) 1 = r * Real.sin θ := by simp [ThetaCore, hr, hθ]
  rw [coreBox, Set.mem_ofPred_eq, h0, h1] at h
  have h2 : Real.sqrt (r ^ 2) < 1 / 2 := by
    have heq : r ^ 2 = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
      have hs := Real.sin_sq_add_cos_sq θ; nlinarith [hs]
    rw [heq]; exact h
  have hr2 : |r| < 1 / 2 := by rwa [Real.sqrt_sq_eq_abs] at h2
  by_contra hc
  push Not at hc
  have hge : 1 / 2 ≤ nrm p := by linarith
  have hrc : radial v p y = R0 - Real.log (collarS v p y) := radial_collar v p y hge
  have hcl : collarS v p y ≤ sJ := collarS_le_sJ v p y hge
  have hpos : 0 < collarS v p y := by rw [collarS, collarHeight]; exact Real.exp_pos _
  have hlog : Real.log (collarS v p y) ≤ 1 / 2 := by
    calc Real.log (collarS v p y) ≤ Real.log sJ := Real.log_le_log hpos hcl
      _ = 1 / 2 := by rw [sJ, Real.log_exp]
  rw [hr, hrc] at hr2
  have h3 : (3 : ℝ) ≤ R0 - Real.log (collarS v p y) := by rw [R0]; linarith
  have h4 : (0 : ℝ) < R0 - Real.log (collarS v p y) := by linarith
  rw [abs_of_pos h4] at hr2
  linarith

theorem ccm_sqNorm_lt_one (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2)
    {x : Work.Space.SquarePt × a.Torus v} (hx : x ∈ ccmFillProj a v tor '' ccmCoreSect v W) :
    Work.Space.sqNorm x.1 < 1 := by
  rcases hx with ⟨z, hz, rfl⟩
  exact ccm_nrm_lt_one (ccm_coreBoxSect_subset_coreBox W hz)

/-! ### Openness in `M̂` of the interior part of a filling piece -/

/-- **The image of an open set of the interior of the `v`-th filling piece is open in `M̂`.**  The
inclusion `incW v` fails to be open only across the glued boundary `‖p‖∞ = 1`: on the interior
`‖p‖∞ < 1` a point of a filling piece is not identified with any point of `M̄`
(`Assembly.incY_eq_incMbar_iff`), so the traces of the image on the two pieces of the quotient are
empty and the image itself. -/
theorem ccm_isOpen_incW_image (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (S : Set (Work.Space.SquarePt × a.Torus v)) (hS : IsOpen S)
    (hbd : ∀ x ∈ S, Work.Space.sqNorm x.1 < 1) : IsOpen (a.incW v '' S) := by
  rw [a.isOpen_iff_sum]
  refine ⟨?_, ?_⟩
  · have h : {x : a.Mbar | a.incMbar x ∈ a.incW v '' S} = ∅ := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, Set.mem_image]
      rintro ⟨w, hw, hxw⟩
      obtain ⟨hx, hgl⟩ := a.incY_eq_incMbar_iff.mp hxw
      have h1 : Work.Space.sqNorm w.1 = 1 := by
        have h3 := (a.glue ⟨x, hx⟩).2
        rw [hgl] at h3
        exact h3
      have h2 := hbd w hw
      linarith
    rw [h]
    exact isOpen_empty
  · have h : {y : a.Y | a.incY y ∈ a.incW v '' S} = Sigma.mk v '' S := by
      ext y
      constructor
      · rintro ⟨w, hw, hyw⟩
        obtain ⟨v', q⟩ := y
        have h1 : (⟨v', q⟩ : a.Y) = ⟨v, w⟩ := a.incY_injective hyw.symm
        cases h1
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    rw [h]
    exact (Topology.IsOpenEmbedding.sigmaMk (i := v)).isOpen_iff_image_isOpen.mp hS

/-! ### Openness of the image of `coreCoordM` -/

/-- The image of `coreCoordM` is the image of the core section of the cover under the inclusion of
the filling piece. -/
lemma ccm_range_coreCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) :
    range (coreCoordM a v tor W) = a.incW v '' (ccmFillProj a v tor '' ccmCoreSect v W) := by
  rw [ccm_coreCoordM_eq_comp a v tor W, Set.range_comp, Set.range_comp, ccm_range_coreInv]

theorem ccm_isOpen_range_coreCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W) :
    IsOpen (range (coreCoordM a v tor W)) := by
  rw [ccm_range_coreCoordM a v tor W]
  exact ccm_isOpen_incW_image a v _
    (ccm_isOpenMap_fillProj a v tor _ (ccm_isOpen_coreSect v W hW))
    (fun x hx => ccm_sqNorm_lt_one a v tor W hx)

/-! ### Openness of `coreCoordM` -/

/-- **`coreCoordM` is an open map.**  For an open set `A` of the core box section,
`coreCoordM '' A = incW v '' (fillProjM '' (ccmCoreInv '' A))`: the middle set is open (the inverse
chart is open as a map — `ccm_coreInv_image_eq` — and the projection of the cover is an open map),
and the outer image is open because the layer parameter is `< 1` on it
(`ccm_isOpen_incW_image`). -/
theorem ccm_isOpenMap_coreCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W) :
    IsOpenMap (coreCoordM a v tor W) := by
  rw [ccm_coreCoordM_eq_comp a v tor W]
  intro A hA
  rw [Set.image_comp, Set.image_comp]
  have h1 : IsOpen (ccmCoreInv v W '' A) := by
    obtain ⟨A', hA', rfl⟩ := isOpen_induced_iff.mp hA
    rw [ccm_coreInv_image_eq]
    exact (ccm_isOpen_coreSect v W hW).inter (hA'.preimage (ccm_continuous_coreTheta v))
  have h2 : IsOpen (ccmFillProj a v tor '' (ccmCoreInv v W '' A)) :=
    ccm_isOpenMap_fillProj a v tor _ h1
  exact ccm_isOpen_incW_image a v _ h2 (fun x hx => by
    rcases hx with ⟨z, hz, rfl⟩
    rcases hz with ⟨q, -, rfl⟩
    exact ccm_sqNorm_lt_one a v tor W ⟨ccmCoreInv v W q, ccm_coreInv_mem_coreSect v W q, rfl⟩)

end CoreChartM

open CoreChartM

/-- **Existence of the core chart `Φ_v` of the `v`-th cusp on `M̂`.**  The coordinate inclusion
`coreCoordM a v tor W` of the core box section `coreBoxSect W` (the core disk `r < 1/2` cut by the
`w`-box `W`) into `M̂` is an open embedding, and the requested chart is its inverse (composed with
the open embedding `coreBoxSect W ↪ E4`). -/
theorem exists_coreChartM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    ∃ Φ : OpenPartialHomeomorph a.Mhat E4,
      Φ.source = coreCoordM a v tor W '' (Set.univ : Set {q : E4 // q ∈ coreBoxSect W}) ∧
      Φ.target = coreBoxSect W ∧
      ∀ q (hq : q ∈ coreBoxSect W), Φ (coreCoordM a v tor W ⟨q, hq⟩) = q := by
  classical
  by_cases hne : (coreBoxSect W).Nonempty
  · have hne' : Nonempty {q : E4 // q ∈ coreBoxSect W} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    have hemb : Topology.IsOpenEmbedding (coreCoordM a v tor W) :=
      Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        (by rw [ccm_coreCoordM_eq_comp a v tor W]
            exact (a.continuous_incW v).comp
              ((ccm_continuous_fillProj a v tor).comp (ccm_continuous_coreInv v W)))
        (ccm_coreCoordM_injective a v tor W hsec) (ccm_isOpenMap_coreCoordM a v tor W hW)
    have hcoe : Topology.IsOpenEmbedding ((↑) : {q : E4 // q ∈ coreBoxSect W} → E4) :=
      IsOpen.isOpenEmbedding_subtypeVal (ccm_isOpen_coreBoxSect W hW)
    refine ⟨(IsOpenEmbedding.toOpenPartialHomeomorph (coreCoordM a v tor W) hemb).symm.trans
      (IsOpenEmbedding.toOpenPartialHomeomorph _ hcoe), ?_, ?_, ?_⟩
    · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        IsOpenEmbedding.toOpenPartialHomeomorph_target,
        IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
      exact Set.image_univ.symm
    · simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
        IsOpenEmbedding.toOpenPartialHomeomorph_source,
        IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_val, Set.preimage_univ,
        Set.inter_univ]
    · intro q hq
      rw [OpenPartialHomeomorph.trans_apply]
      have h1 : (IsOpenEmbedding.toOpenPartialHomeomorph (coreCoordM a v tor W) hemb).symm
          (coreCoordM a v tor W ⟨q, hq⟩) = ⟨q, hq⟩ :=
        IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _
      rw [h1, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  · have hMb : Nonempty a.Mbar := (inferInstance : ConnectedSpace a.Mbar).toNonempty
    have hU : coreCoordM a v tor W '' (Set.univ : Set {q : E4 // q ∈ coreBoxSect W}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨q, -, -⟩
      exact hne ⟨q.1, q.2⟩
    refine ⟨{ toFun := fun _ => 0
              invFun := fun _ => a.incMbar hMb.some
              source := coreCoordM a v tor W '' (Set.univ : Set {q : E4 // q ∈ coreBoxSect W})
              target := coreBoxSect W
              map_source' := fun x hx => by rw [hU] at hx; exact absurd hx (Set.notMem_empty x)
              map_target' := fun x hx => (hne ⟨x, hx⟩).elim
              left_inv' := fun x hx => by rw [hU] at hx; exact absurd hx (Set.notMem_empty x)
              right_inv' := fun x hx => (hne ⟨x, hx⟩).elim
              continuousOn_toFun := by rw [hU]; exact continuous_const.continuousOn
              continuousOn_invFun := continuous_const.continuousOn
              open_source := by rw [hU]; exact isOpen_empty
              open_target := ccm_isOpen_coreBoxSect W hW }, rfl, rfl,
            fun q hq => (hne ⟨q, hq⟩).elim⟩

end Work.Cusp
