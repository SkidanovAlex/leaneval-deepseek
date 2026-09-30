/-
# The fold block of the atlas

This file produces, from the *single* named hypothesis `Work.RTOwed.FoldTransLocal`, the element
`Work.RTOwed.foldAnalyticOf (hloc) : Work.RTInstance.FoldAnalytic` of the three analytic facts about
the delivered fold charts `Work.FoldInst.foldChart` — the smoothness and the isometry of their
transitions, and the height bound of their images — i.e. the whole of item 1 of the contract apart
from the local Möbius model itself.

The mathematics assembled here:

* `Work.RTOwed.foldTrans_piece` — the transition of two fold charts, computed on a Voronoi piece,
  is the Möbius transformation of `Work.RTOwed.transMat`;
* `Work.RTOwed.foldTrans_piece_twisted` — its form for a lift translated by a group element, with
  the transported matrix `Work.RTOwed.transMatG`;
* `Work.RTOwed.transPieceLift` — every point of the transition source has such a piece datum;
* the named hypothesis `Work.RTOwed.FoldTransLocal` (`Work.RTOwed.foldTrans_local`) — every point of
  the transition source has an open neighbourhood on which the transition is the Möbius
  transformation of a *single* Lorentz matrix (the pieces of the transition source are glued by
  `Work.RTOwed.foldDr_ratio_flip`, the ratio of the developing matrices agreeing between the two
  classes).

Everything here is the assembly of those facts: `ContDiffOn` follows from the local Möbius models
through `ContDiffWithinAt.congr_of_eventuallyEq`, the isometry from `Work.HypModel.mobius_isometry`
together with the agreement of the total model `Work.RTInstance.uhsModel δ` with the upper half
space metric on the chart images, and the height bound from
`Work.FoldInst.exists_pos_le_foldTheta_height`.
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.FoldTransLocal
import Submission.Work.RTOwed.foldTrans_local
import Submission.Work.RTOwed.foldTrans_piece

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace Matrix
open Bundle

namespace Work.RTOwed

open Work.FoldInst

/-- The height function `q ↦ q 3` of `E4`, as a continuous linear map. -/
def heightCLM : E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) 3

/-- The upper half space is open. -/
theorem isOpen_upperHalfSpace : IsOpen HypModel.upperHalfSpace :=
  isOpen_lt continuous_const heightCLM.continuous

/-! ### The chart values of the fold charts are in the upper half space -/

/-- **The fold chart values have positive height**: `foldTheta i r y` is `coordPerm i` of a Klein
action, and the Klein action of a Lorentz matrix sends the ball into the upper half space. -/
theorem foldTheta_height_pos (i : Fin 98) (r : Fin (foldCodim i) → Bool) {y : E4}
    (hy : y ∈ HypModel.ball) : 0 < (foldTheta i r y) 3 := by
  rw [foldTheta, coordPerm_three]
  exact HypModel.mobiusKlein_mem (foldInst_foldNr_mul_foldDrR_isLorentz i r) hy

/-- **A uniform bound for the chart images**: if δ bounds the heights of all the Voronoi pieces
from below, then it bounds the height of every point of every fold chart target. -/
theorem foldChart_height_le {δ : ℝ}
    (hgt : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ ≤ (foldTheta i r x.2.1) 3) (i : Fin 98) {z : E4}
    (hz : z ∈ (foldChart i).target) : δ ≤ z 3 := by
  have hsrc : (foldChart i).symm z ∈ (foldChart i).source := (foldChart i).map_target hz
  rw [foldChart_source] at hsrc
  obtain ⟨r, x, hx, hxeq⟩ := Set.mem_iUnion.mp hsrc
  have hz' : z = foldTheta i r x.2.1 := by
    have h1 : z = (foldChart i) ((foldChart i).symm z) := ((foldChart i).right_inv hz).symm
    rw [h1, ← hxeq, foldChart_apply i r x hx]
  rw [hz']
  exact hgt i r x hx

/-- **The target of a fold chart lies in the upper half space.** -/
theorem foldChart_target_height_pos (i : Fin 98) {z : E4}
    (hz : z ∈ (foldChart i).target) : 0 < z 3 := by
  have hsrc : (foldChart i).symm z ∈ (foldChart i).source := (foldChart i).map_target hz
  rw [foldChart_source] at hsrc
  obtain ⟨r, x, hx, hxeq⟩ := Set.mem_iUnion.mp hsrc
  have hz' : z = foldTheta i r x.2.1 := by
    have h1 : z = (foldChart i) ((foldChart i).symm z) := ((foldChart i).right_inv hz).symm
    rw [h1, ← hxeq, foldChart_apply i r x hx]
  rw [hz']
  exact foldTheta_height_pos i r (Dvor_subset_ball i r hx)

/-- **The transition source is open.** -/
theorem trans_open (i j : Fin 98) : IsOpen (Trans i j) :=
  ((foldChart i).symm ≫ₕ foldChart j).open_source

/-! ### Smoothness of the transitions -/

/-- **The local Möbius model of a transition is smooth on the transition source at the point.** -/
theorem mobius_contDiffWithinAt (i j : Fin 98) {z : E4} (hz : z ∈ Trans i j)
    {B : Matrix (Fin 5) (Fin 5) ℝ} (hB : HypModel.IsLorentzMat B) :
    ContDiffWithinAt ℝ ∞ (HypModel.mobius B) (Trans i j) z := by
  have hzH : z ∈ HypModel.upperHalfSpace := foldChart_target_height_pos i hz.1
  have hu : HypModel.upperHalfSpace ∈ 𝓝 z := isOpen_upperHalfSpace.mem_nhds hzH
  refine (contDiffWithinAt_iff_contDiffAt ((trans_open i j).mem_nhds hz)).mpr ?_
  refine ContDiffAt.of_le ?_ le_top
  exact (contDiffWithinAt_iff_contDiffAt hu).mp
    ((HypModel.mobius_contDiffOn hB).contDiffWithinAt hzH)

/-- **The transition of two fold charts is `C^∞` at every point of its source.**  This is the local
Möbius model of `Work.RTOwed.foldTrans_local`. -/
theorem transMap_contDiffWithinAt (hloc : FoldTransLocal) (i j : Fin 98) {z : E4}
    (hz : z ∈ Trans i j) :
    ContDiffWithinAt ℝ ∞ (transMap i j) (Trans i j) z := by
  obtain ⟨V, B, hVopen, hzV, hB, hEq⟩ := hloc.localModel i j hz
  refine ContDiffWithinAt.congr_of_eventuallyEq (mobius_contDiffWithinAt i j hz hB) ?_ ?_
  · change ∀ᶠ x in 𝓝[Trans i j] z, transMap i j x = HypModel.mobius B x
    rw [eventually_nhdsWithin_iff]
    refine Filter.eventually_of_mem (hVopen.mem_nhds hzV) ?_
    intro z' hz' hz'T
    exact hEq z' ⟨hz', hz'T⟩
  · exact hEq z ⟨hzV, hz⟩

/-- **The transitions of the fold charts are `C^∞`.** -/
theorem foldTrans_smooth (hloc : FoldTransLocal) : ∀ i j : Fin 98,
    ContDiffOn ℝ ∞ ((foldChart j : Mbar → E4) ∘ (foldChart i).symm)
      ((foldChart i).symm ≫ₕ foldChart j).source :=
  fun i j _z hz => transMap_contDiffWithinAt hloc i j hz

/-! ### The height bounds of the chart images -/

/-- **A uniform strict height bound for the images of the fold charts.** -/
theorem foldTrans_ok (δ : ℝ) (hδ : 0 < δ)
    (hgt : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ < (foldTheta i r x.2.1) 3) :
    ∀ (i : Fin 98) ⦃y : Mbar⦄, y ∈ (foldChart i).source →
      (Work.RTInstance.ChartLayer.uhs δ).ok (foldChart i y) := by
  intro i y hy
  refine ⟨hδ, ?_⟩
  rw [foldChart_source] at hy
  obtain ⟨r, x, hx, hxeq⟩ := Set.mem_iUnion.mp hy
  rw [← hxeq, foldChart_apply i r x hx]
  exact hgt i r x hx

/-! ### The isometry of the transitions -/

/-- **The transitions of the fold charts are isometries of the upper half space model.** -/
theorem foldTrans_iso (hloc : FoldTransLocal) (δ : ℝ) (hδ : 0 < δ)
    (hgt : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ ≤ (foldTheta i r x.2.1) 3) :
    ∀ i j : Fin 98, ∀ ⦃y : Mbar⦄, y ∈ (foldChart i).source → y ∈ (foldChart j).source →
      ∀ u v : E4,
        Work.RTInstance.uhsModel δ (foldChart j y)
          (fderiv ℝ ((foldChart j : Mbar → E4) ∘ (foldChart i).symm) ((foldChart i) y) u)
          (fderiv ℝ ((foldChart j : Mbar → E4) ∘ (foldChart i).symm) ((foldChart i) y) v)
        = Work.RTInstance.uhsModel δ (foldChart i y) u v := by
  intro i j y hyi hyj u v
  rw [show ((foldChart j : Mbar → E4) ∘ (foldChart i).symm) = transMap i j from rfl]
  set z : E4 := foldChart i y with hzdef
  have hzt : z ∈ (foldChart i).target := (foldChart i).map_source hyi
  have hzi : ((foldChart i).symm : E4 → Mbar) z = y := (foldChart i).left_inv hyi
  have hzT : z ∈ Trans i j := by
    rw [Trans]
    refine ⟨hzt, ?_⟩
    change ((foldChart i).symm : E4 → Mbar) z ∈ (foldChart j).source
    rw [hzi]; exact hyj
  obtain ⟨V, B, hVopen, hzV, hB, hEq⟩ := hloc.localModel i j hzT
  have hev : transMap i j =ᶠ[𝓝 z] HypModel.mobius B := by
    refine Filter.eventually_of_mem
      (Filter.inter_mem (hVopen.mem_nhds hzV) ((trans_open i j).mem_nhds hzT)) ?_
    intro z' hz'
    exact hEq z' hz'
  have hfd : fderiv ℝ (transMap i j) z = fderiv ℝ (HypModel.mobius B) z := hev.fderiv_eq
  have hzA : transMap i j z = HypModel.mobius B z := hEq z ⟨hzV, hzT⟩
  have hzj : transMap i j z = foldChart j y := by
    show (foldChart j : Mbar → E4) (((foldChart i).symm : E4 → Mbar) z) = (foldChart j : Mbar → E4) y
    rw [hzi]
  have hzH : δ ≤ z 3 := foldChart_height_le hgt i hzt
  have hTzH : δ ≤ (HypModel.mobius B z) 3 := by
    rw [← hzA, hzj]
    exact foldChart_height_le hgt j ((foldChart j).map_source hyj)
  have hzpos : 0 < z 3 := foldChart_target_height_pos i hzt
  have hmob : HypModel.uhsMetric (HypModel.mobius B z)
      (fderiv ℝ (HypModel.mobius B) z u) (fderiv ℝ (HypModel.mobius B) z v)
      = HypModel.uhsMetric z u v := HypModel.mobius_isometry hB hzpos u v
  have hgoalEq : Work.RTInstance.uhsModel δ ((foldChart j : Mbar → E4) y)
        ((fderiv ℝ (transMap i j) z) u) ((fderiv ℝ (transMap i j) z) v)
      = Work.RTInstance.uhsModel δ z u v := by
    rw [← hzj]
    rw [hzA, hfd]
    calc Work.RTInstance.uhsModel δ (HypModel.mobius B z)
          ((fderiv ℝ (HypModel.mobius B) z) u) ((fderiv ℝ (HypModel.mobius B) z) v)
        = HypModel.uhsMetric (HypModel.mobius B z)
            ((fderiv ℝ (HypModel.mobius B) z) u) ((fderiv ℝ (HypModel.mobius B) z) v) := by
          rw [Work.RTInstance.uhsModel_eq_uhsMetric hδ hTzH]; rfl
      _ = HypModel.uhsMetric z u v := hmob
      _ = Work.RTInstance.uhsModel δ z u v := by
          rw [Work.RTInstance.uhsModel_eq_uhsMetric hδ hzH]; rfl
  exact hgoalEq

/-! ### The fold block of the atlas -/

/-! ### The fold block from the named hypothesis

The three analytic facts of `Work.RTInstance.FoldAnalytic` are proved from the *single* named
hypothesis `Work.RTOwed.FoldTransLocal` (the local Möbius model of a transition); everything else —
the twisted piece formula, the transport, the lifting of a transition point to pieces, the height
bounds — is in this chapter. -/
/-- **THE FOLD BLOCK**: the three analytic facts about the delivered fold charts of `FoldInst`, as
`Work.RTInstance.FoldAnalytic`, from the named hypothesis `Work.RTOwed.FoldTransLocal`. -/
noncomputable def foldAnalyticOf (hloc : FoldTransLocal) : Work.RTInstance.FoldAnalytic :=
  let δ₀ : ℝ := Classical.choose Work.FoldInst.exists_pos_le_foldTheta_height
  let hδ₀ : 0 < δ₀ := (Classical.choose_spec Work.FoldInst.exists_pos_le_foldTheta_height).1
  let hgt₀ : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ₀ ≤ (foldTheta i r x.2.1) 3 :=
    (Classical.choose_spec Work.FoldInst.exists_pos_le_foldTheta_height).2
  let δ : ℝ := δ₀ / 2
  let hδ : 0 < δ := by positivity
  let hgt : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ ≤ (foldTheta i r x.2.1) 3 := by
    intro i r x hx; have := hgt₀ i r x hx; dsimp only [δ]; linarith
  let hgt' : ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ < (foldTheta i r x.2.1) 3 := by
    intro i r x hx; have := hgt₀ i r x hx; dsimp only [δ]; linarith
  { δ := δ
    hδ := hδ
    smooth := foldTrans_smooth hloc
    iso := foldTrans_iso hloc δ hδ hgt
    ok := foldTrans_ok δ hδ hgt' }

/-! ### The fold block, unconditionally

`Work.RTOwed.foldTrans_local` proves the one named hypothesis of the area, so the fold block of the
atlas is unconditional. -/

/-- The named hypothesis `Work.RTOwed.FoldTransLocal` is inhabited, by the proved
`Work.RTOwed.foldTrans_local`. -/
noncomputable def foldLocalInst : FoldTransLocal :=
  ⟨fun i j z hz => Work.RTOwed.foldTrans_local i j hz⟩

/-- **THE FOLD BLOCK**: the three analytic facts about the delivered fold charts of `FoldInst`, as
`Work.RTInstance.FoldAnalytic` — no hypothesis. -/
noncomputable def foldAnalytic : Work.RTInstance.FoldAnalytic :=
  foldAnalyticOf foldLocalInst

end Work.RTOwed
