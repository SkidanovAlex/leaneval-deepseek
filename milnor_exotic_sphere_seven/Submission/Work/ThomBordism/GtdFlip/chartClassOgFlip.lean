import Mathlib
import Submission.Work.ThomBordism.GtdFlip.Flip
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.Orientation.Mpun_gaugeEnd_neg
import Submission.Work.Thom.Mpun_natural_map

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The orientation flip of the tautological bundle acts on the chart Thom class by `-1`

`Work.Thom.localThomOfChart Z k e S W hW` is the explicit local Thom class over the chart cell `W`
of the bundle `Z`: the pullback of the model class `Work.Thom.Mpun k ↥W` along the chart
homeomorphism `chartHomeo : ↥(Z.proj ⁻¹' W) ≃ₜ ↥W × ℝᵏ` (`Work.Thom.localThomOfChart_tau`).

The orientation-reversing automorphism `Work.ThomBordism.Grassmann.ogFlipPiece k m S` of the piece
over the chart cell of the tautological bundle (which keeps the vector of the plane and reverses the
orientation of the plane) reverses the sign of that class.

The proof is the following completely explicit computation.  In the chart coordinates of the piece
the flip reads

  `chartHomeo (ogFlipPiece p) = (ogFlip P, matLin (flipMat k) v)`,  `(P, v) = chartHomeo p`,

i.e. it is the composition of the *base change* `ogFlip` with the constant *gauge* `matLin flipMat`
(`Work.ThomBordism.GtdFlip.hcf_comp`).  The base change does nothing to the model class
(`Work.Thom.Mpun_natural_map`), and a gauge whose determinant is negative everywhere acts by `-1`
(`Work.Thom.Orientation.Mpun_gaugeEnd_neg`, applied to `matLin flipMat`, whose determinant is `-1`).
-/

namespace Work.ThomBordism.GtdFlip

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-- **The orientation flip of a chart cell** `baseSet S` of the oriented Grassmannian: the self-map
of `↥(baseSet S)` induced by `ogFlip` (which preserves each chart cell, `ogFlip_mem_baseSet_iff`). -/
def ogFlipSet (k m : ℕ) (S : Grassmann.ChartIdx k m) :
    C(↥(Grassmann.baseSet S), ↥(Grassmann.baseSet S)) where
  toFun y := ⟨Grassmann.ogFlip k m y, (Grassmann.ogFlip_mem_baseSet_iff S y).mpr y.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((Grassmann.continuous_ogFlip k m).comp continuous_subtype_val) _

@[simp] theorem ogFlipSet_apply (k m : ℕ) (S : Grassmann.ChartIdx k m)
    (y : ↥(Grassmann.baseSet S)) :
    ((ogFlipSet k m S y : ↥(Grassmann.baseSet S)) : Grassmann.OG k m)
      = Grassmann.ogFlip k m (y : Grassmann.OG k m) := rfl

/-! ## The flip is a base change followed by a constant gauge -/

/-- **The first (base) component of the chart description of the flip.** -/
theorem chartHomeo_ogFlipPiece_fst (k m : ℕ) (S : Grassmann.ChartIdx k m)
    (p : ↥((Grassmann.tautologicalBundle k m).proj ⁻¹' Grassmann.baseSet S)) :
    (Work.Thom.chartHomeo (Grassmann.tautologicalBundle k m) k
        (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
        (Grassmann.baseSet S) subset_rfl
      (Grassmann.ogFlipPiece k m S p)).1
    = ogFlipSet k m S ((Work.Thom.chartHomeo (Grassmann.tautologicalBundle k m) k
        (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
        (Grassmann.baseSet S) subset_rfl p)).1 := by
  rw [Work.Thom.chartHomeo_apply, Work.Thom.chartHomeo_apply]
  rfl

/-- **The second (fibre) component of the chart description of the flip**: in the chart `S` the
fibre coordinate is multiplied by `flipMat k`, the matrix of the orientation reversal.  This is
`Work.ThomBordism.Grassmann.localTriv_ogFlipTotal`, stated for the chart homeomorphism instead of
the trivialisation. -/
theorem chartHomeo_ogFlipPiece_snd (k m : ℕ) (S : Grassmann.ChartIdx k m)
    (p : ↥((Grassmann.tautologicalBundle k m).proj ⁻¹' Grassmann.baseSet S)) :
    (Work.Thom.chartHomeo (Grassmann.tautologicalBundle k m) k
        (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
        (Grassmann.baseSet S) subset_rfl
      (Grassmann.ogFlipPiece k m S p)).2
    = Grassmann.matLin (Grassmann.flipMat k)
      ((Work.Thom.chartHomeo (Grassmann.tautologicalBundle k m) k
        (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
        (Grassmann.baseSet S) subset_rfl p)).2 := by
  rw [Work.Thom.chartHomeo_apply, Work.Thom.chartHomeo_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.refl_apply]
  rw [← Grassmann.localTriv_snd_eq S
      ((Grassmann.ogFlipPiece k m S p) : (Grassmann.tautologicalBundle k m).TotalSpace),
    ← Grassmann.localTriv_snd_eq S (p : (Grassmann.tautologicalBundle k m).TotalSpace)]
  exact Grassmann.localTriv_ogFlipTotal S
    (p : (Grassmann.tautologicalBundle k m).TotalSpace) p.2

/-- **The chart description of the flip**: in the coordinates of the chart homeomorphism, the flip
of the piece is the base change `ogFlipSet` composed with the constant gauge `matLin (flipMat k)`. -/
theorem hcf_comp (k m : ℕ) (S : Grassmann.ChartIdx k m) :
    ((Work.Thom.chartHomeo (Grassmann.tautologicalBundle k m) k
        (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
        (Grassmann.baseSet S) subset_rfl) :
        C(↥((Grassmann.tautologicalBundle k m).proj ⁻¹' Grassmann.baseSet S),
          ↥(Grassmann.baseSet S) × Grassmann.Amb k)).comp
      (Grassmann.ogFlipPiece k m S)
    = ((Work.Thom.prodMapA (ogFlipSet k m S) (Grassmann.Amb k)).comp
        (Work.Thom.gaugeEnd (fun _ : ↥(Grassmann.baseSet S) =>
          Grassmann.matLin (Grassmann.flipMat k)) continuous_const)).comp
      ((Work.Thom.chartHomeo (Grassmann.tautologicalBundle k m) k
        (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
        (Grassmann.baseSet S) subset_rfl) :
        C(↥((Grassmann.tautologicalBundle k m).proj ⁻¹' Grassmann.baseSet S),
          ↥(Grassmann.baseSet S) × Grassmann.Amb k)) := by
  apply ContinuousMap.ext
  intro p
  have h := chartHomeo_ogFlipPiece_fst k m S p
  have h2 := chartHomeo_ogFlipPiece_snd k m S p
  simp only [ContinuousMap.comp_apply, Work.Thom.prodMapA_apply, Work.Thom.gaugeEnd_apply]
  exact Prod.ext h h2

/-! ## The gauge part: `matLin (flipMat k)` acts by `-1` on the model class -/

/-- The determinant of the matrix model of `flipMat k` is negative (in positive rank). -/
theorem flipMat_det_neg (k : ℕ) (hk : 1 ≤ k) (Y : Type) (_y : Y) :
    LinearMap.det (Grassmann.matLin (Grassmann.flipMat k)).toLinearMap < 0 := by
  rw [Grassmann.det_matLin, Signs.CoordFlip.flipMat_det (by omega)]
  norm_num

/-- **A base change along a self-map does nothing to the model class**: the pullback of
`Work.Thom.Mpun n Y` along `prodMapA F ℝⁿ` is `Mpun n Y`.  (`Mpun_natural_map` at `B = B' = Y`.) -/
theorem Mpun_prodMapA_self (n : ℕ) (Y : Type) [TopologicalSpace Y] (F : C(Y, Y)) :
    (Work.Thom.relCohMap (Work.Thom.prodMapA F (EuclideanSpace ℝ (Fin n)))
        (Work.Thom.Punct Y n) (Work.Thom.Punct Y n) (fun _ hx => hx) ℤ n).hom
      (Work.Thom.Mpun n Y) = Work.Thom.Mpun n Y := by
  convert Work.Thom.Mpun_natural_map (n := n) F using 2

/-- **The model class of the punctured trivial bundle is multiplied by `-1` by the composite of the
base change `ogFlipSet` and the constant gauge `matLin (flipMat k)`** (whose determinant is negative
everywhere, so that the gauge acts by `-1`). -/
theorem gauge_Mpun (k m : ℕ) (hk : 1 ≤ k) (S : Grassmann.ChartIdx k m)
    (hmem : ∀ p ∈ Work.Thom.Punct ↥(Grassmann.baseSet S) k,
      ((Work.Thom.prodMapA (ogFlipSet k m S) (Grassmann.Amb k)).comp
        (Work.Thom.gaugeEnd (fun _ : ↥(Grassmann.baseSet S) =>
          Grassmann.matLin (Grassmann.flipMat k)) continuous_const)) p ∈
      Work.Thom.Punct ↥(Grassmann.baseSet S) k) :
    (Work.Thom.relCohMap
        ((Work.Thom.prodMapA (ogFlipSet k m S) (Grassmann.Amb k)).comp
          (Work.Thom.gaugeEnd (fun _ : ↥(Grassmann.baseSet S) =>
            Grassmann.matLin (Grassmann.flipMat k)) continuous_const))
        (Work.Thom.Punct ↥(Grassmann.baseSet S) k)
        (Work.Thom.Punct ↥(Grassmann.baseSet S) k) hmem ℤ k).hom
      (Work.Thom.Mpun k ↥(Grassmann.baseSet S))
    = - (Work.Thom.Mpun k ↥(Grassmann.baseSet S)) := by
  have hdet : ∀ y : ↥(Grassmann.baseSet S),
      LinearMap.det ((fun _ : ↥(Grassmann.baseSet S) =>
        Grassmann.matLin (Grassmann.flipMat k)) y).toLinearMap < 0 :=
    fun y => flipMat_det_neg k hk _ y
  have hbij : ∀ y : ↥(Grassmann.baseSet S),
      Function.Bijective ((fun _ : ↥(Grassmann.baseSet S) =>
        Grassmann.matLin (Grassmann.flipMat k)) y) :=
    fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero _ (ne_of_lt (hdet y))
  rw [← Work.Thom.relCohMap_compA_apply
    (A := Work.Thom.Punct ↥(Grassmann.baseSet S) k)
    (B := Work.Thom.Punct ↥(Grassmann.baseSet S) k)
    (C := Work.Thom.Punct ↥(Grassmann.baseSet S) k)
    (Work.Thom.gaugeEnd (fun _ : ↥(Grassmann.baseSet S) =>
      Grassmann.matLin (Grassmann.flipMat k)) continuous_const)
    (Work.Thom.prodMapA (ogFlipSet k m S) (Grassmann.Amb k))
    (Work.Thom.gaugeEnd_mem _ _ hbij) (fun _ hx => hx) hmem ℤ k
    (Work.Thom.Mpun k ↥(Grassmann.baseSet S))]
  rw [Mpun_prodMapA_self k ↥(Grassmann.baseSet S) (ogFlipSet k m S)]
  exact Work.Thom.Orientation.Mpun_gaugeEnd_neg k hk _ continuous_const hdet

/-! ## The main statement -/

theorem chartClassOgFlip (k m : ℕ) (hk : 1 ≤ k) (S : Work.ThomBordism.Grassmann.ChartIdx k m) :
    (Work.Thom.relCohMap (Work.ThomBordism.Grassmann.ogFlipPiece k m S)
        (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k m)
          (Work.ThomBordism.Grassmann.baseSet S))
        (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k m)
          (Work.ThomBordism.Grassmann.baseSet S))
        (Work.ThomBordism.Grassmann.ogFlipPiece_mem k m S) ℤ k).hom
      ((Work.Thom.localThomOfChart (Work.ThomBordism.Grassmann.tautologicalBundle k m) k
          (ContinuousLinearEquiv.refl ℝ (Work.ThomBordism.Grassmann.Amb k)) S
          (Work.ThomBordism.Grassmann.baseSet S) subset_rfl).τ)
    = - ((Work.Thom.localThomOfChart (Work.ThomBordism.Grassmann.tautologicalBundle k m) k
          (ContinuousLinearEquiv.refl ℝ (Work.ThomBordism.Grassmann.Amb k)) S
          (Work.ThomBordism.Grassmann.baseSet S) subset_rfl).τ) := by
  rw [Work.Thom.localThomOfChart_tau]
  let Zb := Work.ThomBordism.Grassmann.tautologicalBundle k m
  let W := Work.ThomBordism.Grassmann.baseSet S
  let Y := ↥(Work.ThomBordism.Grassmann.baseSet S)
  let chc : C(↥(Zb.proj ⁻¹' W), Y × Work.ThomBordism.Grassmann.Amb k) :=
    ((Work.Thom.chartHomeo Zb k (ContinuousLinearEquiv.refl ℝ (Work.ThomBordism.Grassmann.Amb k)) S
      W subset_rfl) : C(↥(Zb.proj ⁻¹' W), Y × Work.ThomBordism.Grassmann.Amb k))
  let flp : C(↥(Zb.proj ⁻¹' W), ↥(Zb.proj ⁻¹' W)) := Work.ThomBordism.Grassmann.ogFlipPiece k m S
  let gφ : C(Y × Work.ThomBordism.Grassmann.Amb k, Y × Work.ThomBordism.Grassmann.Amb k) :=
    (Work.Thom.prodMapA (ogFlipSet k m S) (Work.ThomBordism.Grassmann.Amb k)).comp
      (Work.Thom.gaugeEnd (fun _ : Y => Work.ThomBordism.Grassmann.matLin
        (Work.ThomBordism.Grassmann.flipMat k)) continuous_const)
  have hJmem : ∀ p ∈ Work.Thom.pieceZero Zb W, flp p ∈ Work.Thom.pieceZero Zb W :=
    Work.ThomBordism.Grassmann.ogFlipPiece_mem k m S
  have hcmem : ∀ p ∈ Work.Thom.pieceZero Zb W, chc p ∈ Work.Thom.Punct Y k :=
    Work.Thom.chartHomeo_mem Zb k (ContinuousLinearEquiv.refl ℝ (Work.ThomBordism.Grassmann.Amb k))
      S W subset_rfl
  have hgφmem : ∀ p ∈ Work.Thom.Punct Y k, gφ p ∈ Work.Thom.Punct Y k := by
    intro p hp
    exact Work.Thom.gaugeEnd_mem _ continuous_const
      (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero _
        (ne_of_lt (flipMat_det_neg k hk _ y))) p hp
  have hgf : ∀ p ∈ Work.Thom.pieceZero Zb W, chc (flp p) ∈ Work.Thom.Punct Y k :=
    fun p hp => (Work.Thom.chartHomeo_mem_punct Zb k
      (ContinuousLinearEquiv.refl ℝ (Work.ThomBordism.Grassmann.Amb k)) S W subset_rfl
      (flp p)).mp (hJmem p hp)
  have hgf2 : ∀ p ∈ Work.Thom.pieceZero Zb W, gφ (chc p) ∈ Work.Thom.Punct Y k :=
    fun p hp => hgφmem (chc p) (hcmem p hp)
  have h1 := Work.Thom.relCohMap_compA_apply (A := Work.Thom.pieceZero Zb W)
    (B := Work.Thom.pieceZero Zb W) (C := Work.Thom.Punct Y k) flp chc hJmem hcmem hgf ℤ k
    (Work.Thom.Mpun k Y)
  have hsq : chc.comp flp = gφ.comp chc := hcf_comp k m S
  have h2 : (Work.Thom.relCohMap (chc.comp flp) (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k)
        hgf ℤ k).hom (Work.Thom.Mpun k Y)
      = (Work.Thom.relCohMap (gφ.comp chc) (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k)
        hgf2 ℤ k).hom (Work.Thom.Mpun k Y) :=
    congrArg (fun ψ => ModuleCat.Hom.hom ψ (Work.Thom.Mpun k Y))
      (Work.Thom.relCohMap_congrA (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k) hsq hgf hgf2
        ℤ k)
  have h3 := Work.Thom.relCohMap_compA_apply (A := Work.Thom.pieceZero Zb W)
    (B := Work.Thom.Punct Y k) (C := Work.Thom.Punct Y k) chc gφ hcmem hgφmem hgf2 ℤ k
    (Work.Thom.Mpun k Y)
  have h4 := gauge_Mpun k m hk S hgφmem
  calc (Work.Thom.relCohMap flp (Work.Thom.pieceZero Zb W) (Work.Thom.pieceZero Zb W) hJmem
          ℤ k).hom
        ((Work.Thom.relCohMap chc (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k) hcmem
          ℤ k).hom (Work.Thom.Mpun k Y))
      = (Work.Thom.relCohMap (chc.comp flp) (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k)
          hgf ℤ k).hom (Work.Thom.Mpun k Y) := h1
    _ = (Work.Thom.relCohMap (gφ.comp chc) (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k)
          hgf2 ℤ k).hom (Work.Thom.Mpun k Y) := h2
    _ = (Work.Thom.relCohMap chc (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k) hcmem
          ℤ k).hom ((Work.Thom.relCohMap gφ (Work.Thom.Punct Y k) (Work.Thom.Punct Y k) hgφmem
          ℤ k).hom (Work.Thom.Mpun k Y)) := h3.symm
    _ = (Work.Thom.relCohMap chc (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k) hcmem
          ℤ k).hom (- (Work.Thom.Mpun k Y)) := by rw [h4]
    _ = - ((Work.Thom.relCohMap chc (Work.Thom.pieceZero Zb W) (Work.Thom.Punct Y k) hcmem
          ℤ k).hom (Work.Thom.Mpun k Y)) := map_neg _ _

end

end Work.ThomBordism.GtdFlip
