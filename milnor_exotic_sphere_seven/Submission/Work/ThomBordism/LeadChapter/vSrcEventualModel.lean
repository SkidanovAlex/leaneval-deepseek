import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetCore
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.PTGeometric.flatCoordModel
import Submission.Work.PTGeometric.SourceNull

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The eventual model of the raw level function `vSrc` at a collar point

`Work.ThomBordism.LeadChapter.vSrc` is the raw level function of the source construction
(`(G.coord ⟨srcHf u, _⟩).2` where `srcHf` is the flat source homotopy of the family).  The purpose of
this file is the lemma `vSrcEventualModel`: on a *neighbourhood* of a collar point
`collarPiece G m hpow h a i z`, `vSrc` agrees with the explicit smooth expression

`u ↦ padEuc (tubeNormalCoord (G.emb a.2) (G.chart a.2) (modelEuc G (cZero k) (cOne k) a.1 (equivFin ι a.2) u))`.

This is the "`vSrc = padEuc ∘ tubeNormalCoord ∘ Aff_a`" statement of the S3 guidance
(`LeadChapter/S3_guidance.md`), in the form the derivative computation (`HasFDerivAt (vSrc …)`)
consumes.

The two mathematical inputs are

* `srcHf_eq_alphaFamily_of_clamp` — the collar identity of the flat source homotopy, valid on the
  (open, around a point with `u 0 ≤ 1/2`) region `clamp (u 0) ≤ 1/2`;
* `modelEuc_eq_cubeToEuc` (already in `Work.PTGeometric.flatCoordModel`) — the block model of the
  tube point, i.e. the identification of `modelEuc` with `cubeToEuc` of the block reparametrisation.

No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.LeadChapter

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-- **`modelEuc` only depends on the collar cube point `collPt`** of its argument: the model reads
off the cube coordinates `cubeCoord (k+8) (tail (srcCast ·))` of the source point only. -/
theorem modelEuc_congr_collPt (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ) {y y' : EuclideanSpace ℝ (Fin ((8 + k) + 1))}
    (h : Work.PTGeometric.collPt k y = Work.PTGeometric.collPt k y') :
    Work.PTGeometric.modelEuc G i₀ i₁ k₀ j₀ y = Work.PTGeometric.modelEuc G i₀ i₁ k₀ j₀ y' := by
  have hpt : Work.PTGeometric.modelPoint k i₀ i₁ k₀ j₀ y
      = Work.PTGeometric.modelPoint k i₀ i₁ k₀ j₀ y' := by
    funext m
    simp only [Work.PTGeometric.modelPoint_apply, h]
  simp only [Work.PTGeometric.modelEuc, hpt]

/-- **The collar identity of the flat source homotopy**, in the `clamp` form: as soon as the
homotopy time `1 + clamp (u 0)` is at most `3/2`, the flat source homotopy is the explicit `0`-end
`alphaFamily`, read at the collar cube point `collPt k u` of the source.

This strengthens `Work.PTGeometric.flatSourceHomotopy8_eq_collapse` (which assumes `u 0 ≤ 1/2`,
giving `clamp (u 0) = 0`) to the open condition `clamp (u 0) ≤ 1/2`, which is what makes the
identity hold on a *neighbourhood* of a point with `u 0 ≤ 1/2`. -/
theorem srcHf_eq_alphaFamily_of_clamp (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    {u : EuclideanSpace ℝ (Fin ((8 + k) + 1))}
    (hu : Work.PTGeometric.clamp (u 0) ≤ 1 / 2) :
    Work.ThomBordism.LeadChapter.srcHf G m hpow u
      = Work.PTGeometric.alphaFamily G m (Work.PTGeometric.collPt k u) := by
  have hτ : ((Work.PTGeometric.srcTime (k + 8) (Work.PTGeometric.srcCast k u)
      : Set.Icc (1 : ℝ) 2) : ℝ) ≤ 3 / 2 := by
    rw [Work.PTGeometric.srcTime_coe, Work.PTGeometric.head_srcCast]
    linarith
  exact (Work.PTGeometric.familySource G m hpow).collar
    (Work.PTGeometric.cubeCoord (k + 8) (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u)))
    (Work.PTGeometric.srcTime (k + 8) (Work.PTGeometric.srcCast k u)) hτ

/-- **The eventual model of `vSrc` at a collar point** (the statement this file is for). -/
theorem vSrcEventualModel {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (h : Work.ThomBordism.LeadChapter.BdryId G m hpow)
    (hspec : Work.ThomBordism.LeadChapter.BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : Work.PTGeometric.tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz12 : z 0 ≤ 1 / 2)
    (hne : Work.ThomBordism.LeadChapter.srcHf G m hpow
      (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z) ≠ D.t₀) :
    (fun u : Work.ThomBordism.CofAtlas.ModN k => Work.ThomBordism.LeadChapter.vSrc G m hpow u)
      =ᶠ[nhds (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z)]
      (fun u => Work.PTGeometric.padEuc k G.mU G.hmU
        (Work.PTGeometric.tubeNormalCoord (G.emb a.2) (G.chart a.2)
          (Work.PTGeometric.modelEuc G (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
            (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u))) := by
  classical
  set u₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
    Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z with hu₀
  -- ### the data of the collar point
  have hcol : u₀ 0 = z 0 := by
    rw [hu₀, Work.ThomBordism.LeadChapter.collarPiece_eq]
    show (Work.ThomBordism.LeadChapter.srcOfSpatial k
        (Work.ThomBordism.LeadChapter.spatialMap G m hpow h a i (Work.PTGeometric.tail 8 z))).ofLp 0
      + ((z 0) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0 = z 0
    rw [Work.ThomBordism.LeadChapter.srcOfSpatial_zero, zero_add, PiLp.smul_apply, smul_eq_mul,
      Work.PTGeometric.eZero_apply, mul_one]
  have htail : Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u₀)
      = Work.ThomBordism.LeadChapter.xiCoord G m hpow h a y := by
    rw [hu₀, Work.ThomBordism.LeadChapter.collarPiece_eq,
      Work.ThomBordism.LeadChapter.tail_srcCast_srcOfSpatial_add]
    show Work.ThomBordism.LeadChapter.xiCoord G m hpow h a
        ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm (Work.PTGeometric.tail 8 z))
      = Work.ThomBordism.LeadChapter.xiCoord G m hpow h a y
    rw [hz, (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.left_inv hy]
  have hcollu₀ : Work.PTGeometric.collPt k u₀
      = Work.PTGeometric.cubeCoord (k + 8)
          (Work.ThomBordism.LeadChapter.xiCoord G m hpow h a y) := by
    show Work.PTGeometric.cubeCoord (k + 8)
        (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u₀))
      = Work.PTGeometric.cubeCoord (k + 8)
          (Work.ThomBordism.LeadChapter.xiCoord G m hpow h a y)
    rw [htail]
  have hbs := Work.ThomBordism.LeadChapter.blockStrict G m hpow h hspec a y
  have hA₀ : 1 < (2 : ℝ) ^ ((a.1 : ℕ) + 1) *
      ((Work.PTGeometric.collPt k u₀ (Work.PTGeometric.cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollu₀]; exact hbs.1
  have hB₀ : (2 : ℝ) ^ (a.1 : ℕ) *
      ((Work.PTGeometric.collPt k u₀ (Work.PTGeometric.cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollu₀]; exact hbs.2.1
  have hC₀ : 1 < (2 : ℝ) ^ ((Fintype.equivFin ι a.2 : ℕ) + 1) *
      ((Work.PTGeometric.collPt k u₀ (Work.PTGeometric.cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollu₀]; exact hbs.2.2.1
  have hD₀ : (2 : ℝ) ^ (Fintype.equivFin ι a.2 : ℕ) *
      ((Work.PTGeometric.collPt k u₀ (Work.PTGeometric.cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollu₀]; exact hbs.2.2.2
  have hcoll' : Work.PTGeometric.collPt k
        (Work.ThomBordism.LeadChapter.srcOfSpatial k
          (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u₀)))
      = Work.PTGeometric.collPt k u₀ := by
    show Work.PTGeometric.cubeCoord (k + 8) (Work.PTGeometric.tail (k + 8)
          (Work.PTGeometric.srcCast k (Work.ThomBordism.LeadChapter.srcOfSpatial k
            (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u₀)))))
      = Work.PTGeometric.cubeCoord (k + 8)
          (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u₀))
    rw [Work.ThomBordism.LeadChapter.tail_srcCast_srcOfSpatial]
  have hμ₀ : Work.PTGeometric.modelEuc G (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
        (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u₀ ∈ (G.chart a.2).openTube := by
    have h1 : Work.PTGeometric.modelEuc G (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
        (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u₀
        = Work.ThomBordism.LeadChapter.theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
            (Work.PTGeometric.tail (k + 8) (Work.PTGeometric.srcCast k u₀)) :=
      (modelEuc_congr_collPt G (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
        (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) hcoll').symm
    rw [h1, htail, Work.ThomBordism.LeadChapter.theta_xiCoord_eq_emb G m hpow h hspec a y]
    exact Work.Tubular.TubeChart.mem_openTube (G.chart a.2) y
  -- ### the eventual conditions
  have hEv1 : ∀ᶠ u in nhds u₀, Work.PTGeometric.clamp (u 0) < 1 / 2 :=
    (isOpen_lt (Work.PTGeometric.continuous_clamp.comp (Work.PTGeometric.continuous_coord0 k))
      continuous_const).mem_nhds (by
        change Work.PTGeometric.clamp (u₀.ofLp 0) < 1 / 2
        rw [hcol, Work.PTGeometric.clamp_eq_zero_of_le_half hz12]
        norm_num)
  have hc0 : Continuous fun u : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
      ((Work.PTGeometric.collPt k u (Work.PTGeometric.cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) :=
    (Work.PTGeometric.contMDiff_collPt_apply k (Work.PTGeometric.cZero k)).continuous
  have hc1 : Continuous fun u : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
      ((Work.PTGeometric.collPt k u (Work.PTGeometric.cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) :=
    (Work.PTGeometric.contMDiff_collPt_apply k (Work.PTGeometric.cOne k)).continuous
  have hEvA : ∀ᶠ u in nhds u₀, 1 < (2 : ℝ) ^ ((a.1 : ℕ) + 1) *
      ((Work.PTGeometric.collPt k u (Work.PTGeometric.cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) :=
    (isOpen_lt continuous_const (continuous_const.mul hc0)).mem_nhds hA₀
  have hEvB : ∀ᶠ u in nhds u₀, (2 : ℝ) ^ (a.1 : ℕ) *
      ((Work.PTGeometric.collPt k u (Work.PTGeometric.cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 :=
    (isOpen_lt (continuous_const.mul hc0) continuous_const).mem_nhds hB₀
  have hEvC : ∀ᶠ u in nhds u₀, 1 < (2 : ℝ) ^ ((Fintype.equivFin ι a.2 : ℕ) + 1) *
      ((Work.PTGeometric.collPt k u (Work.PTGeometric.cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) :=
    (isOpen_lt continuous_const (continuous_const.mul hc1)).mem_nhds hC₀
  have hEvD : ∀ᶠ u in nhds u₀, (2 : ℝ) ^ (Fintype.equivFin ι a.2 : ℕ) *
      ((Work.PTGeometric.collPt k u (Work.PTGeometric.cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 :=
    (isOpen_lt (continuous_const.mul hc1) continuous_const).mem_nhds hD₀
  have hEvμ : ∀ᶠ u in nhds u₀, Work.PTGeometric.modelEuc G (Work.PTGeometric.cZero k)
        (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u
      ∈ (G.chart a.2).openTube :=
    ((G.chart a.2).openTube_isOpen.preimage
      (Work.PTGeometric.contMDiff_modelEuc G (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
        (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)).continuous).mem_nhds hμ₀
  -- ### the identity, pointwise where the conditions hold
  filter_upwards [hEv1, hEvA, hEvB, hEvC, hEvD, hEvμ] with u hclamp hA hB hC hD hmu
  have hsrc : Work.ThomBordism.LeadChapter.srcHf G m hpow u
      = Work.PTGeometric.alphaFamily G m (Work.PTGeometric.collPt k u) :=
    srcHf_eq_alphaFamily_of_clamp G m hpow (le_of_lt hclamp)
  have hcollapse : Work.PTGeometric.alphaFamily G m (Work.PTGeometric.collPt k u)
      = (G.rep a.2).collapse (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
          (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u) := by
    have hh := Work.PTGeometric.alphaFamily_eq_collapse_of_block (G := G) m (a.1 : ℕ)
      (Fintype.equivFin ι a.2 : ℕ) (a.1).2 (Fintype.equivFin ι a.2).2 u hA hB hC hD
    rw [show (G.rep ((Fintype.equivFin ι).symm ⟨↑((Fintype.equivFin ι) a.2),
          (Fintype.equivFin ι a.2).2⟩)).collapse
        (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
          (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)
      = (G.rep a.2).collapse (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
          (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)
      from by rw [Equiv.symm_apply_apply]] at hh
    exact hh
  have hgeom : (G.rep a.2).collapse (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
        (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)
      = Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
          (G.g a.2) (G.hg a.2)
          (Work.PTGeometric.reIdx k (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
            (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)) := by
    rw [← Work.PTGeometric.reIdx_comp_finKR k (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
      (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)]
    exact G.isGeom a.2 _
  have hsrcV := hsrc.trans (hcollapse.trans hgeom)
  have heuc : (Work.Tubular.cubeToEuc (8 + k) G.R)
      (Work.PTGeometric.reIdx k (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
        (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u))
      = Work.PTGeometric.modelEuc G (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
          (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u :=
    (Work.PTGeometric.modelEuc_eq_cubeToEuc G (Work.PTGeometric.cZero_ne_cOne k) (a.1 : ℕ)
      (Fintype.equivFin ι a.2 : ℕ) u hA hB hC hD).symm
  have htube : (Work.Tubular.cubeToEuc (8 + k) G.R)
      (Work.PTGeometric.reIdx k (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k)
        (Work.PTGeometric.cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u))
      ∈ (G.chart a.2).openTube := by
    rw [heuc]; exact hmu
  obtain ⟨hneT, hcoord⟩ := G.coord_collapse a.2 (Work.PTGeometric.reIdx k
    (Work.PTGeometric.clipPt k (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k)
      (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)) htube
  have hne' : Work.ThomBordism.LeadChapter.srcHf G m hpow u ≠ D.t₀ :=
    fun hh => hneT (hsrcV.symm.trans hh)
  simp only [Work.ThomBordism.LeadChapter.vSrc, dif_neg hne']
  have hsub : (⟨Work.ThomBordism.LeadChapter.srcHf G m hpow u, hne'⟩ : {x : D.T // x ≠ D.t₀})
      = ⟨Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
          (G.g a.2) (G.hg a.2) (Work.PTGeometric.reIdx k (Work.PTGeometric.clipPt k
            (Work.PTGeometric.cZero k) (Work.PTGeometric.cOne k) (a.1 : ℕ)
            (Fintype.equivFin ι a.2 : ℕ) u)), hneT⟩ := Subtype.ext hsrcV
  rw [hsub, congrArg Prod.snd hcoord, heuc]

end

end Work.ThomBordism.LeadChapter
