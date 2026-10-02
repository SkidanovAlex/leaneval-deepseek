import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.ThomBordism.LeadChapter.thetaInvAux
import Submission.Work.ThomBordism.LeadChapter.ogFrameSO

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.LeadChapter` — the collar chart of the level set (the calculus core of S3)

The differentiability of `collarPiece` with the block frame `[∂_t | dΞ]` as derivative, where `Ξ` is
the spatial map `xiCoord` of the collar chart.  This is the "∃ B" half of
`Work.ThomBordism.LeadChapter.chapter_tubeDet`.

No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open CategoryTheory Work.PTGeometric

namespace Work.ThomBordism.LeadChapter

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-- **The block inequalities at a piece point.** For every piece point `y'` of the piece `a`, the
cube coordinates of the spatial coordinate `xiCoord a y'` lie in the open block
`((a.1), equivFin ι (a.2))` of the two-level concatenation. -/
theorem blockStrict (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι) (y' : (Fam a.2).pt) :
    1 < (2 : ℝ) ^ ((a.1 : ℕ) + 1) *
        ((cubeCoord (k + 8) (xiCoord G m hpow h a y') (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) ∧
      (2 : ℝ) ^ ((a.1 : ℕ)) *
        ((cubeCoord (k + 8) (xiCoord G m hpow h a y') (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 ∧
      1 < (2 : ℝ) ^ ((Fintype.equivFin ι a.2 : ℕ) + 1) *
        ((cubeCoord (k + 8) (xiCoord G m hpow h a y') (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) ∧
      (2 : ℝ) ^ ((Fintype.equivFin ι a.2 : ℕ)) *
        ((cubeCoord (k + 8) (xiCoord G m hpow h a y') (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
  classical
  set x := h.symm ⟨a, y'⟩ with hx
  have hxval : h x = ⟨a, y'⟩ := h.apply_symm_apply ⟨a, y'⟩
  have hcore : flatSourceHomotopy8 (k := k)
      (familySource (D := D) (Fam := Fam) G m hpow).H
      (familySource (D := D) (Fam := Fam) G m hpow).φ (x.1).1 ∈ G.core := x.2.1
  have hzero : (x.1).1 0 = 0 := x.2.2
  obtain ⟨k₀, j₀, hj, iχ, hiχ, hk₀, hξlo, hξhi, hηlo, hηhi, htube, hz⟩ :=
    Work.PTGeometric.exists_block_data (G := G) m hpow (x.1).1 hzero hcore
  -- the outer index is `k₀`
  have hlenOut : (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)).length = m :=
    List.length_ofFn
  have houter : outerStep G m (collPt k (x.1).1) =
      (k₀, upd (cZero k) k₀ (collPt k (x.1).1)) := by
    rw [show outerStep G m (collPt k (x.1).1)
        = genLoopListConcatStep (cZero k)
            (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G))
            (collPt k (x.1).1) from rfl,
      genLoopListConcatStep_eq_block (cZero k) _ _ k₀ (by rw [hlenOut]; exact hk₀) hξlo hξhi,
      blockPt_eq_upd]
  -- the inner index is `j₀`
  have hlenIn : (List.ofFn (blockLoop (D := D) (Fam := Fam) G)).length = Fintype.card ι :=
    List.length_ofFn
  have hne10 : cOne k ≠ cZero k := by
    intro hh; exact absurd (congrArg Fin.val hh) (by simp [cOne, cZero])
  have hηlo' : 1 < (2 : ℝ) ^ (j₀ + 1) *
      (((outerStep G m (collPt k (x.1).1)).2 (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [houter]
    rw [upd_apply_of_ne (cZero k) k₀ (collPt k (x.1).1) hne10]
    exact hηlo
  have hηhi' : (2 : ℝ) ^ j₀ *
      (((outerStep G m (collPt k (x.1).1)).2 (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [houter]
    rw [upd_apply_of_ne (cZero k) k₀ (collPt k (x.1).1) hne10]
    exact hηhi
  have hinner : innerStep G m (collPt k (x.1).1) =
      (j₀, upd (cOne k) j₀ (upd (cZero k) k₀ (collPt k (x.1).1))) := by
    have h := genLoopListConcatStep_eq_block (cOne k)
      (List.ofFn (blockLoop (D := D) (Fam := Fam) G))
      (outerStep G m (collPt k (x.1).1)).2 j₀ (by rw [hlenIn]; exact hj) hηlo' hηhi'
    rw [show innerStep G m (collPt k (x.1).1)
        = genLoopListConcatStep (cOne k)
            (List.ofFn (blockLoop (D := D) (Fam := Fam) G))
            (outerStep G m (collPt k (x.1).1)).2 from rfl, h,
      blockPt_eq_upd, houter]
  -- hspec identifies the two indices
  obtain ⟨hs1, hs2, hs3⟩ := hspec x
  have hstep : ∀ {b : ℕ}, ((a.1 : Fin m) : ℕ) = b → k₀ = b := by
    intro b hb
    have h := hs2
    rw [hxval] at h
    rw [show cubeCoord (k + 8) (tail (k + 8) (srcCast k ((x.1).1)))
        = collPt k (x.1).1 from rfl, houter] at h
    exact h.symm.trans hb
  have hk₀eq : k₀ = (a.1 : ℕ) := hstep rfl
  have hj₀eq : j₀ = (Fintype.equivFin ι a.2 : ℕ) := by
    have h := hs3
    rw [hxval] at h
    rw [show cubeCoord (k + 8) (tail (k + 8) (srcCast k ((x.1).1)))
        = collPt k (x.1).1 from rfl, hinner] at h
    exact h.symm
  have hcoll : collPt k (x.1).1 = cubeCoord (k + 8) (xiCoord G m hpow h a y') := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcoll, ← hk₀eq]; exact hξlo
  · rw [← hcoll, ← hk₀eq]; exact hξhi
  · rw [← hcoll, ← hj₀eq]; exact hηlo
  · rw [← hcoll, ← hj₀eq]; exact hηhi


/-- **The block model is the tube point on the open block**: `theta` agrees with `cubeToEuc` of
`blockTubePoint` at the cube coordinates. -/
theorem theta_eq_cubeToEuc_blockTubePoint (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (hk₀ : k₀ < m) (hj₀ : j₀ < Fintype.card ι) (v : EuclideanSpace ℝ (Fin (k + 8)))
    (hlo : 1 < (2 : ℝ) ^ (k₀ + 1) * ((cubeCoord (k + 8) v (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hhi : (2 : ℝ) ^ k₀ * ((cubeCoord (k + 8) v (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (hlo2 : 1 < (2 : ℝ) ^ (j₀ + 1) *
      ((cubeCoord (k + 8) v (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hhi2 : (2 : ℝ) ^ j₀ * ((cubeCoord (k + 8) v (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1) :
    theta G m k₀ j₀ v =
      Work.Tubular.cubeToEuc (8 + k) G.R (blockTubePoint G m (cubeCoord (k + 8) v)) := by
  have hcoll : collPt k (srcOfSpatial k v) = cubeCoord (k + 8) v := by
    rw [collPt, tail_srcCast_srcOfSpatial]
  have hξlo : 1 < (2 : ℝ) ^ (k₀ + 1) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcoll]; exact hlo
  have hξhi : (2 : ℝ) ^ k₀ *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcoll]; exact hhi
  have hηlo : 1 < (2 : ℝ) ^ (j₀ + 1) *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcoll]; exact hlo2
  have hηhi : (2 : ℝ) ^ j₀ *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcoll]; exact hhi2
  have h1 := modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) k₀ j₀ (srcOfSpatial k v)
    hξlo hξhi hηlo hηhi
  have hclip : clipPt k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v)
      = upd (cOne k) j₀ (upd (cZero k) k₀ (cubeCoord (k + 8) v)) := by
    simp only [clipPt, outerPt, collPt, tail_srcCast_srcOfSpatial]
  have h2 : reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v))
      = blockTubePoint G m (cubeCoord (k + 8) v) :=
    (congrArg (reIdx k) hclip).trans (blockTubePoint_eq_reIdx_upd G m (cubeCoord (k + 8) v) k₀ j₀ hk₀ hj₀ hlo hhi hlo2 hhi2).symm
  rw [theta, h1, h2]

/-- **The block model at a piece point is the piece point**: for every `y'` of the piece `a`, the
model `theta` reads the spatial coordinate `xiCoord a y'` off as the embedding of `y'`. -/
theorem theta_xiCoord_eq_emb (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι) (y' : (Fam a.2).pt) :
    theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y')
      = (G.emb a.2).e y' := by
  have hb := blockStrict G m hpow h hspec a y'
  have h1 := (hspec (h.symm ⟨a, y'⟩)).1
  rw [h.apply_symm_apply] at h1
  refine (theta_eq_cubeToEuc_blockTubePoint G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
    (a.1).2 (Fintype.equivFin ι a.2).2 (xiCoord G m hpow h a y')
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2).trans ?_
  exact h1.symm

/-- **The spatial map is the model inverse composed with the embedding**. -/
theorem xiCoord_eq_thetaInv (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι) (y' : (Fam a.2).pt) :
    xiCoord G m hpow h a y' =
      thetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y') := by
  have hR : 0 < G.R := tube_radius_pos (G := G) a.2
  have hh := theta_xiCoord_eq_emb G m hpow h hspec a y'
  rw [← hh]
  -- the delegated `thetaInvAux` (conjunct 1)
  exact ((thetaInvAux G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) hR).1
    (xiCoord G m hpow h a y')).symm


/-- The chart representative `e_a ∘ φ⁻¹` of the embedding in the chart `i` is `C¹` on the chart's
target. -/
theorem chartRep_hasFDerivAt (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) :
    HasFDerivAt (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
        (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
      (fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
          (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
        ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y))
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) := by
  have hmem : (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 ∈
      IsManifold.maximalAtlas (𝓡 8) 1 (Fam a.2).pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := 1)
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).2
  have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 8) 1
      (fun z => (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm z)
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hmem
  have hcomp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (8 + k))) 1
      (fun z => (G.emb a.2).e ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm z))
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target :=
    (((G.emb a.2).smooth.of_le (by norm_num)).contMDiffOn).comp hsymm (t := Set.univ)
      (fun z _ => Set.mem_univ _)
  have hg : ContDiffOn ℝ 1
      (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
        (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target := hcomp.contDiffOn
  have hc : ContDiffAt ℝ 1
      (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
        (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :=
    hg.contDiffAt ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.open_target.mem_nhds
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.map_source hy))
  exact (hc.differentiableAt (by norm_num)).hasFDerivAt

/-- **The spatial map is differentiable**, with derivative the model inverse composed with the
derivative of the chart representative. -/
theorem hasFDerivAt_spatialMap (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) :
    HasFDerivAt (spatialMap G m hpow h a i)
      ((dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y)).comp
        (fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
            (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
          ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)))
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) := by
  have hR : 0 < G.R := tube_radius_pos (G := G) a.2
  have hθ : theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y)
      = (G.emb a.2).e y := theta_xiCoord_eq_emb G m hpow h hspec a y
  have hΞ : HasFDerivAt (thetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
      (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y))
      ((G.emb a.2).e y) := by
    have hh : HasFDerivAt (thetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
        (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
          (theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y)))
        (theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y)) :=
      (thetaInvAux G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) hR).2.1
        (xiCoord G m hpow h a y)
    rwa [hθ] at hh
  have hpt : (G.emb a.2).e ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)) = (G.emb a.2).e y :=
    congrArg (fun z => (G.emb a.2).e z)
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.left_inv hy)
  rw [← hpt] at hΞ
  have hΨ := chartRep_hasFDerivAt (G := G) m a i y hy
  have hcomp := hΞ.comp ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) hΨ
  rw [hpt] at hcomp
  have hfun : (fun w => thetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
        (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
          (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i) w))
      = spatialMap G m hpow h a i := by
    funext w
    exact (xiCoord_eq_thetaInv G m hpow h hspec a
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm w)).symm
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => (congrFun hfun w).symm))


/-- **The collar chart in coordinates**: the value of `collarPiece` is the source point with the
spatial coordinates of the piece point and the collar coordinate `z 0`. -/
theorem collarPiece_eq (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (z : Work.ThomBordism.CofAtlas.E9) :
    collarPiece G m hpow h a i z
      = srcOfSpatial k (spatialMap G m hpow h a i (tail 8 z)) + (z 0) • eZero := by
  set v : EuclideanSpace ℝ (Fin (k + 8)) := spatialMap G m hpow h a i (tail 8 z) with hv
  set x := h.symm ⟨a, (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm (tail 8 z)⟩ with hx
  have h0 : ((x.1).1) 0 = 0 := x.2.2
  have hu : ((x.1).1) = srcOfSpatial k v := (srcOfSpatial_tail_srcCast (k := k) ((x.1).1) h0).symm
  rw [collarPiece]
  show consVec (z 0) (tailVec ((x.1).1)) = srcOfSpatial k v + (z 0) • eZero
  rw [hu, consVec, tailVec, srcOfSpatial_zero]
  simp

/-- **The collar chart is differentiable**, with derivative the block frame `[∂_t | dΞ]`. -/
theorem hasFDerivAt_collarPiece (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i)
    (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :
    HasFDerivAt (collarPiece G m hpow h a i)
      (collarB k ((dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y)).comp
        (fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
            (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
          ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)))) z := by
  have hΞ := hasFDerivAt_spatialMap G m hpow h hspec a i y hy
  rw [← hz] at hΞ
  have htail : HasFDerivAt (fun z : Work.ThomBordism.CofAtlas.E9 => tail 8 z) (tailCLM 8) z :=
    (tailCLM 8).hasFDerivAt
  have h1 := hΞ.comp z htail
  have h2 := (srcOfSpatialCLM k).hasFDerivAt (x := spatialMap G m hpow h a i (tail 8 z)).comp z h1
  have h3 : HasFDerivAt (fun z : Work.ThomBordism.CofAtlas.E9 => (z 0) • eZero) (collarCLM k) z := by
    have hc := (collarCLM k).hasFDerivAt (x := z)
    have hfun : (⇑(collarCLM k) : Work.ThomBordism.CofAtlas.E9 →
        EuclideanSpace ℝ (Fin ((8 + k) + 1))) = fun z => (z 0) • eZero :=
      funext fun w => collarCLM_apply k w
    rw [hfun] at hc
    exact hc
  have hsum := h2.add h3
  have hfun : (fun z : Work.ThomBordism.CofAtlas.E9 =>
      srcOfSpatial k (spatialMap G m hpow h a i (tail 8 z)) + (z 0) • eZero)
      = collarPiece G m hpow h a i := by
    funext w
    exact (collarPiece_eq G m hpow h a i w).symm
  rw [hz] at hsum
  exact hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun w => (congrFun hfun w).symm))


/-- **The collar chart lands in the level set**: the source homotopy at the collar piece is in the
core of the Thom target. -/
theorem srcHf_collarPiece_mem_core (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz12 : z 0 ≤ 1 / 2) :
    srcHf G m hpow (collarPiece G m hpow h a i z) ∈ G.core := by
  classical
  set S := familySource (D := D) (Fam := Fam) G m hpow with hS
  set j := (Fintype.equivFin ι a.2 : ℕ) with hj
  have hcp := collarPiece_eq (G := G) m hpow h a i z
  -- the collar coordinate of the collar piece
  have hx0 : (collarPiece G m hpow h a i z) 0 ≤ 1 / 2 := by
    rw [hcp]
    show (srcOfSpatial k (spatialMap G m hpow h a i (tail 8 z))).ofLp 0
      + ((z 0) • (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0 ≤ 1 / 2
    rw [srcOfSpatial_zero, zero_add, PiLp.smul_apply, smul_eq_mul, eZero_apply, mul_one]
    exact hz12
  -- its spatial coordinates
  have htail : tail (k + 8) (srcCast k (collarPiece G m hpow h a i z))
      = xiCoord G m hpow h a y := by
    rw [hcp, tail_srcCast_srcOfSpatial_add]
    show xiCoord G m hpow h a ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm (tail 8 z))
      = xiCoord G m hpow h a y
    rw [hz, (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.left_inv hy]
  -- the value of the source homotopy
  have hval : srcHf G m hpow (collarPiece G m hpow h a i z)
      = alphaFamily (D := D) (Fam := Fam) G m
          (cubeCoord (k + 8) (xiCoord G m hpow h a y)) := by
    rw [srcHf,
      flatSourceHomotopy8_eq_collapse (k := k) S.H S.φ (alphaFamily (D := D) (Fam := Fam) G m)
        S.collar hx0, htail]
  rw [hval]
  -- the piece and the block data
  set v := xiCoord G m hpow h a y with hv
  have hb := blockStrict G m hpow h hspec a y
  have hjval : j = j := rfl
  have hcollv : collPt k (srcOfSpatial k v) = cubeCoord (k + 8) v := by
    rw [collPt, tail_srcCast_srcOfSpatial]
  have hIlo : 1 < (2 : ℝ) ^ ((a.1 : ℕ) + 1) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollv]; exact hb.1
  have hIhi : (2 : ℝ) ^ ((a.1 : ℕ)) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollv]; exact hb.2.1
  have hJlo : 1 < (2 : ℝ) ^ (j + 1) *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollv]; exact hb.2.2.1
  have hJhi : (2 : ℝ) ^ j *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollv]; exact hb.2.2.2
  have hpiece : (G.rep a.2).collapse (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))
      = alphaFamily (D := D) (Fam := Fam) G m (cubeCoord (k + 8) v) := by
    have h := alphaFamily_eq_collapse_of_block (G := G) m (a.1 : ℕ) j (a.1).2
      (Fintype.equivFin ι a.2).2 (srcOfSpatial k v) hIlo hIhi hJlo hJhi
    have hiχ : (Fintype.equivFin ι).symm ⟨j, (Fintype.equivFin ι a.2).2⟩ = a.2 :=
      Equiv.symm_apply_apply (Fintype.equivFin ι) a.2
    rw [hiχ] at h
    rw [← h, hcollv]
  rw [← hpiece]
  -- the collapse value is in the core
  have hgeom : (G.rep a.2).collapse
      (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))
      = Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
          (G.g a.2) (G.hg a.2)
          (Work.PTGeometric.reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))) := by
    have h := G.isGeom a.2 (Work.PTGeometric.reIdx k
      (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v)))
    rwa [Work.PTGeometric.reIdx_comp_finKR k
      (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))] at h
  rw [hgeom, G.zero]
  -- the tube point of the block is the embedding of the piece point
  rw [show Work.Tubular.cubeToEuc (8 + k) G.R
      (Work.PTGeometric.reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v)))
      = modelEuc G (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v) from
    (modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) (a.1 : ℕ) j (srcOfSpatial k v)
      hIlo hIhi hJlo hJhi).symm]
  rw [show modelEuc G (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v)
      = theta G m (a.1 : ℕ) j v from rfl, theta_xiCoord_eq_emb G m hpow h hspec a y]
  exact ⟨y, rfl⟩

end

end Work.ThomBordism.LeadChapter
