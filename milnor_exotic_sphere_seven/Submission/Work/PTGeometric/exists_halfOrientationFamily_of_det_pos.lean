import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Boundary
import Submission.Work.Tubular.exists_halfOrientationFamily_euclidean
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.HOFExc
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.PTGeometric.HOFChart
import Submission.Work.PTGeometric.halfBallPiece_image
import Submission.Work.PTGeometric.halfBallPiece_coord_pos
import Submission.Work.PTGeometric.transition_hasFDerivAt
import Submission.Work.PTGeometric.exists_interiorChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.PTGeometric

/-- The **interior chart** at a manifold point: the chart `extChartAt I z`, equipped with the open
source and the open target `interior (extChartAt I z).target`, so that it is an
`OpenPartialHomeomorph` and can be used by the chart-transfer machinery. -/
noncomputable def icChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W] (z : W) :
    OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))) :=
  Classical.choose (Work.PTGeometric.exists_interiorChart n W z)

theorem icChart_coe (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W] (z : W) :
    ⇑(icChart n W z) = extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z :=
  (Classical.choose_spec (Work.PTGeometric.exists_interiorChart n W z)).1

theorem icChart_coe_symm (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W] (z : W) :
    ⇑(icChart n W z).symm = ⇑(extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm :=
  (Classical.choose_spec (Work.PTGeometric.exists_interiorChart n W z)).2.1

theorem icChart_target (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W] (z : W) :
    (icChart n W z).target
      = interior (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).target :=
  (Classical.choose_spec (Work.PTGeometric.exists_interiorChart n W z)).2.2.1

theorem icChart_mem_source (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W] (z x : W)
    (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hxsrc : x ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).source) :
    x ∈ (icChart n W z).source :=
  (Classical.choose_spec (Work.PTGeometric.exists_interiorChart n W z)).2.2.2 x hx hxsrc

/-- **A positive-determinant atlas orients a manifold with boundary: an orientation family.**

`Work.Orient.IsHalfOrientationFamily n W γ` is the local-homology form of an orientation of a
`C^1` `(n+1)`-manifold with boundary `W`: `γ x hx` generates `H_{n+1}(W, W∖{x}; ℤ)` at every
interior point `x`, coherently over coordinate half-balls disjoint from `∂W`.  This is the missing
foundation that the orientation datum `Work.PTGeometric.LevelOrientationDatum` (a field of the last
mile) consumes through `Work.Orient.exists_relFundClass_of_halfOrientation`.

**Route.**  For each interior point `x`, take `γ x` to be the image of the standard generator of
`H_{n+1}(I^{n+1}, I^{n+1}∖0)` under the inverse of the chart `extChartAt I x`.  The standard generator
is available in the form of `Work.Tubular.exists_halfOrientationFamily_euclidean` (the canonical
orientation family of the half-space) and its variants
(`Work.Tubular.exists_halfOrientationFamily_normalDiscSub` shows the chart-wise pattern: a family
built by pushing the model generator along a chart homeomorphism).  Clause (a) of
`IsHalfOrientationFamily` is then by construction.  For clause (b), given a coordinate half-ball
`K = Work.Orient.halfBallPiece (n+1) W z r` that is disjoint from `∂W` (hence inside
`(chartAt z).source`), build the class over `K` from the single chart at `z`: the image of the
standard class of the model half-ball under `chartAt z` inverse.  Its localisation at `x ∈ K` agrees
with `γ x` because the comparison of the two charts, `(extChartAt I x) ∘ (chartAt z).symm`, is a `C^1`
local diffeomorphism at `(extChartAt I z) x` whose derivative has **positive** determinant (the
hypothesis `hdet` at the interior overlap point), and a `C^1` local diffeomorphism with `det > 0` at a
point acts as the identity on the local homology generators.  The latter needs two steps, neither of
which is in the workspace yet: (i) a `C^1` germ at a point and its derivative induce the same map on
`H_{n+1}(B, B∖{x})` for a small ball `B` (the homotopy `f_t(z) = f(t·z)/t`, `t ∈ (0,1]`, with
`f_0 := Df(0)`, continuous at `t = 0` by differentiability; `|f_t(z) - A z| ≤ ½‖A⁻¹‖⁻¹|z|` for small
`|z|` keeps `f_t(z) ≠ 0` for `z ≠ 0`); (ii) a linear isomorphism with `det > 0` fixes the standard
generator — the path in `GL⁺` to the identity (`Work.Thom.exists_path_GL_pos_linear`,
`Work.Thom.Mpun_gaugeEnd_homotopy` specialised to a point base) gives the homotopy in homology. -/
theorem exists_halfOrientationFamily_of_det_pos (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (hdet : ∀ (x y : W), x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      ∀ z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x).target ∩
        (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x).symm ⁻¹'
          (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).source,
      z 0 > 0 →
      (0 : ℝ) < LinearMap.det ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y)
          ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x).symm w)) z) :
            EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) :
    ∃ γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        Work.Orient.LocH W (n + 1) x,
      Work.Orient.IsHalfOrientationFamily n W γ := by
  have hN : 1 ≤ n + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have hmain : ∀ x : W, x ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x).source := by
    intro x
    rw [extChartAt_source]
    exact mem_chart_source (EuclideanHalfSpace (n + 1)) x
  refine ⟨fun x hx => Work.PTGeometric.HOF.chartTr (icChart n W x) x
      (icChart_mem_source n W x x hx (hmain x))
      (Work.PTGeometric.HOF.eucFam (n + 1) hN ((icChart n W x) x)), ?_, ?_⟩
  · intro x hx
    exact Work.Tubular.span_singleton_eq_top_of_surjective
      (Work.PTGeometric.HOF.chartTr (icChart n W x) x
        (icChart_mem_source n W x x hx (hmain x)))
      (Work.PTGeometric.HOF.chartTr_surjective _ _ _)
      (Work.PTGeometric.HOF.eucFam (n + 1) hN _)
      (Work.PTGeometric.HOF.eucFam_gen (n + 1) hN _)
  · intro K hK hKint
    obtain ⟨z, r, hr, hgood, rfl⟩ := hK
    have hznot : z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W :=
      hKint z (Work.Orient.mem_halfBallPiece_center hr)
    -- the interior chart at `z`
    have hecoee := icChart_coe n W z
    have hecoes := icChart_coe_symm n W z
    have hetgt := icChart_target n W z
    -- membership in the source of the piece
    have hcent : z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).source := hmain z
    have hKsrc : ∀ x ∈ Work.Orient.halfBallPiece (n + 1) W z r, x ∈ (icChart n W z).source := by
      intro x hxK
      refine icChart_mem_source n W z x (hKint x hxK) ?_
      rw [extChartAt_source]
      exact hxK.2
    set S : Set (Work.PTGeometric.HOF.Euc (n + 1)) := (icChart n W z) ''
      Work.Orient.halfBallPiece (n + 1) W z r with hS
    have hKcpt : IsCompact (Work.Orient.halfBallPiece (n + 1) W z r) :=
      Work.Orient.halfBallPiece_isCompact z r hr hgood
    have hScomp : IsCompact S := hKcpt.image_of_continuousOn
      ((icChart n W z).continuousOn.mono hKsrc)
    have hSclosed : IsClosed S := hScomp.isClosed
    have hSsub : S ⊆ (icChart n W z).target := by
      rintro y ⟨x, hxK, rfl⟩
      rw [hetgt]
      have hxsrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source := hxK.2
      have hxt : (chartAt (EuclideanHalfSpace (n + 1)) z) x
          ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).target :=
        (chartAt (EuclideanHalfSpace (n + 1)) z).map_source hxsrc
      have hxposz : 0 < ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x) 0 :=
        Work.PTGeometric.halfBallPiece_coord_pos n W z r hr hgood x hxK (hKint x hxK)
      have hpos' : (modelWithCornersEuclideanHalfSpace (n + 1))
          ((chartAt (EuclideanHalfSpace (n + 1)) z) x)
          ∈ interior (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
        have h1 : Set.range (modelWithCornersEuclideanHalfSpace (n + 1))
            = {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ y 0} := range_euclideanHalfSpace (n + 1)
        have h2 : interior ({y : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ y 0})
            = {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 < y 0} := interior_halfSpace 2 0 0
        rw [h1, h2]
        exact hxposz
      have h := (chartAt (EuclideanHalfSpace (n + 1)) z).mem_interior_extend_target
        (I := modelWithCornersEuclideanHalfSpace (n + 1)) hxt hpos'
      rw [hecoee]
      exact h
    have hpc : ∀ z' ∉ Work.PTGeometric.HOF.trace
        (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (icChart n W z).target S,
        (Work.PTGeometric.HOF.eSymmA (icChart n W z)) z'
          ∉ Work.Orient.halfBallPiece (n + 1) W z r := by
      intro z' hz' hzK
      refine hz' ?_
      show (z' : Work.PTGeometric.HOF.Euc (n + 1)) ∈ S
      rw [← (icChart n W z).right_inv z'.2]
      exact ⟨(icChart n W z).symm (z' : Work.PTGeometric.HOF.Euc (n + 1)), hzK, rfl⟩
    refine ⟨Work.PTGeometric.HOF.RelHmapOf (n + 1) (Work.PTGeometric.HOF.eSymmA (icChart n W z))
        (Work.PTGeometric.HOF.trace (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (icChart n W z).target S)
        (Work.Orient.halfBallPiece (n + 1) W z r) hpc
        ((Work.PTGeometric.HOF.excE (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (n + 1)
            (icChart n W z).target (icChart n W z).open_target S hSsub hSclosed).symm
          (Work.PTGeometric.HOF.eucCanon (n + 1) hN S hScomp)), ?_⟩
    intro x hx hxK
    have hxsrc : x ∈ (icChart n W z).source := hKsrc x hxK
    have hxpos : 0 < ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x) 0 :=
      Work.PTGeometric.halfBallPiece_coord_pos n W z r hr hgood x hxK hx
    have hexS : (icChart n W z) x ∈ S := ⟨x, hxK, rfl⟩
    have hexsub : Work.PTGeometric.HOF.punctSet (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
        (icChart n W z).target ((icChart n W z) x)
        ⊆ Work.PTGeometric.HOF.trace (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
          (icChart n W z).target S := by
      intro z' hz'
      show (z' : Work.PTGeometric.HOF.Euc (n + 1)) ∈ S
      rw [show (z' : Work.PTGeometric.HOF.Euc (n + 1)) = (icChart n W z) x from hz']
      exact hexS
    have hxpos' : 0 < ((icChart n W z) x) 0 := by rw [hecoee]; exact hxpos
    have h1 : Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxK)
        (Work.PTGeometric.HOF.RelHmapOf (n + 1) (Work.PTGeometric.HOF.eSymmA (icChart n W z))
          (Work.PTGeometric.HOF.trace (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (icChart n W z).target S)
          (Work.Orient.halfBallPiece (n + 1) W z r) hpc
          ((Work.PTGeometric.HOF.excE (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (n + 1)
              (icChart n W z).target (icChart n W z).open_target S hSsub hSclosed).symm
            (Work.PTGeometric.HOF.eucCanon (n + 1) hN S hScomp)))
        = Work.PTGeometric.HOF.RelHmapOf (n + 1) (Work.PTGeometric.HOF.eSymmA (icChart n W z))
            (Work.PTGeometric.HOF.punctSet (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
              (icChart n W z).target ((icChart n W z) x))
            ({x} : Set W)
            (fun z' hz' => Work.PTGeometric.HOF.eSymmA_pair (icChart n W z) x hxsrc hz')
            (Work.Orient.resRelH (TopCat.of ↥(icChart n W z).target) (n + 1)
              (A := Work.PTGeometric.HOF.punctSet (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
                (icChart n W z).target ((icChart n W z) x))
              (B := Work.PTGeometric.HOF.trace (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (icChart n W z).target S) hexsub
              ((Work.PTGeometric.HOF.excE (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (n + 1)
                  (icChart n W z).target (icChart n W z).open_target S hSsub hSclosed).symm
                (Work.PTGeometric.HOF.eucCanon (n + 1) hN S hScomp))) := by
      have h := LinearMap.congr_fun
        (Work.PTGeometric.HOF.RelHmapOf_resRelH
          (X := TopCat.of ↥(icChart n W z).target) (Y := W) (n := n + 1)
          (Work.PTGeometric.HOF.eSymmA (icChart n W z))
          (K₁ := Work.PTGeometric.HOF.punctSet (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
            (icChart n W z).target ((icChart n W z) x))
          (K₂ := Work.PTGeometric.HOF.trace (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (icChart n W z).target S)
          (K'₁ := ({x} : Set W)) (K'₂ := Work.Orient.halfBallPiece (n + 1) W z r)
          hexsub (Set.singleton_subset_iff.mpr hxK)
          hpc (fun z' hz' => Work.PTGeometric.HOF.eSymmA_pair (icChart n W z) x hxsrc hz'))
        ((Work.PTGeometric.HOF.excE (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (n + 1)
            (icChart n W z).target (icChart n W z).open_target S hSsub hSclosed).symm
          (Work.PTGeometric.HOF.eucCanon (n + 1) hN S hScomp))
      exact h.symm
    have h2 : Work.Orient.resRelH (TopCat.of ↥(icChart n W z).target) (n + 1)
        (A := Work.PTGeometric.HOF.punctSet (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
          (icChart n W z).target ((icChart n W z) x))
        (B := Work.PTGeometric.HOF.trace (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (icChart n W z).target S) hexsub
        ((Work.PTGeometric.HOF.excE (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (n + 1)
            (icChart n W z).target (icChart n W z).open_target S hSsub hSclosed).symm
          (Work.PTGeometric.HOF.eucCanon (n + 1) hN S hScomp))
        = ((Work.PTGeometric.HOF.punctIso (TopCat.of (Work.PTGeometric.HOF.Euc (n + 1))) (n + 1)
            (icChart n W z).target (icChart n W z).open_target ((icChart n W z) x)
            ((icChart n W z).map_source hxsrc) isClosed_singleton).symm)
            (Work.PTGeometric.HOF.eucFam (n + 1) hN ((icChart n W z) x)) := by
      have h := Work.PTGeometric.HOF.resRelH_excE_symm
        (X := TopCat.of (Work.PTGeometric.HOF.Euc (n + 1)))
        (n + 1) (icChart n W z).target (icChart n W z).open_target
        (K₁ := ({(icChart n W z) x} : Set (Work.PTGeometric.HOF.Euc (n + 1))))
        (K₂ := S) (Set.singleton_subset_iff.mpr hexS) hSsub
        (Set.singleton_subset_iff.mpr ((icChart n W z).map_source hxsrc)) isClosed_singleton hSclosed
        (Work.PTGeometric.HOF.eucCanon (n + 1) hN S hScomp)
      rw [Work.PTGeometric.HOF.eucCanon_spec (n + 1) hN S hScomp ((icChart n W z) x) hexS] at h
      exact h
    -- the chart comparison
    have hfun : (fun w : Work.PTGeometric.HOF.Euc (n + 1) =>
          (icChart n W x) ((icChart n W z).symm w))
        = (fun w : Work.PTGeometric.HOF.Euc (n + 1) =>
            (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x)
              ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w)) := by
      funext w
      rw [congrFun (icChart_coe_symm n W z) w, congrFun (icChart_coe n W x)
        ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w)]
    have hpt : (icChart n W z) x
        = (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x :=
      congrFun (icChart_coe n W z) x
    have hmem : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x
        ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).target ∩
          (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm ⁻¹'
            (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x).source :=
      ⟨(extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).map_source
          (by rw [extChartAt_source]; exact hxK.2),
        by
          show (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm
            ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x)
            ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x).source
          rw [(extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).left_inv
            (by rw [extChartAt_source]; exact hxK.2)]
          exact hmain x⟩
    have hdetval : 0 < LinearMap.det
        ((fderiv ℝ (fun w : Work.PTGeometric.HOF.Euc (n + 1) =>
          (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x)
            ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w))
          ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x)
          : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) :=
      hdet z x hznot hx ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x) hmem hxpos
    have hderiv : HasFDerivAt (fun w : Work.PTGeometric.HOF.Euc (n + 1) =>
          (icChart n W x) ((icChart n W z).symm w))
        (fderiv ℝ (fun w : Work.PTGeometric.HOF.Euc (n + 1) =>
            (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x)
              ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w))
          ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x))
        ((icChart n W z) x) := by
      rw [hfun, hpt]
      exact Work.PTGeometric.transition_hasFDerivAt n W z x hxK.2 hxpos
    have h3 := Work.PTGeometric.HOF.chartTr_change (n + 1) hN (icChart n W z) (icChart n W x) x
      hxsrc (icChart_mem_source n W x x hx (hmain x))
      (fderiv ℝ (fun w : Work.PTGeometric.HOF.Euc (n + 1) =>
        (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x)
          ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w))
        ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x))
      hderiv hdetval
    rw [h1, h2]
    show Work.PTGeometric.HOF.chartTr (icChart n W z) x hxsrc
        (Work.PTGeometric.HOF.eucFam (n + 1) hN ((icChart n W z) x))
      = Work.PTGeometric.HOF.chartTr (icChart n W x) x
        (icChart_mem_source n W x x hx (hmain x))
        (Work.PTGeometric.HOF.eucFam (n + 1) hN ((icChart n W x) x))
    exact h3

end Work.PTGeometric
