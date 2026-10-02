import Mathlib
import Submission.Work.ThomBordism.stdHalfBallOrientExists
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.PTGeometric.relLocalisation_injective
import Submission.Work.PTGeometric.isOrientFamily_eq_smul_of_connected
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.ThomBordism.modelHalfOrientation
import Submission.Work.ThomBordism.localGenAux
import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.ThomBordism.ModelBall.stdHalfBallHomeoBall
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the boundary sign of the standard half-ball model

`Work.ThomBordism.stdHalfBallBoundarySign`: for the standard half-ball
`W = {u : ℝ^{m+1} | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}` with its flat face `{u 0 = 0}`, there is a *universal*
`c = ±1` such that for every class `w ∈ H_{m+1}(W, ∂W)` whose local classes at the interior points
are the prescribed standard ones (`Work.ThomBordism.stdIntOrient`), the local class of the boundary
class `hPairδ w` at every point of the flat face is `c` times the standard flat-face generator
`Work.ThomBordism.stdFlatGen`.

## The route (no explicit value of `c` is ever needed)

* The prescribed local classes determine `w` uniquely: with `stdHalfBallCharted` (the charted space
  structure pushed from the closed ball along `ModelBall.stdHalfBallHomeoBall`) and its collar,
  `Work.PTGeometric.relLocalisation_injective` gives that a class with vanishing local classes is
  zero.  (`boundarySign_isFundClass_hPairδ` and `boundarySign_eq_of_localClass_eq` transport the two
  boundary-spelling theorems of the ORIENT area to the `stdHalfBallBdry`-spelling of the excluded
  set.)
* `Work.ThomBordism.stdHalfBallOrientExists` (the companion file) produces a class `w₀` realizing
  the prescribed local classes, so it suffices to treat `w₀`.
* At every point of the flat chart's source both `locClass (hPairδ w₀) y` and `stdFlatGen y`
  generate the local group `H_m(∂W, ∂W∖{y}) ≅ ℤ`, so they differ by a sign `c y = ±1`.
* The function `y ↦ c y` is *locally constant* (`boundarySign_locClass_spread`): on a small coordinate
  ball the two families are the localisations of single classes over the ball, and the localisation
  out of a coordinate ball is injective; the flat chart's source is preconnected, so `c` is constant.

Only the *uniformity* of the sign is used downstream (`w ↦ -w` absorbs the value).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology Manifold ContDiff
open Classical
open Work.PTGeometric

namespace Work.ThomBordism

noncomputable section

/-! ## The flat boundary of the standard half-ball as a charted space -/

/-- Piece 0: a Euclidean charted-space structure on the flat boundary of the standard half-ball. -/
theorem boundarySign_bdryCharted (m : ℕ) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin m)) ↥(stdHalfBallBdry (m + 1))) := by
  classical
  obtain ⟨e1, h1⟩ := ModelBall.stdHalfBallHomeoBall (m + 1)
  have hmem : ∀ u : ↥(stdHalfBall (m + 1)),
      u ∈ stdHalfBallBdry (m + 1)
        ↔ e1 u ∈ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary (Work.Surgery.Disk m) := by
    intro u
    have h1u : ((u : EuclideanSpace ℝ (Fin (m + 1))) 0 = 0 ∨
        ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1)
        ↔ (e1 u : EuclideanSpace ℝ (Fin (m + 1))) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := h1 u
    rw [Work.SignatureBordism.ball_boundary]
    show ((u : EuclideanSpace ℝ (Fin (m + 1))) 0 = 0 ∨
        ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1) ↔ e1 u ∈ Work.SignatureBordism.ballSphere m
    rw [Work.SignatureBordism.mem_ballSphere_iff]
    exact h1u
  exact ⟨((Work.Orient.Boundary.homeomorphRestrict e1 (stdHalfBallBdry (m + 1))
    ((modelWithCornersEuclideanHalfSpace (m + 1)).boundary (Work.Surgery.Disk m)) hmem).symm).chartedSpace⟩

/-- Piece 1a: the boundary class of a relative fundamental class generates the local groups,
in the `stdHalfBallBdry`-spelling of the excluded set. -/
theorem boundarySign_isFundClass_hPairδ {m : ℕ}
    [CompactSpace ↥(stdHalfBall (m + 1))] [T2Space ↥(stdHalfBall (m + 1))]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) ↥(stdHalfBall (m + 1))]
    [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 ↥(stdHalfBall (m + 1))]
    {B : Set ↥(stdHalfBall (m + 1))}
    (hB : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1)) = B)
    (w : (Work.Cohomology.relChains (TopCat.of ↥(stdHalfBall (m + 1))) B).homology (m + 1))
    (hw : Work.Orient.IsRelFundClass (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1) B w) :
    Work.Orient.IsFundClass (TopCat.of ↥B) m
      ((Work.Cohomology.hPairδ (TopCat.of ↥(stdHalfBall (m + 1))) B m).hom w) := by
  subst hB
  exact Work.Orient.Boundary.BoundaryOrientation m (TopCat.of ↥(stdHalfBall (m + 1))) w hw

/-- Piece 1b: a relative class is decided by its local classes (the `stdHalfBallBdry`-spelling). -/
theorem boundarySign_eq_of_localClass_eq {m : ℕ}
    [CompactSpace ↥(stdHalfBall (m + 1))] [T2Space ↥(stdHalfBall (m + 1))]
    [ConnectedSpace ↥(stdHalfBall (m + 1))]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) ↥(stdHalfBall (m + 1))]
    [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 ↥(stdHalfBall (m + 1))]
    {B : Set ↥(stdHalfBall (m + 1))}
    (hB : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1)) = B)
    {u v : (Work.Cohomology.relChains (TopCat.of ↥(stdHalfBall (m + 1))) B).homology (m + 1)}
    (h : ∀ (x : ↥(stdHalfBall (m + 1))) (hx : x ∉ B),
      (HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (m + 1))) B x hx) (m + 1)).hom u
      = (HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (m + 1))) B x hx) (m + 1)).hom v) :
    u = v := by
  subst hB
  have h0 : ∀ (x : ↥(stdHalfBall (m + 1)))
      (hx : x ∉ (modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))),
      (HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (m + 1)))
          ((modelWithCornersEuclideanHalfSpace (m + 1)).boundary ↥(stdHalfBall (m + 1))) x hx)
        (m + 1)).hom (u - v) = 0 := by
    intro x hx
    rw [map_sub, h x hx, sub_self]
  exact sub_eq_zero.mp
    (Work.PTGeometric.relLocalisation_injective (TopCat.of ↥(stdHalfBall (m + 1))) h0)


section ResRelH

/-- Composition of the restrictions of relative classes. -/
theorem boundarySign_resRelH_comp (W : TopCat) (m : ℕ) {A B C : Set W} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    (Work.Orient.resRelH W m h₁).comp (Work.Orient.resRelH W m h₂)
      = Work.Orient.resRelH W m (h₁.trans h₂) := by
  rw [Work.PTGeometric.resRelH_eq W m h₁, Work.PTGeometric.resRelH_eq W m h₂,
    Work.PTGeometric.resRelH_eq W m (h₁.trans h₂)]
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    Work.Orient.relChainsIncl_trans]

/-- The restriction of relative classes does not depend on the proof of the inclusion. -/
theorem boundarySign_resRelH_congr (W : TopCat) (m : ℕ) {A B : Set W} (h h' : A ⊆ B) :
    Work.Orient.resRelH W m h = Work.Orient.resRelH W m h' := by
  conv_lhs => rw [Work.PTGeometric.resRelH_eq W m h]
  conv_rhs => rw [Work.PTGeometric.resRelH_eq W m h']

end ResRelH

/-- **The flat-face local class of a global class is locally constant wherever it equals the flat
generator.** -/
theorem boundarySign_locClass_spread {m : ℕ} (hm : 1 ≤ m)
    [T2Space ↥(stdHalfBallBdry (m + 1))]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) ↥(stdHalfBallBdry (m + 1))]
    (V : (Work.Cohomology.singularChains ℤ (TopCat.of ↥(stdHalfBallBdry (m + 1)))).homology m)
    {y : ↥(stdHalfBallBdry (m + 1))} (hy : y ∈ (stdFlatChart m).source)
    (h0 : Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V y
        = stdFlatGen m hm y hy) :
    ∃ U : Set ↥(stdHalfBallBdry (m + 1)), IsOpen U ∧ y ∈ U ∧
      (∀ z (hz : z ∈ U), ∀ hz' : z ∈ (stdFlatChart m).source,
        Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V z
          = stdFlatGen m hm z hz') := by
  classical
  set e := stdFlatChart m with he
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hy)
  have hρpos : 0 < ρ / 2 := by linarith
  have hcl : Metric.closedBall (e y) (ρ / 2) ⊆ e.target :=
    fun z hz => hρsub (Metric.closedBall_subset_ball (by linarith) hz)
  set K : Set ↥(stdHalfBallBdry (m + 1)) :=
    {z | z ∈ e.source ∧ e z ∈ Metric.closedBall (e y) (ρ / 2)} with hKdef
  have hKsrc : ∀ z ∈ K, z ∈ e.source := fun z hz => hz.1
  have hyK : y ∈ K := ⟨hy, Metric.mem_closedBall_self hρpos.le⟩
  have hKcpt : IsCompact K := by
    have hEq : K = (fun w => e.symm w) '' Metric.closedBall (e y) (ρ / 2) := by
      ext z
      constructor
      · intro hz
        exact ⟨e z, hz.2, e.left_inv hz.1⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨e.map_target (hcl hw), ?_⟩
        rw [e.right_inv (hcl hw)]
        exact hw
    rw [hEq]
    exact (isCompact_closedBall (e y) (ρ / 2)).image_of_continuousOn
      ((e.continuousOn_symm).mono hcl)
  obtain ⟨b, hb⟩ := pieceClassChartTr (W := TopCat.of ↥(stdHalfBallBdry (m + 1))) (N := m) hm
    e K hKcpt hKsrc
  set a := Work.Orient.relClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V K with hadef
  have ha : ∀ (z : ↥(stdHalfBallBdry (m + 1))) (hz : z ∈ K),
      Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
          (Set.singleton_subset_iff.mpr hz) a
        = Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V z :=
    fun z hz => Work.Orient.relClass_restrict (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V hz
  have hGe : Work.PTGeometric.HOF.chartTr e y (hKsrc y hyK)
      (Work.PTGeometric.HOF.eucFam m hm (e y)) = stdFlatGen m hm y hy := rfl
  have hD : Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
      (Set.singleton_subset_iff.mpr hyK) (a - b) = 0 := by
    rw [map_sub, ha y hyK, hb y hyK, hGe, h0]
    exact sub_eq_zero.mpr rfl
  -- the open chart ball
  set U : Set ↥(stdHalfBallBdry (m + 1)) :=
    {z | z ∈ e.source ∧ e z ∈ Metric.ball (e y) (ρ / 2)} with hUdef
  have hUopen : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  have hyU : y ∈ U := ⟨hy, Metric.mem_ball_self hρpos⟩
  have hUK : U ⊆ K := fun z hz => ⟨hz.1, Metric.ball_subset_closedBall hz.2⟩
  -- a coordinate ball inside `U`
  obtain ⟨r, hr, _hball, hsub⟩ := Work.ThomBordism.exists_coordBall_subset (n := m)
    (M := TopCat.of ↥(stdHalfBallBdry (m + 1))) hUopen hyU
  set K' : Set ↥(stdHalfBallBdry (m + 1)) :=
    (chartAt (EuclideanSpace ℝ (Fin m)) y) ⁻¹'
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin m)) y) y) (r / 2) ∩
      (chartAt (EuclideanSpace ℝ (Fin m)) y).source with hK'def
  have hK'coord : Work.ThomBordism.IsCoordBall m (TopCat.of ↥(stdHalfBallBdry (m + 1))) K' :=
    ⟨y, r, hr, _hball, hK'def⟩
  have hyK' : y ∈ K' :=
    ⟨by rw [Set.mem_preimage, Metric.mem_closedBall, dist_self]; linarith,
      mem_chart_source _ y⟩
  have hK'sub : K' ⊆ K := fun z hz => hUK (hsub hz)
  -- the restriction of the difference to `K'` vanishes at `y`
  have hdi : Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
      (Set.singleton_subset_iff.mpr hyK')
      (Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m hK'sub (a - b)) = 0 := by
    rw [← LinearMap.comp_apply, boundarySign_resRelH_comp]
    rw [boundarySign_resRelH_congr (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
      ((Set.singleton_subset_iff.mpr hyK').trans hK'sub) (Set.singleton_subset_iff.mpr hyK)]
    exact hD
  have hD' : Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m hK'sub (a - b) = 0 :=
    (Work.PTGeometric.injective_resRelH_isCoordBall (n := m)
      (W := TopCat.of ↥(stdHalfBallBdry (m + 1))) hm hK'coord hyK')
      (hdi.trans (map_zero _).symm)
  -- the neighbourhood where the equality spreads
  have hsmall : IsOpen ((chartAt (EuclideanSpace ℝ (Fin m)) y).source ∩
      (chartAt (EuclideanSpace ℝ (Fin m)) y) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin m)) y) y) (r / 2)) :=
    (chartAt (EuclideanSpace ℝ (Fin m)) y).isOpen_inter_preimage Metric.isOpen_ball
  have hymem : y ∈ (chartAt (EuclideanSpace ℝ (Fin m)) y).source ∩
      (chartAt (EuclideanSpace ℝ (Fin m)) y) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin m)) y) y) (r / 2) :=
    ⟨mem_chart_source _ y,
      by rw [Set.mem_preimage, Metric.mem_ball, dist_self]; linarith⟩
  refine ⟨_, hsmall, hymem, ?_⟩
  intro z hz hz'
  have hzK' : z ∈ K' := by
    refine ⟨?_, hz.1⟩
    exact Metric.ball_subset_closedBall hz.2
  have hzK : z ∈ K := hK'sub hzK'
  have hzfac : Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
      (Set.singleton_subset_iff.mpr hzK) (a - b) = 0 := by
    have hstep : (Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
        (Set.singleton_subset_iff.mpr hzK'))
        ((Work.Orient.resRelH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m hK'sub) (a - b)) = 0 := by
      rw [hD']
      exact map_zero _
    rw [← LinearMap.comp_apply, boundarySign_resRelH_comp] at hstep
    rw [boundarySign_resRelH_congr (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
      ((Set.singleton_subset_iff.mpr hzK').trans hK'sub) (Set.singleton_subset_iff.mpr hzK)] at hstep
    exact hstep
  have hzval : Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V z
      = stdFlatGen m hm z hz' := by
    have h := hzfac
    rw [map_sub, ha z hzK, hb z hzK] at h
    exact sub_eq_zero.mp h
  exact hzval


theorem stdHalfBallBoundarySign (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (w : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
          (Work.ThomBordism.stdHalfBallBdry (m + 1))).homology (m + 1)),
        (∀ (x : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (hx : x ∈ (Work.ThomBordism.stdIntChart (m + 1)).source),
            (HomologicalComplex.homologyMap
              (Work.Orient.relPunct (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
                (Work.ThomBordism.stdHalfBallBdry (m + 1)) x
                (Work.ThomBordism.stdIntChart_source_notMem (m + 1) hx)) (m + 1)).hom w
              = Work.ThomBordism.stdIntOrient m x hx) →
        ∀ (y : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
          (hy : y ∈ (Work.ThomBordism.stdFlatChart m).source),
            Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
                ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
                  (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w) y
              = c • Work.ThomBordism.stdFlatGen m hm y hy := by
  classical
  obtain ⟨cs, him, hbdry, hcollar, hcpt⟩ := stdHalfBallCharted m
  letI : ChartedSpace (EuclideanHalfSpace (m + 1)) ↥(stdHalfBall (m + 1)) := cs
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ ↥(stdHalfBall (m + 1)) := him
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 ↥(stdHalfBall (m + 1)) :=
    inferInstance
  haveI : CompactSpace ↥(stdHalfBall (m + 1)) := hcpt
  haveI : Nonempty ↥(stdHalfBall (m + 1)) := ⟨⟨0, zero_mem_stdHalfBall (m + 1)⟩⟩
  -- the half-ball is connected
  have hconv : Convex ℝ (stdHalfBall (m + 1)) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_⟩
    · have h1 : ((a • u + b • v : Euc (m + 1)) 0) = a * u 0 + b * v 0 := by
        simp [PiLp.add_apply, PiLp.smul_apply]
      rw [h1]
      nlinarith [hu.1, hv.1]
    · calc ‖(a • u + b • v : Euc (m + 1))‖ ≤ a * ‖u‖ + b * ‖v‖ := by
            calc ‖(a • u + b • v : Euc (m + 1))‖ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
              _ = a * ‖u‖ + b * ‖v‖ := by
                    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                      abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * 1 + b * 1 := by nlinarith [hu.2, hv.2]
        _ = 1 := by linarith
  haveI : PreconnectedSpace ↥(stdHalfBall (m + 1)) :=
    isPreconnected_iff_preconnectedSpace.mp hconv.isPreconnected
  haveI : ConnectedSpace ↥(stdHalfBall (m + 1)) :=
    ConnectedSpace.mk ⟨⟨0, zero_mem_stdHalfBall (m + 1)⟩⟩
  -- a Euclidean charted structure on the flat boundary
  obtain ⟨bcs⟩ := boundarySign_bdryCharted m
  letI : ChartedSpace (EuclideanSpace ℝ (Fin m)) ↥(stdHalfBallBdry (m + 1)) := bcs
  -- the flat chart's source is preconnected and nonempty
  have hballEq : (stdFlatChart m).target = Metric.ball (0 : Euc m) 1 := by
    show stdFlatTarget m = Metric.ball (0 : Euc m) 1
    ext u
    rw [Metric.mem_ball, dist_zero_right]
    show ‖consCLM m ((0 : ℝ), u)‖ < 1 ↔ ‖u‖ < 1
    rw [norm_consCLM_zero]
  have htarget : IsPreconnected (stdFlatChart m).target := by
    rw [hballEq]
    exact (convex_ball (0 : Euc m) (1 : ℝ)).isPreconnected
  have hpre : IsPreconnected (stdFlatChart m).source := by
    have h := htarget.image (f := fun w => (stdFlatChart m).symm w)
      (stdFlatChart m).continuousOn_symm
    have hset : (fun w => (stdFlatChart m).symm w) '' (stdFlatChart m).target
        = (stdFlatChart m).source := by
      rw [show (fun w => (stdFlatChart m).symm w) '' (stdFlatChart m).target
          = ↑(stdFlatChart m).symm '' (stdFlatChart m).symm.source from rfl]
      exact (stdFlatChart m).symm.image_source_eq_target
    rwa [hset] at h
  haveI : PreconnectedSpace ↥((stdFlatChart m).source) :=
    isPreconnected_iff_preconnectedSpace.mp hpre
  have h0ball : (0 : Euc m) ∈ (stdFlatChart m).target := by
    show (0 : Euc m) ∈ stdFlatTarget m
    show ‖consCLM m ((0 : ℝ), (0 : Euc m))‖ < 1
    rw [norm_consCLM_zero]
    norm_num
  have hne : Nonempty ↥((stdFlatChart m).source) :=
    ⟨⟨(stdFlatChart m).symm 0, (stdFlatChart m).map_target h0ball⟩⟩
  -- a class realizing the prescribed local classes
  obtain ⟨w₀, hw₀P, hw₀fund⟩ := stdHalfBallOrientExists m hm
  set V₀ := (Work.Cohomology.hPairδ (TopCat.of ↥(stdHalfBall (m + 1)))
    (stdHalfBallBdry (m + 1)) m).hom w₀ with hV₀
  have hfundV₀ : Work.Orient.IsFundClass
      (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ :=
    boundarySign_isFundClass_hPairδ (m := m) hbdry w₀ hw₀fund
  -- the flat family generates
  have hgenFlat : ∀ (z : ↥(stdHalfBallBdry (m + 1))) (hz : z ∈ (stdFlatChart m).source),
      Submodule.span ℤ ({stdFlatGen m hm z hz} :
        Set (Work.Orient.LocH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m z)) = ⊤ := by
    intro z hz
    show Submodule.span ℤ ({(Work.PTGeometric.HOF.chartTr (stdFlatChart m) z hz
      (Work.PTGeometric.HOF.eucFam m hm ((stdFlatChart m) z)))} : Set _) = ⊤
    exact span_chartTr_eucFam hm (stdFlatChart m) z hz
  -- the action of `ℤ` on the flat generator is injective
  have hinj : ∀ (z : ↥(stdHalfBallBdry (m + 1))) (hz : z ∈ (stdFlatChart m).source)
      (a b : ℤ), a • stdFlatGen m hm z hz = b • stdFlatGen m hm z hz → a = b := by
    intro z hz a b hab
    exact Work.PTGeometric.HOF.coeff_eq_of_smul_eq (hgenFlat z hz)
      (Classical.choice (Work.PTGeometric.nonempty_locH_iso_int m hm
        (TopCat.of ↥(stdHalfBallBdry (m + 1))) z)).toLinearEquiv hab
  -- the sign at each point of the flat chart
  have hex : ∀ (y : ↥(stdHalfBallBdry (m + 1))) (hy : y ∈ (stdFlatChart m).source),
      ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
        Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ y
          = c • stdFlatGen m hm y hy := by
    intro y hy
    obtain ⟨e⟩ := Work.PTGeometric.nonempty_locH_iso_int m hm
      (TopCat.of ↥(stdHalfBallBdry (m + 1))) y
    obtain ⟨c, hc, heq⟩ := Work.PTGeometric.exists_pm_one_smul_eq_of_span_eq_top
      e.toLinearEquiv (hgenFlat y hy) (hfundV₀ y)
    exact ⟨c, hc, heq⟩
  -- the global sign function
  let c : ↥((stdFlatChart m).source) → ℤ := fun y => Classical.choose (hex y.1 y.2)
  have hc_spec : ∀ y : ↥((stdFlatChart m).source), (c y = 1 ∨ c y = -1) ∧
      Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ y.1
        = c y • stdFlatGen m hm y.1 y.2 := fun y => Classical.choose_spec (hex y.1 y.2)
  -- the sign is locally constant
  have hclc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hyc := (hc_spec y).1
    have hyval := (hc_spec y).2
    have hspread : ∃ U : Set ↥(stdHalfBallBdry (m + 1)), IsOpen U ∧ y.1 ∈ U ∧
        (∀ z (hz : z ∈ U), ∀ hz' : z ∈ (stdFlatChart m).source,
          Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ z
            = c y • stdFlatGen m hm z hz') := by
      rcases hyc with h1 | h1
      · have hhyp : Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ y.1
            = stdFlatGen m hm y.1 y.2 := by
          rw [hyval, h1, one_smul]
        obtain ⟨U, hU, hyU, h⟩ := boundarySign_locClass_spread hm V₀ y.2 hhyp
        refine ⟨U, hU, hyU, fun z hz hz' => ?_⟩
        rw [h z hz hz', h1, one_smul]
      · have hhyp : Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m (-V₀) y.1
            = stdFlatGen m hm y.1 y.2 := by
          rw [Work.Orient.locClass_neg, hyval, h1]
          simp
        obtain ⟨U, hU, hyU, h⟩ := boundarySign_locClass_spread hm (-V₀) y.2 hhyp
        refine ⟨U, hU, hyU, fun z hz hz' => ?_⟩
        have hz1 := h z hz hz'
        rw [Work.Orient.locClass_neg] at hz1
        have hz2 : Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ z
            = -(stdFlatGen m hm z hz') := by
          have h := congrArg Neg.neg hz1
          rwa [neg_neg] at h
        rw [hz2, h1]
        simp
    obtain ⟨U, hUo, hyU, hUprop⟩ := hspread
    filter_upwards [(continuous_subtype_val.continuousAt).preimage_mem_nhds
      (hUo.mem_nhds hyU)] with z hz
    have hcz := (hc_spec z).2
    have hzy := hUprop z.1 hz z.2
    have hzy2 : c z • stdFlatGen m hm z.1 z.2 = c y • stdFlatGen m hm z.1 z.2 := by
      rw [← hcz, hzy]
    exact hinj z.1 z.2 (c z) (c y) hzy2
  -- the constant
  obtain ⟨y₀⟩ := hne
  refine ⟨c y₀, (hc_spec y₀).1, ?_⟩
  have hconst : ∀ y : ↥((stdFlatChart m).source), c y = c y₀ :=
    fun y => hclc.apply_eq_of_preconnectedSpace y y₀
  -- the value on `V₀`
  have hV₀val : ∀ (y : ↥(stdHalfBallBdry (m + 1))) (hy : y ∈ (stdFlatChart m).source),
      Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m V₀ y
        = c y₀ • stdFlatGen m hm y hy := by
    intro y hy
    have h1 := (hc_spec ⟨y, hy⟩).2
    rw [hconst ⟨y, hy⟩] at h1
    exact h1
  intro w hwP
  -- `w` is a relative fundamental class
  have hwrel : Work.Orient.IsRelFundClass
      (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1) (stdHalfBallBdry (m + 1)) w := by
    intro x hx
    have hxs : x ∈ (stdIntChart (m + 1)).source := by
      show (x : Euc (m + 1)) ∈ stdIntTarget (m + 1)
      exact (mem_stdHalfBallInterior_iff (m + 1) x).mpr hx
    have hcl := hwP x hxs
    have hspan : Submodule.span ℤ ({Work.ThomBordism.stdIntOrient m x hxs} :
        Set (Work.Orient.LocH (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1) x)) = ⊤ := by
      show Submodule.span ℤ ({(Work.PTGeometric.HOF.chartTr (stdIntChart (m + 1)) x hxs
        (Work.PTGeometric.HOF.eucFam (m + 1) (by omega)
          ((stdIntChart (m + 1)) x)))} : Set _) = ⊤
      exact span_chartTr_eucFam (by omega) (stdIntChart (m + 1)) x hxs
    rw [hcl]
    exact hspan
  -- uniqueness
  have hw_eq : w = w₀ := by
    refine boundarySign_eq_of_localClass_eq (m := m) hbdry (u := w) (v := w₀) ?_
    intro x hx
    have hxs : x ∈ (stdIntChart (m + 1)).source := by
      show (x : Euc (m + 1)) ∈ stdIntTarget (m + 1)
      exact (mem_stdHalfBallInterior_iff (m + 1) x).mpr hx
    exact (hwP x hxs).trans (hw₀P x hxs).symm
  intro y hy
  rw [hw_eq]
  exact hV₀val y hy



end

end Work.ThomBordism
