import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.localHomology_corner
import Submission.Work.Orient.Boundary.halfBallInteriorUnionPoint_model
import Submission.Work.Orient.Boundary.halfBallInteriorUnionPoint_transfer
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Orient.Boundary.injective_localisation_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The vanishing of `H_n(W, W∖(K ∩ W° ∪ {y}))`

`Work.Orient.Boundary.isZero_halfBallInteriorUnionPoint` (Hatcher's local computation at a boundary
point, in the degree one below the top): for a compact space `W` charted in the half-space model, a
boundary point `y` and a coordinate half-ball `K = halfBallPiece (n+1) W y r` around it,

`H_n(W, W ∖ (K ∩ W° ∪ {y})) = 0`.

The route:

* the **flat model** `isZero_relChains_punctured_boundary_halfBall`
  (`Submission/Work/Orient/Boundary/halfBallInteriorUnionPoint_model.lean`): pushing away from the
  boundary point in the half-space;
* the **chart transfer** `isZero_halfBallInteriorUnionPoint_of_model`
  (`…halfBallInteriorUnionPoint_transfer.lean`), giving `H_n(W∖{y}, (W∖{y})∖(K ∩ W°)) = 0`;
* the **long exact sequence of the triple** `(K ∩ W° ∪ {y})ᶜ ⊆ W∖{y} ⊆ W`: its third term
  `H_n(W, W∖{y})` vanishes because `y` is a boundary point
  (`isZero_locH_of_mem_boundary`), and its first term is the "restricted inclusion" model of
  `C_*(W∖{y}, (W∖{y})∖(K ∩ W°))`, identified with the subspace model by
  `Work.Cohomology.relSubPunctured_homology_iso`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **The local homology of a manifold with boundary at a boundary point vanishes in every
degree.**  (`Work.Orient.Boundary.localHomology_corner` is the case `k = n + 1`; the same argument
works in all degrees: the chart identifies the local group with that of the half-space at a point of
the hyperplane, where `Work.Orient.Boundary.halfspace_boundary_isZero` applies.) -/
theorem isZero_locH_of_mem_boundary_all (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {x : W}
    (hx : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (k : ℕ) :
    IsZero (Work.Orient.LocH W k x) := by
  have hb : (modelWithCornersEuclideanHalfSpace (n + 1)).IsBoundaryPoint x := hx
  have h0 : (chartAt (EuclideanHalfSpace (n + 1)) x x).1 0 = 0 := by
    have hce : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x x :
        EuclideanSpace ℝ (Fin (n + 1))) = (chartAt (EuclideanHalfSpace (n + 1)) x x).1 := by
      simp [extChartAt_coe]
    have h1 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x x :
        EuclideanSpace ℝ (Fin (n + 1))) ∈
        frontier (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := hb
    have h2 : (chartAt (EuclideanHalfSpace (n + 1)) x x).1 ∈
        frontier (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
      rw [← hce]; exact h1
    rw [frontier_range_modelWithCornersEuclideanHalfSpace (n + 1)] at h2
    exact h2.symm
  obtain ⟨e1⟩ := locH_iso_halfspace n k W x
  exact IsZero.of_iso (halfspace_boundary_isZero n k (chartAt (EuclideanHalfSpace (n + 1)) x x) h0) e1

/-! ## The flat model, in the chart form -/

/-- The canonical homeomorphism between the punctured half-space `pSpace` (ambient coordinates) and
the punctured half-space as a subtype of `EuclideanHalfSpace`. -/
def puncturedHalfSpaceHomeo (n : ℕ) (c : EuclideanHalfSpace (n + 1)) :
    pSpace n c.1 ≃ₜ ↥{v : EuclideanHalfSpace (n + 1) | v ≠ c} where
  toFun y := ⟨⟨y.1, y.2.1⟩, fun h =>
    y.2.2 (congrArg (fun z : EuclideanHalfSpace (n + 1) => z.1) h)⟩
  invFun v := ⟨(v.1).1, (v.1).2, fun h => v.2 (Subtype.ext h)⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The flat model, in the chart form.**  The vanishing of the ambient model
(`isZero_relChains_punctured_boundary_halfBall`) transported along the canonical homeomorphism. -/
theorem isZero_model_halfspaceForm (n : ℕ) (c : EuclideanHalfSpace (n + 1)) (hc : c.1 0 = 0)
    (ρ : ℝ) (hρ : 0 < ρ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ c})
      {v : {v : EuclideanHalfSpace (n + 1) | v ≠ c} | (v : EuclideanHalfSpace (n + 1)) ∉
        (Work.Orient.halfIncl (n + 1) ⁻¹' Metric.closedBall (Work.Orient.halfIncl (n + 1) c) ρ
          ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0})}).homology n) := by
  classical
  obtain ⟨e⟩ := homeoRelChainsIso (puncturedHalfSpaceHomeo n c) (pSet n c.1 ρ)
    {v : ↥{v : EuclideanHalfSpace (n + 1) | v ≠ c} | (v : EuclideanHalfSpace (n + 1)) ∉
      (Work.Orient.halfIncl (n + 1) ⁻¹' Metric.closedBall (Work.Orient.halfIncl (n + 1) c) ρ
        ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0})}
    (fun y => by
      exact Iff.rfl) n
  exact IsZero.of_iso (isZero_relChains_punctured_boundary_halfBall n c.1 hc ρ hρ) e.symm

/-! ## The main statement -/

/-- **The vanishing input.**  For the coordinate half-ball `K` around the boundary point `y`, the
relative group `H_n(W, W∖(K ∩ W° ∪ {y}))` vanishes. -/
theorem isZero_halfBallInteriorUnionPoint (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) :
    IsZero ((Work.Cohomology.relChains W
      ((((Work.Orient.halfBallPiece (n + 1) W y r) ∩
        {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ∪ {y})ᶜ)).homology n) := by
  classical
  -- the flat model and its transfer
  have hmod := isZero_model_halfspaceForm n ((chartAt (EuclideanHalfSpace (n + 1)) y) y)
    (chartAt_boundary_coord_zero n W hy) (r / 2) (by linarith)
  have htr := isZero_halfBallInteriorUnionPoint_of_model n W y hy r hr hgood hmod
  -- the triple `A ⊆ B ⊆ W`
  set B : Set W := {z : W | z ≠ y} with hBdef
  set P : Set W := (Work.Orient.halfBallPiece (n + 1) W y r) ∩
    {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} with hPdef
  have hAB : (P ∪ {y})ᶜ ⊆ B := fun z hz hyz => hz (Or.inr hyz)
  -- the vanishing of the third term: `y` is a boundary point
  have h3 : IsZero ((Work.Cohomology.relChains W B).homology n) := by
    have hB : B = {z : W | z ≠ y} := rfl
    rw [hB]
    exact isZero_locH_of_mem_boundary_all n W hy n
  -- the vanishing of the first term, via the subspace model of the transfer
  have hset : {z : ↥{z : W | z ≠ y} | (z : W) ∈ (P ∪ {y})ᶜ}
      = {z : ↥{z : W | z ≠ y} | (z : W) ∉ P} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h hP; exact h (Or.inl hP)
    · rintro h (hP | hyz)
      · exact h hP
      · exact z.2 hyz
  have hspace : IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ y})
      {z : ↥{z : W | z ≠ y} | (z : W) ∉ P}).homology n) := htr
  have h1 : IsZero (((Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).X₁).homology n) := by
    obtain ⟨e⟩ := Work.Cohomology.relSubPunctured_homology_iso W y (P ∪ {y})
      (Set.mem_union_right _ rfl) n
    have hsp : IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ y})
        {z : ↥{z : W | z ≠ y} | (z : W) ∈ (P ∪ {y})ᶜ}).homology n) := by
      rw [hset]; exact hspace
    exact IsZero.of_iso hsp e
  -- the long exact sequence of the triple gives the middle
  have hS : (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).ShortExact :=
    Work.Cohomology.relChains_triple_shortExact W (P ∪ {y})ᶜ B hAB
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).g n)) = ⊥ := by
    have hf0 : HomologicalComplex.homologyMap
        (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).f n = 0 :=
      IsZero.eq_zero_of_src h1 _
    have hr := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ n)
    have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).f n)).range = ⊥ := by
      rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero]
    exact hr.symm.trans hrange
  have hinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).g n)) :=
    LinearMap.ker_eq_bot.mp hker
  haveI : Subsingleton (((Work.Cohomology.tripleShort W (P ∪ {y})ᶜ B hAB).X₃).homology n) :=
    ModuleCat.isZero_iff_subsingleton.mp h3
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => hinj (Subsingleton.elim _ _)⟩

end

end Work.Orient.Boundary
