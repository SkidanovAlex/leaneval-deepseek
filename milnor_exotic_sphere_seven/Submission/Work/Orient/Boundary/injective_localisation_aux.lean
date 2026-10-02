import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.halfBallPuncturedCore
import Submission.Work.Orient.Boundary.isZero_punctured_halfBall_of_model
import Submission.Work.Orient.Boundary.localHomology_corner
import Submission.Work.Orient.Boundary.HalfRestrictIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Supporting lemmas for the injectivity of the localisation out of a boundary half-ball

The triple-sequence criterion for injectivity, the assembly of the localisation from the vanishing
of the punctured pair, and the two chart facts used to instantiate the flat model statement.
The main theorem lives in `Submission.Work.Orient.Boundary.injective_localisation_of_halfBallInterior`.
-/

namespace Work.Orient.Boundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

section Helpers


/-! ## The triple-sequence criterion for injectivity -/

/-- **Injectivity of the enlargement map out of the homology sequence of a triple.**

If the "first" term `coker (inclChainsSub X A B h)` of the triple sequence `A ⊆ B ⊆ X`
(a model of the relative chains of the pair `(B, A)`) has vanishing `n`-th homology, then the map
`H_n(X, A) ⟶ H_n(X, B)` induced by `A ⊆ B` (i.e. `relCokerMap`) has trivial kernel. -/
theorem ker_eq_bot_of_isZero_coker {X : TopCat} {A B : Set X} (h : A ⊆ B) (n : ℕ)
    (hvan : IsZero ((cokernel (Work.Cohomology.inclChainsSub X A B h)).homology n)) :
    LinearMap.ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A B h) n)) = ⊥ := by
  have hS : (Work.Cohomology.tripleShort X A B h).ShortExact :=
    Work.Cohomology.relChains_triple_shortExact X A B h
  have hg : (Work.Cohomology.tripleShort X A B h).g = Work.Cohomology.relCokerMap X A B h :=
    Work.Cohomology.tripleShort_g X A B h
  have hf0 : HomologicalComplex.homologyMap (Work.Cohomology.tripleShort X A B h).f n = 0 := by
    refine IsZero.eq_zero_of_src ?_ _
    simpa only [Work.Cohomology.tripleShort_X1] using hvan
  have hr2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.tripleShort X A B h).f n)).range =
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.tripleShort X A B h).g n)).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ n)
  rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero] at hr2
  rw [← hg]
  exact hr2.symm

/-! ## The assembly -/

/-- **The injectivity of the localisation from the vanishing of the punctured pair.**

Let `P = K ∩ W°` be the coordinate half-ball piece of `W` with boundary centre `y` and `x ∈ P` an
interior point.  If `H_{n+1}(W ∖ {x}, (W ∖ {x}) ∖ P) = 0` then the localisation
`H_{n+1}(W, W∖P) ⟶ H_{n+1}(W, W∖{x})` is injective.

The long exact sequence of the triple `Pᶜ ⊆ {x}ᶜ ⊆ W` (`Work.Cohomology.tripleShort`) identifies
the kernel of the localisation with the image of `H_{n+1}(W∖{x}, (W∖{x})∖P)`, which vanishes; the
translation between the two models of that relative group is
`Work.Cohomology.relSubPunctured_homology_iso`. -/
theorem injective_of_isZero_punctured (n : ℕ) (W : TopCat)
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ)
    (x : W) (hx : x ∈ Work.Orient.halfBallPiece (n + 1) W y r ∩
        {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})
    (hvan : IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ x})
      {z : {z : W | z ≠ x} | (z : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})}).homology
          (n + 1))) :
    Function.Injective (resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)) := by
  classical
  set P : Set W := Work.Orient.halfBallPiece (n + 1) W y r ∩
    {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} with hPdef
  have hxP : x ∈ P := hx
  -- the two proofs of the inclusion `Pᶜ ⊆ {x}ᶜ`
  have hsub' : Pᶜ ⊆ ({x} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
  -- the honest vanishing transports to the "restricted inclusion" (cokernel) model
  have hvan' : IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ x})
      {z : {z : W | z ≠ x} | (z : W) ∈ Pᶜ}).homology (n + 1)) := hvan
  have hker := ker_eq_bot_of_isZero_coker hsub' (n + 1) (by
    obtain ⟨e⟩ := Work.Cohomology.relSubPunctured_homology_iso W x P hxP (n + 1)
    exact IsZero.of_iso hvan' e)
  have hinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap W Pᶜ ({x} : Set W)ᶜ hsub') (n + 1))) :=
    LinearMap.ker_eq_bot.mp hker
  -- the statement's map is the map of the triple sequence, definitionally
  have hmap : (resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) : RelH W (n + 1) P →ₗ[ℤ]
        RelH W (n + 1) ({x} : Set W))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.relCokerMap W Pᶜ ({x} : Set W)ᶜ hsub') (n + 1))) := rfl
  rw [hmap]
  exact hinj

/-! ## Auxiliary facts about the chart at the centre of the piece -/

/-- **The chart at a boundary point puts it on the hyperplane** of the half-space model. -/
theorem chartAt_boundary_coord_zero (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 0 = 0 := by
  have hce : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y y :
      EuclideanSpace ℝ (Fin (n + 1))) =
      ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 := by
    simp
  have h1 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y y :
      EuclideanSpace ℝ (Fin (n + 1))) ∈
      frontier (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := hy
  have h2 : ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 ∈
      frontier (Set.range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
    rw [← hce]; exact h1
  rw [frontier_range_modelWithCornersEuclideanHalfSpace (n + 1)] at h2
  exact h2.symm

/-- **A point of the coordinate half-ball is at distance at most `r/2` from its centre**
in the ambient Euclidean space of the model. -/
theorem dist_chart_le_of_mem_halfBallPiece (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {y x : W} {r : ℝ} (hx : x ∈ Work.Orient.halfBallPiece (n + 1) W y r) :
    dist (((chartAt (EuclideanHalfSpace (n + 1)) y) x).1 : EuclideanSpace ℝ (Fin (n + 1)))
      (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 : EuclideanSpace ℝ (Fin (n + 1))) ≤ r / 2 :=
  Metric.mem_closedBall.mp hx.1

/-! ## The theorem -/

end Helpers


/-! ## The main theorem's proof, stated in the aux module -/

theorem injective_localisation_of_halfBallInterior_aux (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (x : W) (hx : x ∈ (Work.Orient.halfBallPiece (n + 1) W y r) ∩
        {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) :
    Function.Injective (resRelH W (n + 1)
      (Set.singleton_subset_iff.mpr hx)) := by
  set e := chartAt (EuclideanHalfSpace (n + 1)) y with he
  -- the chart at the boundary point `y` puts it on the hyperplane, and `x` in the open half-space
  have hc : (e y).1 0 = 0 := chartAt_boundary_coord_zero n W hy
  have hx0 : 0 < ((e x).1 0) :=
    chartAt_interior_pos (n := n) (W := W) (z := y) hx.1.2 hx.2
  have hxd : dist ((e x).1 : EuclideanSpace ℝ (Fin (n + 1)))
      (((e y).1) : EuclideanSpace ℝ (Fin (n + 1))) ≤ r / 2 :=
    dist_chart_le_of_mem_halfBallPiece n W hx.1
  -- the flat model statement at this chart, and its transfer to `W`
  exact injective_of_isZero_punctured n W y r x hx
    (isZero_punctured_halfBall_of_model n W y hy r hr hgood x hx
      (halfBallPuncturedCore n (e y) hc (r / 2) (by linarith) (e x) hx0 hxd))

end Work.Orient.Boundary
