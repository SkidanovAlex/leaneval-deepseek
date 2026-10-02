import Submission.Work.ThomBordism.boundaryLocalGenerator
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Surgery.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Middle-degree Poincaré duality for the boundary `∂W`

For `W : NullBordismFamily ι F` (a compact oriented smooth `9`-manifold with boundary whose boundary
is identified with the closed oriented `8`-manifolds `F i`, with relative fundamental class `w`),
the boundary class `∂w = Work.Cohomology.hPairδ W.W (bdrySet W.W) 8 W.w ∈ H₈(∂W;ℤ)` is a
fundamental class of the closed `8`-manifold `∂W` (`Work.ThomBordism.boundaryLocalGenerator`), so
capping with it is a bijection `H⁴(∂W;ℤ) → H₄(∂W;ℤ)`: this is the middle-degree instance of
Poincaré duality, `Work.ThomBordism.bdryCapBdryBijective`.

## The proof, and the charted-space problem

The closed Poincaré duality theorem of the workspace,
`Work.Cohomology.pd_middleDegree_of_good`, needs a `ChartedSpace (EuclideanSpace ℝ (Fin 8)) ∂W`
together with the local generation of the fundamental class.  The calculus of the boundary chart of
`W` (`Work.Surgery.bnd_isManifold`) is only available for `C^∞` manifolds, while the model
`NullBordismFamily` asks only for a `C¹` bounding manifold; so the boundary charts of `W` cannot be
used directly.  Instead the charted-space structure on `∂W` is *transported* along the
homeomorphism `W.bdry : ∂W ≃ₜ Σ i, (F i).pt` from the finite disjoint union of the pieces, which is
charted because every piece is (`Man8.chartedSpace`): the chart of the disjoint union at a point is
the inclusion of the piece, inverted, followed by the chart of the piece (`sigmaPieceChart`).

Everything else is the local generation hypothesis (`Work.ThomBordism.boundaryLocalGenerator`) and
the closed Poincaré duality theorem of the workspace
(`Work.ThomBordism.goodUniv_of_localGen` + `Work.Cohomology.pd_middleDegree_of_good`).  No
smoothness of `∂W` is used beyond its `ChartedSpace` structure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-! ## The chart of a finite disjoint union -/

/-- **The chart of a finite disjoint union of charted spaces** at a point `q = ⟨i, y⟩`: the open
partial homeomorphism which inverts the open embedding `Sigma.mk i` and then applies the chart of
the piece `σ i` at `y`. -/
noncomputable def sigmaPieceChart {ι : Type} (σ : ι → Type) [∀ i, TopologicalSpace (σ i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 8)) (σ i)] (q : Σ i, σ i) :
    OpenPartialHomeomorph (Σ i, σ i) (EuclideanSpace ℝ (Fin 8)) := by
  haveI : Nonempty (σ q.1) := ⟨q.2⟩
  exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Sigma.mk q.1)
      (Topology.IsOpenEmbedding.sigmaMk (i := q.1))).symm.trans
    (chartAt (EuclideanSpace ℝ (Fin 8)) q.2)

/-- The chart `sigmaPieceChart` is defined at its own base point. -/
theorem sigmaPieceChart_mem_source {ι : Type} (σ : ι → Type) [∀ i, TopologicalSpace (σ i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 8)) (σ i)] (q : Σ i, σ i) :
    q ∈ (sigmaPieceChart σ q).source := by
  rw [sigmaPieceChart, OpenPartialHomeomorph.trans_source]
  constructor
  · rw [OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨q.2, rfl⟩
  · rw [Set.mem_preimage]
    haveI : Nonempty (σ q.1) := ⟨q.2⟩
    have h : ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Sigma.mk q.1)
        (Topology.IsOpenEmbedding.sigmaMk (i := q.1))).symm) q = q.2 := by
      have h2 := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
        (f := Sigma.mk q.1) (h := Topology.IsOpenEmbedding.sigmaMk (i := q.1)) (x := q.2)
      exact h2
    rw [h]
    exact mem_chart_source _ _

/-- **The charted-space structure of a finite disjoint union** of spaces charted over `ℝ⁸`. -/
noncomputable def sigmaChartedSpace {ι : Type} (σ : ι → Type) [∀ i, TopologicalSpace (σ i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 8)) (σ i)] :
    ChartedSpace (EuclideanSpace ℝ (Fin 8)) (Σ i, σ i) where
  atlas := Set.range (sigmaPieceChart σ)
  chartAt := sigmaPieceChart σ
  mem_chart_source q := sigmaPieceChart_mem_source σ q
  chart_mem_atlas q := ⟨q, rfl⟩

/-! ## The target -/

theorem bdryCapBdryBijective {ι : Type} [Fintype ι] {F : ι → Work.ThomBordism.Man8}
    (W : Work.ThomBordism.NullBordismFamily ι F) :
    Function.Bijective (fun y : (Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (Work.ThomBordism.bdrySet W.W))).homology 4 =>
      (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4 4) y
        (Work.Cohomology.hPairδ (TopCat.of W.W) (Work.ThomBordism.bdrySet W.W) 8 W.w)) := by
  -- the charted-space structure of the boundary, transported from the disjoint union of the pieces
  haveI hσ : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (Σ i, (F i).pt) :=
    sigmaChartedSpace (ι := ι) (fun i => (F i).pt)
  haveI hb : ChartedSpace (EuclideanSpace ℝ (Fin 8)) ↥(Work.ThomBordism.bdrySet W.W) :=
    W.bdry.symm.chartedSpace
  -- the boundary is compact and Hausdorff
  haveI hcomp : CompactSpace ↥(Work.ThomBordism.bdrySet W.W) := by
    have hcl : IsClosed (Work.ThomBordism.bdrySet W.W) :=
      ModelWithCorners.isClosed_boundary (I := modelWithCornersEuclideanHalfSpace 9) (M := W.W)
        (n := (1 : WithTop ℕ∞)) (by norm_num)
    exact isCompact_iff_compactSpace.mp hcl.isCompact
  haveI ht2 : T2Space ↥(Work.ThomBordism.bdrySet W.W) := inferInstance
  -- the class is a fundamental class, hence capping with it is bijective
  refine Work.Cohomology.pd_middleDegree_of_good 4
    (TopCat.of (Work.ThomBordism.bdrySet W.W))
    (Work.Cohomology.hPairδ (TopCat.of W.W) (Work.ThomBordism.bdrySet W.W) 8 W.w)
    (Work.ThomBordism.goodUniv_of_localGen (N := 8)
      (M := TopCat.of (Work.ThomBordism.bdrySet W.W))
      (Work.Cohomology.hPairδ (TopCat.of W.W) (Work.ThomBordism.bdrySet W.W) 8 W.w)
      (fun x => Work.ThomBordism.boundaryLocalGenerator W x) (by norm_num))

end

end Work.ThomBordism
