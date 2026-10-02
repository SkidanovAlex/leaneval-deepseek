import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Closed
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_map_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sum of the pushed fundamental classes of the pieces of a boundary is a fundamental class

`Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push` proves that for a finite family
`Fam : ι → Man8` of closed oriented `8`-manifolds and a homeomorphism `φ : Σ i, (Fam i).pt ≃ₜ M`
onto a compact `8`-manifold `M`, the sum `∑ i, (φ ∘ σᵢ)_* (Fam i).c` is a fundamental class of `M`.

Here we need the same statement for `M = ∂W`, the boundary of a compact `9`-manifold with boundary
`W`.  The hypotheses of `isFundClass_sum_push` on `M` (`ChartedSpace (EuclideanSpace ℝ (Fin 8)) M`
and `IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8))) ⊤ M`) are *not* available for
`∂W` here: the workspace's boundary-manifold instances
(`Work.Surgery.bndChartedSpace`, `Work.Surgery.bndIsManifold`) require `W` to be `C^∞`, whereas the
ambient hypothesis of the ORIENT chapter is only `C¹`.

Inspection of the proof of `isFundClass_sum_push` shows that neither hypothesis on `M` is used: its
only structural input is `[T1Space M]` (through `isIso_openEmbPairMap_of_isOpenEmbedding`), which
comes from `[T2Space M]`.  We therefore record the generalisation
`isFundClass_sum_push_of_t2` (arbitrary topological `M`, `T2`), from which the requested
`piecesBound_sum_isFundClass` is the immediate specialisation `φ = e.symm`.

The mathematical content is the local analysis of the disjoint union: the local class of a sum is
the sum of the local classes; a piece whose image misses the point contributes `0`; and the piece
containing the point is the image of its own space under an *open embedding* `φ ∘ σᵢ`, hence
induces an isomorphism on local homology carrying the fundamental class of the piece to a generator.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.Transversality.OrientBridge

noncomputable section

/-- **The sum of the pushed fundamental classes is a fundamental class**, for `M` an arbitrary `T2`
topological space (no manifold structure is needed).  This is
`Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push` with the manifold hypotheses on
`M` dropped, which is what the boundary `∂W` of a merely `C¹` manifold with boundary requires. -/
theorem isFundClass_sum_push_of_t2 {ι : Type} [Fintype ι] (Fam : ι → Work.ThomBordism.Man8)
    {M : Type} [TopologicalSpace M] [T2Space M] (φ : (Σ i : ι, (Fam i).pt) ≃ₜ M) :
    Work.Orient.IsFundClass (TopCat.of M) 8
      (∑ i, HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of M)
        (TopCat.ofHom ⟨fun y => φ ⟨i, y⟩, φ.continuous_toFun.comp continuous_sigmaMk⟩)) 8
        (Fam i).c) := by
  intro y
  rw [locClass_eq_localClassAt]
  -- the point `y` is the image of a point of the `i₀`-th piece
  obtain ⟨w, rfl⟩ : ∃ w : Σ i, (Fam i).pt, φ w = y := ⟨φ.symm y, φ.apply_symm_apply y⟩
  obtain ⟨i₀, y₀⟩ := w
  -- the local class of the sum is the sum of the local classes
  have hsum : Work.ThomBordism.localClassAt (TopCat.of M) 8
        (∑ i, pushClass φ i) (φ ⟨i₀, y₀⟩)
      = ∑ i : ι, Work.ThomBordism.localClassAt (TopCat.of M) 8 (pushClass φ i)
          (φ ⟨i₀, y₀⟩) :=
    Work.ThomBordism.localClassAt_sum 8 _ _
  -- the pieces away from `y` contribute `0`
  have hother : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i₀ →
      Work.ThomBordism.localClassAt (TopCat.of M) 8 (pushClass φ j) (φ ⟨i₀, y₀⟩) = 0 := by
    intro j _ hj
    refine Work.ThomBordism.localClassAt_homologyMap_eq_zero_of_ne (pushPt φ j) _
      (fun z hz => ?_) 8 (Fam j).c
    have h1 : (⟨j, z⟩ : Σ i, (Fam i).pt) = ⟨i₀, y₀⟩ := φ.injective hz
    exact hj ((Sigma.mk.injEq _ _ _ _).mp h1).1
  -- the piece containing `y` contributes a generator
  have hinj : Function.Injective (pushPt φ i₀) := by
    intro a b hab
    have h1 : (⟨i₀, a⟩ : Σ i, (Fam i).pt) = ⟨i₀, b⟩ := φ.injective hab
    exact eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h1).2
  have hemb : Topology.IsOpenEmbedding (fun z : (Fam i₀).pt => pushPt φ i₀ z) :=
    (Homeomorph.isOpenEmbedding φ).comp
      (Topology.IsOpenEmbedding.sigmaMk (σ := fun i => (Fam i).pt) (i := i₀))
  have hgen : Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of M) 8
        (pushClass φ i₀) (φ ⟨i₀, y₀⟩))} = ⊤ := by
    have hfund : Submodule.span ℤ
        {Work.ThomBordism.localClassAt (Fam i₀).X 8 (Fam i₀).c y₀} = ⊤ :=
      (Fam i₀).c_fund y₀
    have hxy : pushPt φ i₀ y₀ = φ ⟨i₀, y₀⟩ := rfl
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.ThomBordism.openEmbPairMap (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy) 8) :=
      Work.ThomBordism.isIso_openEmbPairMap_of_isOpenEmbedding (f := pushPt φ i₀) (x := y₀)
        (y := φ ⟨i₀, y₀⟩) hinj hxy hemb 8
    rw [show pushClass φ i₀ = HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (Fam i₀).X (TopCat.of M) (pushPt φ i₀)) 8 (Fam i₀).c from rfl]
    rw [Work.ThomBordism.localClassAt_naturality (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hxy
      (Work.ThomBordism.openEmbPairMapG (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy)
      (Work.ThomBordism.openEmbPairMapW (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy) 8 (Fam i₀).c]
    exact span_singleton_of_isIso (HomologicalComplex.homologyMap
      (Work.ThomBordism.openEmbPairMap (pushPt φ i₀) y₀ (φ ⟨i₀, y₀⟩) hinj hxy) 8)
      (Work.ThomBordism.localClassAt (Fam i₀).X 8 (Fam i₀).c y₀) hfund
  rw [hsum, Finset.sum_eq_single i₀ hother (fun h => absurd (Finset.mem_univ i₀) h)]
  exact hgen

end

end Work.ThomBordism.Transversality.OrientBridge

namespace Work.ThomBordism

/-- **The sum of the pushed fundamental classes of the pieces of the boundary of `W` is a
fundamental class of that boundary.**

`W` is a compact `T2` `C¹` `9`-manifold with boundary, `Fam` a finite family of closed oriented
`8`-manifolds (`Work.ThomBordism.Man8`), and `e : ∂W ≃ₜ Σ i, (Fam i).pt` a homeomorphism exhibiting
`∂W` as the disjoint union of the pieces.  Then the sum of the fundamental classes of the pieces,
pushed into `∂W` along `e.symm`, is a fundamental class of `∂W`; equivalently, `∂W` is oriented by
the pieces.

This is `Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push_of_t2` specialised to
`φ = e.symm`.  (Note that the manifold hypotheses on `M` in
`Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push` cannot be instantiated for `∂W`
here: the boundary-manifold instances of the workspace need `W` to be `C^∞`, and only `C¹`
smoothness of `W` is assumed.) -/
theorem piecesBound_sum_isFundClass
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary W) ≃ₜ (Σ i : ι, (Fam i).pt)) :
    Work.Orient.IsFundClass
      (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8
      (∑ i : ι, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X
            (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W))
            (TopCat.ofHom ⟨fun y => e.symm ⟨i, y⟩,
              e.continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c) :=
  Transversality.OrientBridge.isFundClass_sum_push_of_t2 Fam e.symm

end Work.ThomBordism
