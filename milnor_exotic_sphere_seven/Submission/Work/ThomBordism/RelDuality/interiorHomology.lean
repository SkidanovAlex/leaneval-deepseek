import Mathlib
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.ThomBordism.RelDuality.interiorPushDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion of the interior of a compact manifold with boundary is a homology equivalence

For a compact `C¹` `9`-manifold `M` with boundary, modelled on the half-space
`H = EuclideanHalfSpace 9`, the interior `int M = {x | x ∉ (𝓡∂ 9).boundary M}` has the same
singular homology as `M`:

`Work.ThomBordism.RelDuality.interiorHomology`.

The classical proof is the collar neighbourhood theorem: `M` deformation retracts onto `int M` by
collapsing a collar of `∂M`.  A collar is not available in this workspace (`Work.Surgery.HasCollar`
is a named *input*), and the statement is only `C¹`, so the retraction is built here by hand from
the charts:

* around every point `x : M` we build a *local inward push* (`PushDatum.localMap`, in
  `interiorPushDefs.lean`) which shifts the first chart coordinate of the points of a small
  half-ball strictly into the interior of the model, and is the identity outside;
* finitely many of these regions cover the compact `M`; composing the corresponding pushes (with
  the time parameter `t ∈ [0,1]` built into each push) gives a continuous homotopy
  `H : M × ℝ → M` with `H (x,0) = x`, `H (x,1) ∈ int M` for all `x`, and `H (int M × ℝ) ⊆ int M`;
* `H` exhibits the inclusion `int M ↪ M` as a homotopy equivalence, so it induces an isomorphism on
  singular homology in every degree, by `Work.Cohomology.homologyEquiv`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped Topology Manifold

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]

/-- The interior of `M` is the complement of its boundary. -/
theorem isInteriorPoint_iff_not_mem_boundary (z : M) :
    (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint z ↔
      z ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M := by
  show z ∈ (modelWithCornersEuclideanHalfSpace 9).interior M ↔ _
  rw [← ModelWithCorners.compl_boundary]
  exact Iff.rfl

/-- **Finitely many local pushes cover `M`**: the regions of the push data at the points of a finite
set cover `M`. -/
theorem exists_finset_region_cover :
    ∃ S : Finset M, ∀ x : M, x ∈ ⋃ y ∈ S, (PushDatum.ofPoint y).region := by
  classical
  obtain ⟨S, hS⟩ := (isCompact_univ (X := M)).elim_finite_subcover
    (fun y : M => (PushDatum.ofPoint y).region)
    (fun y => PushDatum.isOpen_region (PushDatum.ofPoint y))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, PushDatum.mem_region_ofPoint x⟩)
  exact ⟨S, fun x => hS (Set.mem_univ x)⟩

/-- **The composed local push**: a continuous homotopy of the identity of `M` which at time `1`
moves every point of `M` into the interior and which preserves the interior at every time. -/
theorem exists_pushHomotopy :
    ∃ H : M × ℝ → M, Continuous H ∧ (∀ x : M, H (x, 0) = x) ∧
      (∀ x : M, (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint x →
        ∀ t : ℝ, (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (H (x, t))) ∧
      (∀ x : M, (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (H (x, 1))) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_region_cover (M := M)
  have key : ∀ s : Finset M, ∃ H : M × ℝ → M, Continuous H ∧ (∀ x : M, H (x, 0) = x) ∧
      (∀ x : M, (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint x →
        ∀ t : ℝ, (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (H (x, t))) ∧
      (∀ x : M, x ∈ ⋃ y ∈ s, (PushDatum.ofPoint y).region →
        (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (H (x, 1))) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · refine ⟨fun p : M × ℝ => p.1, continuous_fst, fun x => rfl, ?_, ?_⟩
      · intro x hx t
        exact hx
      · intro x hx
        simp at hx
    · intro a s ha ih
      obtain ⟨H, hcont, h0, hpres, hpush⟩ := ih
      refine ⟨fun p : M × ℝ => H ((PushDatum.ofPoint a).localMap p.2 p.1, p.2),
        ?_, ?_, ?_, ?_⟩
      · exact hcont.comp
          (((PushDatum.ofPoint a).continuous_localMap_uncurry).prodMk continuous_snd)
      · intro x
        show H ((PushDatum.ofPoint a).localMap 0 x, 0) = x
        rw [(PushDatum.ofPoint a).localMap_zero x, h0 x]
      · intro x hx t
        exact hpres _ ((PushDatum.ofPoint a).isInteriorPoint_localMap_of_isInteriorPoint hx t) t
      · intro x hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨y, hx⟩ := hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨hy, hxy⟩ := hx
        by_cases hxa : x ∈ (PushDatum.ofPoint a).region
        · exact hpres _ ((PushDatum.ofPoint a).isInteriorPoint_localMap hxa one_pos) 1
        · show (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint
            (H ((PushDatum.ofPoint a).localMap 1 x, 1))
          rw [(PushDatum.ofPoint a).localMap_eq_self_of_not_mem hxa 1]
          refine hpush x ?_
          rcases Finset.mem_insert.mp hy with rfl | hys
          · exact absurd hxy hxa
          · exact Set.mem_biUnion hys hxy
  obtain ⟨H, hcont, h0, hpres, hpush⟩ := key S
  exact ⟨H, hcont, h0, hpres, fun x => hpush x (hS x)⟩

/-- **The inclusion of the interior as a continuous map.** -/
def inclInterior (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] :
    C({x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}, M) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem inclInterior_apply (x : {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    inclInterior M x = x.1 := rfl

/-- The inclusion of the interior into a compact manifold with boundary induces a bijection on
singular homology in every degree. -/
theorem interiorHomology {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M] :
    ∀ m : ℕ, Function.Bijective (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ
        (TopCat.of {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}) (TopCat.of M)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) m) := by
  classical
  obtain ⟨H, hcont, h0, hpres, hpush⟩ := exists_pushHomotopy (M := M)
  -- the interior, as a type
  have hA : ∀ z : M, z ∈ {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M} ↔
      (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint z :=
    fun z => (isInteriorPoint_iff_not_mem_boundary z).symm
  -- the map `M → int M` obtained from the homotopy at time `1`
  have hcontEnd : Continuous fun x : M => H (x, 1) :=
    hcont.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : M => (1 : ℝ)))
  let F : C(M, {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :=
    ⟨fun x => ⟨H (x, 1), (hA (H (x, 1))).mpr (hpush x)⟩,
      Continuous.subtype_mk hcontEnd (fun x => (hA (H (x, 1))).mpr (hpush x))⟩
  have hF_coe : ∀ x : M, (F x).1 = H (x, 1) := fun x => rfl
  -- the homotopy on `M`
  have hcontHom : Continuous fun p : Set.Icc (0 : ℝ) 1 × M => H (p.2, 1 - (p.1 : ℝ)) :=
    hcont.comp (continuous_snd.prodMk
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))
  have hhomM : ((inclInterior M).comp F).Homotopic (ContinuousMap.id M) := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : Set.Icc (0 : ℝ) 1 × M => H (p.2, 1 - (p.1 : ℝ)), hcontHom⟩ ?_ ?_⟩
    · intro x
      change H (x, 1 - ((0 : Set.Icc (0 : ℝ) 1) : ℝ)) = H (x, 1)
      simp
    · intro x
      change H (x, 1 - ((1 : Set.Icc (0 : ℝ) 1) : ℝ)) = x
      rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from by simp,
        show (1 : ℝ) - 1 = 0 from by norm_num]
      exact h0 x
  -- the homotopy on the interior
  have hhomA : (F.comp (inclInterior M)).Homotopic
      (ContinuousMap.id {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}) := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : Set.Icc (0 : ℝ) 1 ×
          {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M} =>
        ⟨H (p.2.1, 1 - (p.1 : ℝ)), (hA (H (p.2.1, 1 - (p.1 : ℝ)))).mpr
          (hpres p.2.1 ((hA p.2.1).mp p.2.2) (1 - (p.1 : ℝ)))⟩, ?_⟩ ?_ ?_⟩
    · exact Continuous.subtype_mk (hcontHom.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd)))
        (fun p => (hA (H (p.2.1, 1 - (p.1 : ℝ)))).mpr
          (hpres p.2.1 ((hA p.2.1).mp p.2.2) (1 - (p.1 : ℝ))))
    · intro a
      apply Subtype.ext
      change H (a.1, 1 - ((0 : Set.Icc (0 : ℝ) 1) : ℝ)) = H (a.1, 1)
      simp
    · intro a
      apply Subtype.ext
      change H (a.1, 1 - ((1 : Set.Icc (0 : ℝ) 1) : ℝ)) = a.1
      rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from by simp,
        show (1 : ℝ) - 1 = 0 from by norm_num]
      exact h0 a.1
  intro m
  haveI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ
        (TopCat.of {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M})
        (TopCat.of M)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) m) :=
    Work.Cohomology.homologyEquiv ℤ
      (TopCat.of {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}) (TopCat.of M)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (TopCat.ofHom F)
      hhomA.some hhomM.some m
  exact ConcreteCategory.bijective_of_isIso _

end

end Work.ThomBordism.RelDuality
