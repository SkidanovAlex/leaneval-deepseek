import Mathlib
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.CircleParam
import Submission.Work.OneDim.classify_connected_one_manifold

namespace Work.Euclidean.TangentField

open scoped Manifold Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

/-- The companion of `Work.ManifoldParity.exists_periodic_param_component` (which parametrises the
*compact* connected components, i.e. circles, by a periodic curve): here the component is not
compact, so by `Work.OneDim.classify_connected_one_manifold` it is diffeomorphic to `ℝ`, and the
diffeomorphism `G : ℝ ≃ ↥C` itself is the required parametrisation.  The proof is a modification of
the `Circle` case of `exists_periodic_param_component` (which computes all the properties of
`t ↦ G (Circle.exp t)` by the chain rule, using `mfderiv_subtypeVal_opens_injective`), with `ℝ` in
place of `Circle.exp` and `G` a diffeomorphism instead of `G ∘ Circle.exp`. -/
theorem exists_param_component_of_not_isCompact {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : Work.ManifoldParity.HasLocalGraphCharts K) (x : ↥K)
    (hne : ¬ IsCompact (connectedComponent x)) :
    letI := Work.ManifoldParity.graphChartedSpace K hgra
    ∃ γ : ℝ → ↥K,
      ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
        ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧
      Function.Injective γ ∧ Set.range γ = connectedComponent x ∧
      (∀ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
        γ t (1 : ℝ) ≠ 0) := by
  letI := Work.ManifoldParity.graphChartedSpace K hgra
  haveI hgr := Work.ManifoldParity.hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K := IsManifold.mk' _ _ _
  set Cx : TopologicalSpace.Opens ↥K :=
    ⟨connectedComponent x, Work.ManifoldParity.isOpen_connectedComponent_graph K hgra x⟩ with hCx
  haveI : IsManifold (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ↥Cx := IsManifold.mk' _ _ _
  haveI : ConnectedSpace ↥Cx :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  have hnec : ¬ CompactSpace ↥Cx := by
    intro hc
    exact hne (isCompact_iff_compactSpace.mpr hc)
  rcases Work.OneDim.classify_connected_one_manifold (C := ↥Cx) with ⟨⟨G⟩⟩ | ⟨⟨G⟩⟩
  · -- the component is diffeomorphic to `ℝ`: the diffeomorphism itself is the parametrisation
    refine ⟨fun t : ℝ => ((G t : ↥Cx) : ↥K), ?_, ?_, ?_, ?_⟩
    · -- smoothness of `z ↦ ((z : ↥Cx) : ↥K) ∘ G`
      exact (contMDiff_subtype_val (U := Cx) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp G.contMDiff
    · -- injectivity
      intro a b hab
      exact G.injective (Subtype.ext hab)
    · -- the range is the whole component
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact (G t).2
      · intro hz
        obtain ⟨w, hw⟩ := G.surjective ⟨z, hz⟩
        exact ⟨w, congrArg (fun y : ↥Cx => (y : ↥K)) hw⟩
    · -- the derivative never vanishes: chain rule, both factors injective
      intro t hv
      have hchain : mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
          (fun t : ℝ => ((G t : ↥Cx) : ↥K)) t
          = (mfderiv (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
              (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
              (Subtype.val : ↥Cx → ↥K) (G t)) ∘SL
            (mfderiv (modelWithCornersSelf ℝ ℝ)
              (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) (G : ℝ → ↥Cx) t) :=
        mfderiv_comp t
          ((Manifold.IsSmoothEmbedding.of_opens (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) Cx).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (G.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      rw [hchain] at hv
      simp only [ContinuousLinearMap.comp_apply] at hv
      have hinj1 : Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) (G : ℝ → ↥Cx) t) :=
        ((G.isLocalDiffeomorph.mfderivToContinuousLinearEquiv
          (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp) t).toLinearEquiv).injective
      have hinj2 : Function.Injective (mfderiv (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
          (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
          (Subtype.val : ↥Cx → ↥K) (G t)) :=
        Work.ManifoldParity.mfderiv_subtypeVal_opens_injective Cx (G t)
      have hzero : (mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) (G : ℝ → ↥Cx) t) (1 : ℝ) = 0 := by
        apply hinj2
        rw [hv, map_zero]
      have h10 : (1 : ℝ) = 0 := hinj1 (by rw [hzero, map_zero])
      exact one_ne_zero h10
  · -- the component is diffeomorphic to the circle, hence compact: contradiction
    exfalso
    exact hnec (G.toHomeomorph.compactSpace)

end

end Work.Euclidean.TangentField
