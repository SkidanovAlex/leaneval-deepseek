import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.exists_maximal_arc_param
import Submission.Work.OneDim.end_behavior_injective
import Submission.Work.OneDim.arc_image_shape
import Submission.Work.OneDim.circle_gluing
import Submission.Work.OneDim.one_manifold_dichotomy

namespace Work.OneDim

open scoped Manifold Topology
open Set Function Filter

/-- **Classification of connected smooth 1-manifolds.**  Every connected (nonempty), Hausdorff,
second countable smooth 1-manifold is diffeomorphic to `ℝ` (when it is not compact) or to the
circle `Circle` (when it is).  Classical; the standard proofs use a maximal arc / locally linear
chart, or a nowhere-vanishing vector field and its maximal integral curves. -/
theorem classify_connected_one_manifold {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    [T2Space C] [SecondCountableTopology C] [ConnectedSpace C] :
    (Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ℝ C ((⊤ : ℕ∞) : WithTop ℕ∞))) ∨
      (Nonempty (Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle C ((⊤ : ℕ∞) : WithTop ℕ∞))) := by
  classical
  obtain ⟨p⟩ : Nonempty C := inferInstance
  obtain ⟨s, γ, harc, hmax⟩ := exists_maximal_arc_param (C := C) p
  have hend : ∀ (γ : ℝ → C), Continuous γ → Function.Injective γ → ∀ x : C,
      (∀ U : Set C, IsOpen U → x ∈ U →
        Filter.Frequently (fun t : ℝ => γ t ∈ U) Filter.atTop) →
      Filter.Tendsto γ Filter.atTop (nhds x) :=
    fun γ hγ hinj x hx => end_behavior_injective hγ hinj hx
  rcases arc_image_shape (C := C) hend harc hmax with
    ⟨φ, hbij, hld⟩ | ⟨q, φ, hinj, hld, hrange, htop, hbot⟩
  · exact Or.inl (nonempty_diffeomorph_of_bijective_localDiffeomorph φ hbij hld)
  · exact Or.inr (circle_gluing hinj hld hrange htop hbot)

end Work.OneDim
