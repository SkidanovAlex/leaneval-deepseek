import Mathlib
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transport of collars along a boundary-preserving homeomorphism

If `e : X ≃ₜ Y` is a homeomorphism of topological manifolds with boundary which carries the
boundary of `X` onto the boundary of `Y` (in the precise sense of the hypothesis `hbdry`), then a
collar of `X` transports to a collar of `Y`: the collar map `∂X × [0,∞) ↪ X` is conjugated by `e`
and reparametrised along the induced homeomorphism `∂Y ≃ₜ ∂X`.

This is pure topology: it shows that `Work.Surgery.HasCollar` is a homeomorphism-invariant
property, so it can be transported between the different models of the same manifold that occur in
the construction of the exotic sphere.
-/

open scoped Manifold Topology
open Function

namespace Work.ThomBordism

/-- **The boundary homeomorphism induced by a homeomorphism of the manifolds.**  A homeomorphism
`e : X ≃ₜ Y` whose inverse carries `∂Y` into `∂X` restricts to a homeomorphism `∂Y ≃ₜ ∂X`. -/
def boundaryHomeomorph {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) Y]
    (e : X ≃ₜ Y)
    (hbdry : ∀ y : Y, y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary Y ↔
      e.symm y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).boundary Y ≃ₜ
      (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X where
  toFun y := ⟨e.symm y.1, (hbdry y.1).mp y.2⟩
  invFun x := ⟨e x.1, (hbdry (e x.1)).mpr (by rw [Homeomorph.symm_apply_apply]; exact x.2)⟩
  left_inv y := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _

@[simp]
theorem boundaryHomeomorph_apply {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) Y]
    (e : X ≃ₜ Y)
    (hbdry : ∀ y : Y, y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary Y ↔
      e.symm y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X)
    (y : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary Y) :
    (boundaryHomeomorph e hbdry y : X) = e.symm y.1 := rfl

theorem collarTransport {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) Y]
    (e : X ≃ₜ Y)
    (hbdry : ∀ y : Y, y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary Y ↔
      e.symm y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X) :
    Work.Surgery.HasCollar n X → Work.Surgery.HasCollar n Y := by
  rintro ⟨c⟩
  refine ⟨{ toFun := fun p : _ × Work.Surgery.HalfLine =>
              e (c.toFun (boundaryHomeomorph e hbdry p.1, p.2))
            isOpenEmbedding := ?_
            toFun_zero := ?_ }⟩
  · have hΦ : Topology.IsOpenEmbedding (fun p :
        (modelWithCornersEuclideanHalfSpace (n + 1)).boundary Y × Work.Surgery.HalfLine =>
        ((boundaryHomeomorph e hbdry) p.1, p.2)) :=
      ((boundaryHomeomorph e hbdry).prodCongr (Homeomorph.refl Work.Surgery.HalfLine)).isOpenEmbedding
    exact e.isOpenEmbedding.comp (c.isOpenEmbedding.comp hΦ)
  · intro x
    show e (c.toFun (boundaryHomeomorph e hbdry x, ⟨0, le_refl 0⟩)) = x.1
    rw [c.toFun_zero]
    exact e.apply_symm_apply x.1

end Work.ThomBordism
