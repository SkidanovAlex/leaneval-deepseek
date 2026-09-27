import Mathlib

/-! Guidance from the project lead (the requester):

# The ambient level field for the `n = 2` level flow

These are the definitions used by `Work.Drive.N2.hasLevelFlow_of_noCritical`.

Let `e : M → ℝ^N` be a smooth embedding of a compact surface (`N = 5` in the application), and
`π : ℝ^N → M` a smooth nearest-point retraction of a tubular neighbourhood of `e '' univ` onto `M`
(existence: `Work.Drive.N2.exists_smooth_retraction_manifold`).  Put
`E := e ∘ π : ℝ^N → ℝ^N` and `G := f ∘ π : ℝ^N → ℝ`.  Then:

* `grad G` is the Riesz representative of `dG` (the gradient w.r.t. the Euclidean inner product);
* `auxField E G` is the vector field `(dE)ᵀ ∇G`;
* `levelField E G χ` is the field `χ • dE ((dE)ᵀ ∇G) / ‖(dE)ᵀ ∇G‖²`, which lies in the range of
  `dE` (so its flow lines are tangent to the image of `e`) and raises `G` at unit speed wherever
  `χ = 1`.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

set_option autoImplicit false

/-- The gradient of a real function on `ℝ^N`, as the Riesz representative of its derivative. -/
noncomputable def grad {N : ℕ} (G : EuclideanSpace ℝ (Fin N) → ℝ) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
  fun z => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm (fderiv ℝ G z)

/-- The vector field `(dE)ᵀ ∇G`. -/
noncomputable def auxField {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
  fun z => (fderiv ℝ E z).adjoint (grad G z)

/-- The level field of the pair `(E, G)` with cutoff `χ`: it is tangent to the range of `E` and
raises `G` at unit speed where `χ = 1`. -/
noncomputable def levelField {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) (χ : EuclideanSpace ℝ (Fin N) → ℝ) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
  fun z => χ z • ((‖auxField E G z‖ ^ 2)⁻¹ • (fderiv ℝ E z) (auxField E G z))

end Work.Drive.N2
