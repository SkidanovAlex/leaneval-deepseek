import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `(n+1)`-tuple normalization map: definitions

This file fixes the objects of the proof of `Work.Diff.C.local_diffeo_of_gram`.

Given `F : Fin (n+1) → M → ℝ` (`n = finrank ℝ E`), we consider

* `uvec F x : Fin (n+1) → ℝ`, the tuple `i ↦ F i x`;
* `U F x`, the same tuple as an element of `EuclideanSpace ℝ (Fin (n+1))`;
* `sq F x = ∑ i, (F i x)^2 = ‖U F x‖²`;
* `rad F x = √(sq F x) = ‖U F x‖`;
* `G₀ F x = (rad F x)⁻¹ • U F x`, the normalization of `U F x`;
* `G F hpos`, the same map with values in the unit sphere `SphereD E`.

Nothing here is a `sorry`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The typed index set: `Fin (n+1)` with `n = finrank ℝ E`. -/
abbrev Idx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  Fin (Module.finrank ℝ E + 1)

/-- The tuple `i ↦ F i x` in `Fin (n+1) → ℝ`. -/
noncomputable def uvec (F : Idx E → M → ℝ) (x : M) : Idx E → ℝ := fun i => F i x

/-- The tuple `i ↦ F i x` as an element of the Euclidean space `ℝ^{n+1}`. -/
noncomputable def U (F : Idx E → M → ℝ) (x : M) : EuclideanSpace ℝ (Idx E) :=
  WithLp.toLp 2 (uvec F x)

/-- `sq F x = ∑ i, (F i x)^2`, the square of the norm of `U F x`. -/
noncomputable def sq (F : Idx E → M → ℝ) (x : M) : ℝ := ∑ i, F i x ^ 2

/-- `rad F x = √(sq F x)`, the norm of `U F x`. -/
noncomputable def rad (F : Idx E → M → ℝ) (x : M) : ℝ := Real.sqrt (sq F x)

/-- The normalization of `U F x`: `(rad F x)⁻¹ • U F x`. -/
noncomputable def G₀ (F : Idx E → M → ℝ) (x : M) : EuclideanSpace ℝ (Idx E) :=
  (rad F x)⁻¹ • U F x

@[simp] theorem ofLp_U (F : Idx E → M → ℝ) (x : M) : (U F x).ofLp = uvec F x := rfl

@[simp] theorem uvec_apply (F : Idx E → M → ℝ) (x : M) (i : Idx E) : uvec F x i = F i x := rfl

@[simp] theorem sq_def (F : Idx E → M → ℝ) (x : M) : sq F x = ∑ i, F i x ^ 2 := rfl

@[simp] theorem rad_def (F : Idx E → M → ℝ) (x : M) : rad F x = Real.sqrt (sq F x) := rfl

@[simp] theorem G₀_def (F : Idx E → M → ℝ) (x : M) : G₀ F x = (rad F x)⁻¹ • U F x := rfl

theorem norm_sq_U (F : Idx E → M → ℝ) (x : M) : ‖U F x‖ ^ 2 = sq F x := by
  rw [EuclideanSpace.norm_sq_eq, sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofLp_U]
  simp [uvec, Real.norm_eq_abs, sq_abs]

theorem norm_U (F : Idx E → M → ℝ) (x : M) : ‖U F x‖ = rad F x := by
  rw [rad_def, ← norm_sq_U]
  exact (Real.sqrt_sq (norm_nonneg (U F x))).symm

theorem sq_nonneg (F : Idx E → M → ℝ) (x : M) : 0 ≤ sq F x := by
  rw [← norm_sq_U]; positivity

theorem rad_pos (F : Idx E → M → ℝ) {x : M} (h : 0 < sq F x) : 0 < rad F x := by
  rw [rad_def]; exact Real.sqrt_pos.mpr h

theorem rad_ne_zero (F : Idx E → M → ℝ) {x : M} (h : 0 < sq F x) : rad F x ≠ 0 :=
  (rad_pos F h).ne'

theorem rad_sq (F : Idx E → M → ℝ) (x : M) : rad F x ^ 2 = sq F x := by
  rw [rad_def]
  exact Real.sq_sqrt (sq_nonneg F x)

theorem norm_G₀ (F : Idx E → M → ℝ) {x : M} (h : 0 < sq F x) : ‖G₀ F x‖ = 1 := by
  rw [G₀_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (rad_pos F h), norm_U,
    inv_mul_cancel₀ (rad_ne_zero F h)]

theorem ofLp_G₀ (F : Idx E → M → ℝ) (x : M) (i : Idx E) :
    (G₀ F x).ofLp i = (rad F x)⁻¹ * F i x := by
  simp [G₀_def, U, uvec, WithLp.toLp]

/-- The normalized map, with values in the unit sphere. -/
noncomputable def G (F : Idx E → M → ℝ) (hpos : ∀ x, 0 < sq F x) : M → SphereD E :=
  fun x => ⟨G₀ F x, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_G₀ F (hpos x)⟩

@[simp] theorem coe_G (F : Idx E → M → ℝ) (hpos : ∀ x, 0 < sq F x) (x : M) :
    ((G F hpos x : SphereD E) : EuclideanSpace ℝ (Idx E)) = G₀ F x := rfl

/-- **The defining property of `G`**: it is a positive multiple of the tuple `(F i x)ᵢ`. -/
theorem coe_G_eq (F : Idx E → M → ℝ) (hpos : ∀ x, 0 < sq F x) (x : M) :
    ((G F hpos x : SphereD E) : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      = (rad F x)⁻¹ • (fun i => F i x) := by
  have h : rad F x ≠ 0 := (rad_pos F (hpos x)).ne'
  rw [coe_G, G₀_def]
  ext i
  simp [U, uvec, WithLp.toLp]

end Work.Diff.C
