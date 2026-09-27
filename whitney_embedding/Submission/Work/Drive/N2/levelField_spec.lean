import Mathlib
import Submission.Work.Drive.N2.FieldData

/-!
# The level field has the two properties it is designed for

`Work.Drive.N2.auxField E G = (dE)ᵀ ∇G`, and `Work.Drive.N2.levelField E G χ` is the field
`χ • dE ((dE)ᵀ ∇G) / ‖(dE)ᵀ ∇G‖²`.  This file proves the two properties recorded in the
definition's docstring:

* where `auxField E G z ≠ 0`, the field raises `G` at speed `χ z`:
  `(dG z) (levelField E G χ z) = χ z`;
* the field always lies in the range of `dE z` (so its flow lines are tangent to the image of `E`).

The proof is the Riesz-representation computation
`(dG z) (dE z) v = ⟨∇G z, (dE z) v⟩ = ⟨(dE z)ᵀ ∇G z, v⟩ = ⟨v, v⟩ = ‖v‖²` with `v = auxField E G z`;
no differentiability of `E` or `G` is needed, the hypotheses are inherited from the application.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

/-- `grad G z` is the Riesz representative of `fderiv ℝ G z`, so `(fderiv ℝ G z) w = ⟪grad G z, w⟫`. -/
lemma fderiv_eq_inner_grad {N : ℕ} (G : EuclideanSpace ℝ (Fin N) → ℝ)
    (z w : EuclideanSpace ℝ (Fin N)) :
    (fderiv ℝ G z) w = inner ℝ (grad G z) w := by
  simp only [grad]
  rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := w) (y := fderiv ℝ G z)]

/-- `dG` evaluated on `dE (auxField E G)` equals `‖auxField E G‖²`. -/
lemma fderiv_comp_auxField {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    (fderiv ℝ G z) ((fderiv ℝ E z) (auxField E G z)) = ‖auxField E G z‖ ^ 2 := by
  rw [fderiv_eq_inner_grad]
  rw [← ContinuousLinearMap.adjoint_inner_left (fderiv ℝ E z) (auxField E G z) (grad G z)]
  rw [show (fderiv ℝ E z).adjoint (grad G z) = auxField E G z from rfl]
  rw [real_inner_self_eq_norm_sq]

theorem levelField_spec {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) (χ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    (∀ z, auxField E G z ≠ 0 → (fderiv ℝ G z) (levelField E G χ z) = χ z) ∧
      (∀ z, levelField E G χ z ∈ (fderiv ℝ E z).range) := by
  have _ := hE
  have _ := hG
  constructor
  · intro z hv
    have hA := fderiv_comp_auxField E G z
    have h : ‖auxField E G z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    show (fderiv ℝ G z)
      (χ z • ((‖auxField E G z‖ ^ 2)⁻¹ • (fderiv ℝ E z) (auxField E G z))) = χ z
    rw [map_smul, map_smul, hA, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ h, mul_one]
  · intro z
    show χ z • ((‖auxField E G z‖ ^ 2)⁻¹ • (fderiv ℝ E z) (auxField E G z)) ∈
      (fderiv ℝ E z).range
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ⟨auxField E G z, rfl⟩)

end Work.Drive.N2
