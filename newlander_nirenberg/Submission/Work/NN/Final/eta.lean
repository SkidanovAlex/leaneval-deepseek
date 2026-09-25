/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The linear "reflection in the normal variable" map

`eta c` is the continuous linear map `(x, t) ↦ (x, c * t)` on `X × ℝ`.  It is the elementary
building block of the one-sided extension: for `c = -(ε i)` with `ε i > 0` it sends the lower
half space `{t < 0}` into the upper half space `{0 < t}`.
-/
import Mathlib

noncomputable section

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The linear map `(x, t) ↦ (x, c * t)` on `X × ℝ`. -/
def eta (c : ℝ) : X × ℝ →L[ℝ] X × ℝ :=
  (ContinuousLinearMap.fst ℝ X ℝ).prod (c • ContinuousLinearMap.snd ℝ X ℝ)

@[simp] lemma eta_apply (c : ℝ) (p : X × ℝ) : eta (X := X) c p = (p.1, c * p.2) := rfl

lemma eta_injective (c : ℝ) (hc : c ≠ 0) : Function.Injective (eta (X := X) c) := by
  intro p q h
  simp only [eta_apply, Prod.mk.injEq] at h
  exact Prod.ext h.1 (mul_left_cancel₀ hc h.2)

lemma eta_surjective (c : ℝ) (hc : c ≠ 0) : Function.Surjective (eta (X := X) c) := by
  intro q
  refine ⟨(q.1, c⁻¹ * q.2), ?_⟩
  ext
  · simp
  · show c * (c⁻¹ * q.2) = q.2
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

@[simp] lemma eta_zero_snd (c : ℝ) (x : X) : eta (X := X) c (x, 0) = (x, 0) := by
  simp [eta_apply]

/-- Bound on the operator norm of `eta c`. -/
lemma norm_eta_le (c : ℝ) : ‖eta (X := X) c‖ ≤ max 1 |c| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _)) fun p => ?_
  rw [eta_apply, Prod.norm_mk]
  refine max_le ?_ ?_
  · calc ‖p.1‖ ≤ max ‖p.1‖ |p.2| := le_max_left _ _
      _ = 1 * max ‖p.1‖ |p.2| := (one_mul _).symm
      _ ≤ max 1 |c| * max ‖p.1‖ |p.2| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_of_le_left (norm_nonneg p.1))
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (abs_nonneg _)
      (le_max_of_le_left zero_le_one)

end Work.NN.Final
