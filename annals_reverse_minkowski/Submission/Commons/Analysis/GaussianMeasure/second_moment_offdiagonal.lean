import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Commons.Analysis.GaussianMeasure

/-! The off-diagonal second moment of the standard Gaussian measure on
`EuclideanSpace ℝ (Fin n)` vanishes: for `i ≠ j`,
`∫ x, (x i) * (x j) * exp (-π‖x‖²) = 0`.
This is an oddness statement: negating the `i`-th coordinate is a linear
isometry preserving Lebesgue measure, and it sends the integrand to its
negative. -/

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Negate the `i`-th coordinate of a function `Fin n → ℝ`. -/
private def negCoord {n : ℕ} (i : Fin n) : (Fin n → ℝ) → Fin n → ℝ :=
  fun f k => if k = i then - f k else f k

/-- Negating the `i`-th coordinate is a linear equivalence on `Fin n → ℝ`. -/
private def negCoordLE {n : ℕ} (i : Fin n) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := negCoord i
  invFun := negCoord i
  left_inv f := by
    funext k
    by_cases h : k = i <;> simp [negCoord, h]
  right_inv f := by
    funext k
    by_cases h : k = i <;> simp [negCoord, h]
  map_add' f g := by
    funext k
    by_cases h : k = i <;> simp [negCoord, h, add_comm]
  map_smul' a f := by
    funext k
    by_cases h : k = i <;> simp [negCoord, h]

/-- The linear equivalence on `EuclideanSpace ℝ (Fin n)` negating coordinate `i`. -/
private def coordFlipLE {n : ℕ} (i : Fin n) : E n ≃ₗ[ℝ] E n :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans
    ((negCoordLE i).trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm)

/-- Negating a single coordinate preserves the norm (both squares are the sum of
the squares of the coordinates). -/
private lemma coordFlipLE_norm_sq {n : ℕ} (i : Fin n) (x : E n) :
    ‖coordFlipLE i x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k = i <;> simp [coordFlipLE, negCoordLE, negCoord, h]

/-- The orthogonal map negating coordinate `i`, as a `LinearIsometryEquiv`. -/
private def coordFlip {n : ℕ} (i : Fin n) : E n ≃ₗᵢ[ℝ] E n where
  toLinearEquiv := coordFlipLE i
  norm_map' := by
    intro x
    have habs : |‖coordFlipLE i x‖| = |‖x‖| :=
      (sq_eq_sq_iff_abs_eq_abs _ _).mp (coordFlipLE_norm_sq i x)
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs
    exact habs

/-- The coordinate-flip sends coordinate `k` to `-x k` if `k = i` and fixes it otherwise. -/
private lemma coordFlip_apply {n : ℕ} (i : Fin n) (x : E n) (k : Fin n) :
    (coordFlip i x) k = (if k = i then -x k else x k) := by
  simp [coordFlip, coordFlipLE, negCoordLE, negCoord]

/-- The off-diagonal Gaussian second moment is zero: for `i ≠ j`,
`∫ x, (x i) * (x j) * exp (-π‖x‖²) = 0`. -/
lemma second_moment_offdiagonal {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (∫ x : EuclideanSpace ℝ (Fin n), (x i) * (x j) * Real.exp (-Real.pi * ‖x‖ ^ 2)) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let σ : E ≃ₗᵢ[ℝ] E := coordFlip i
  let g : E → ℝ := fun x => (x i) * (x j) * Real.exp (-Real.pi * ‖x‖ ^ 2)
  -- σ negates coordinate i and keeps coordinate j (j ≠ i), and preserves norms.
  have h_neg_i : ∀ x : E, (σ x) i = - x i := by
    intro x
    change (coordFlip i x) i = - x i
    simp [coordFlip_apply i x i]
  have h_keep_j : ∀ x : E, (σ x) j = x j := by
    intro x
    change (coordFlip i x) j = x j
    rw [coordFlip_apply i x j]
    have : j ≠ i := by exact fun hji => hij hji.symm
    simp [this]
  have h_norm : ∀ x : E, ‖σ x‖ = ‖x‖ := by
    intro x
    exact (σ.norm_map x)
  -- g ∘ σ = - g
  have hcomp : (fun x : E => g (σ x)) = fun x : E => - g x := by
    funext x
    unfold g σ
    rw [h_neg_i x, h_keep_j x, h_norm x]
    ring
  -- The main integral is invariant under σ:
  have h_mp : MeasurePreserving (σ : E → E) MeasureTheory.volume MeasureTheory.volume := by
    exact (LinearIsometryEquiv.measurePreserving σ)
  have h_meb : MeasurableEmbedding (σ : E → E) := by
    exact σ.toHomeomorph.measurableEmbedding
  have h_inv : (∫ x : E, g (σ x)) = ∫ x : E, g x := by
    exact (MeasurePreserving.integral_comp h_mp h_meb g)
  -- hence I = -I:
  have h_neg : (∫ x : E, g x) = - (∫ x : E, g x) := by
    calc
      (∫ x : E, g x) = ∫ x : E, g (σ x) := h_inv.symm
      _ = ∫ x : E, - g x := by
        rw [← hcomp]
      _ = - (∫ x : E, g x) := integral_neg (fun x : E => g x)
  linarith

end Commons.Analysis.GaussianMeasure
