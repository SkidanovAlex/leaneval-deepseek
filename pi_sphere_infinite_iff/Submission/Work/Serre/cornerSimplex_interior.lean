import Mathlib
import Submission.Work.Serre.simplexBdryGeometry

set_option synthInstance.maxHeartbeats 400000

/-!
# The interior of the corner body

This file computes the (topological) interior of the corner body
`Work.Serre.cornerSimplex n = {y : ℝⁿ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}`, the convex hull of the
origin and the standard basis of `ℝⁿ`:

`interior (cornerSimplex n) = {y : ℝⁿ | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}`.

The two inclusions are proved using:
* the description of the interior of a quadrant `interior {y | ∀ i, a ≤ y i} = {y | ∀ i, a < y i}`
  (`interior_euclideanQuadrant`), together with monotonicity of `interior`;
* the fact that the sum functional `y ↦ ∑ i, y i` is a surjective linear map in positive dimension,
  hence an open map (`LinearMap.isOpenMap_of_finiteDimensional`), so that
  `interior {y | ∑ i, y i ≤ 1} = {y | ∑ i, y i < 1}`;
* the openness of `{y | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}` and `interior_maximal`.
-/

namespace Work.Serre

open Set

noncomputable section

/-- The linear functional `y ↦ ∑ i, y i` on `EuclideanSpace ℝ (Fin n)`. -/
def cornerSum (n : ℕ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun y := ∑ i, y i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[simp] theorem cornerSum_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    cornerSum n y = ∑ i, y i := rfl

theorem cornerSum_continuous (n : ℕ) : Continuous (cornerSum n) :=
  LinearMap.continuous_of_finiteDimensional _

/-- In positive dimension the sum functional is surjective. -/
theorem cornerSum_surjective (m : ℕ) : Function.Surjective (cornerSum (m + 1)) := by
  intro c
  refine ⟨WithLp.toLp 2 (fun i : Fin (m + 1) => if i = 0 then c else 0), ?_⟩
  show ∑ i : Fin (m + 1), (if i = 0 then c else 0) = c
  simp

/-- In positive dimension the sum functional is an open map. -/
theorem cornerSum_isOpenMap (m : ℕ) : IsOpenMap (cornerSum (m + 1)) :=
  LinearMap.isOpenMap_of_finiteDimensional _ (cornerSum_surjective m)

/-- The interior of the closed half-space `{y | ∑ i, y i ≤ 1}` in `ℝⁿ`, `n ≥ 1`. -/
theorem interior_sum_le_one (m : ℕ) :
    interior {y : EuclideanSpace ℝ (Fin (m + 1)) | ∑ i, y i ≤ 1} = {y | ∑ i, y i < 1} :=
  by
  have h := (cornerSum_isOpenMap m).preimage_interior_eq_interior_preimage
    (cornerSum_continuous (m + 1)) (Iic (1 : ℝ))
  rw [interior_Iic] at h
  change interior ((fun y : EuclideanSpace ℝ (Fin (m + 1)) => ∑ i, y i) ⁻¹' Iic 1)
      = (fun y : EuclideanSpace ℝ (Fin (m + 1)) => ∑ i, y i) ⁻¹' Iio 1
  exact h.symm

/-- The interior of a quadrant of `ℝⁿ` is the corresponding open quadrant. -/
theorem interior_quadrant_pos (n : ℕ) :
    interior {y : EuclideanSpace ℝ (Fin n) | ∀ i, (0 : ℝ) ≤ y i} =
      {y | ∀ i, (0 : ℝ) < y i} :=
  interior_euclideanQuadrant n 2 0

theorem cornerSimplex_interior (n : ℕ) :
    interior (Work.Serre.cornerSimplex n) =
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} := by
  rcases n with _ | m
  · rw [interior_cornerSimplex_zero]
    ext y
    simp
  · -- The corner body is contained in both the closed quadrant and the closed half-space.
    have hsubQ : cornerSimplex (m + 1) ⊆
        {y : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, (0 : ℝ) ≤ y i} := fun y hy => hy.1
    have hsubH : cornerSimplex (m + 1) ⊆
        {y : EuclideanSpace ℝ (Fin (m + 1)) | ∑ i, y i ≤ 1} := fun y hy => hy.2
    have h1 : interior (cornerSimplex (m + 1)) ⊆
        {y : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, (0 : ℝ) < y i} := by
      have h := interior_mono hsubQ
      rwa [interior_quadrant_pos] at h
    have h2 : interior (cornerSimplex (m + 1)) ⊆
        {y : EuclideanSpace ℝ (Fin (m + 1)) | ∑ i, y i < 1} := by
      have h := interior_mono hsubH
      rwa [interior_sum_le_one] at h
    -- The open corner body is open and contained in the corner body.
    have hQopen : IsOpen {y : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, (0 : ℝ) < y i} := by
      rw [← interior_quadrant_pos (m + 1)]
      exact isOpen_interior
    have hHopen : IsOpen {y : EuclideanSpace ℝ (Fin (m + 1)) | ∑ i, y i < 1} := by
      have hset : {y : EuclideanSpace ℝ (Fin (m + 1)) | ∑ i, y i < 1} =
          cornerSum (m + 1) ⁻¹' Iio (1 : ℝ) := rfl
      rw [hset]
      exact isOpen_Iio.preimage (cornerSum_continuous (m + 1))
    have hTopen : IsOpen
        {y : EuclideanSpace ℝ (Fin (m + 1)) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} := by
      rw [Set.ofPred_and]
      exact hQopen.inter hHopen
    have hTsub : {y : EuclideanSpace ℝ (Fin (m + 1)) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} ⊆
        cornerSimplex (m + 1) := fun y hy => ⟨fun i => le_of_lt (hy.1 i), le_of_lt hy.2⟩
    refine subset_antisymm ?_ ?_
    · intro y hy
      exact ⟨h1 hy, h2 hy⟩
    · exact interior_maximal hTsub hTopen

end

end Work.Serre
