import Mathlib
import Submission.Work.Drive.psgValDefs

namespace Work.Drive

/- The corner embedding `cornerPt j k a b` hits exactly the points of the box with `j`-coordinate
`a` and `k`-coordinate `b`: it is the identity on those two coordinates, and it is surjective onto
the affine corner `{z | z j = a ∧ z k = b}` of `Amb 4`. -/
theorem cornerPt_data (j k : Fin 5) (hjk : j ≠ k) :
    (∀ (a b : ℝ) (y : Work.Drive.cornerSub j k),
      (Work.Drive.cornerPt j k a b y) j = a ∧ (Work.Drive.cornerPt j k a b y) k = b) ∧
    (∀ (a b : ℝ) (z : Work.Drive.Amb 4), z j = a → z k = b →
      ∃ y : Work.Drive.cornerSub j k, Work.Drive.cornerPt j k a b y = z) := by
  constructor
  · intro a b y
    have h1 := (cornerSub_apply_eq_zero j k y).1
    have h2 := (cornerSub_apply_eq_zero j k y).2
    constructor
    · simp only [cornerPt_coe, e5]
      simp [h1, hjk]
    · simp only [cornerPt_coe, e5]
      simp [h2, Ne.symm hjk]
  · intro a b z hzj hzk
    -- `a • e5 j + b • e5 k` is the point of the corner subspace `(a, b)` whose coordinates
    -- vanish off `{j, k}`, so its translate of `z` is the required kernel element.
    have h1 : cornerLM j k (a • e5 j + b • e5 k) = (a, b) := by
      rw [cornerLM_apply]
      simp [e5, hjk, Ne.symm hjk]
    have h2 : cornerLM j k z = (a, b) := by
      rw [cornerLM_apply, hzj, hzk]
    have hmem : (z - (a • e5 j + b • e5 k)) ∈ cornerSub j k := by
      rw [cornerSub, LinearMap.mem_ker, map_sub, h2, h1, sub_self]
    exact ⟨⟨z - (a • e5 j + b • e5 k), hmem⟩, by simp only [cornerPt_coe]; abel⟩

end Work.Drive
