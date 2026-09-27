import Mathlib

namespace Work.Drive

/-- If a linear map `f : ℝ^5 → ℝ^4` maps the face `{v | v j = 0}` onto the whole target,
then some nonzero vector of the kernel of `f` has nonzero `j`-th coordinate.

Indeed, let `u = single j 1` (so `u j = 1`) and pick `v` in the face with `f v = f u`
(possible by the face-surjectivity hypothesis).  Then `σ = u - v` satisfies `f σ = 0`
and `σ j = u j - v j = 1 ≠ 0`. -/
theorem exists_kernel_ne_zero_of_face_surjective
    (f : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (j : Fin 5) (hsurj : Function.Surjective f)
    (hface : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 5) // v j = 0} => f v.1)) :
    ∃ σ : EuclideanSpace ℝ (Fin 5), f σ = 0 ∧ σ j ≠ 0 := by
  have _ := hsurj (0 : EuclideanSpace ℝ (Fin 4))
  obtain ⟨v, hv⟩ := hface (f (EuclideanSpace.single j 1))
  have hv' : f v.1 = f (EuclideanSpace.single j 1) := hv
  refine ⟨EuclideanSpace.single j 1 - v.1, ?_, ?_⟩
  · rw [map_sub, hv', sub_self]
  · simp [v.2]

end Work.Drive
