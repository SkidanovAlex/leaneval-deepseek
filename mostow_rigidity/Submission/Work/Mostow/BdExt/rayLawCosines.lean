import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BaryBase

namespace Work.Mostow.BdExt

/-- The hyperbolic law of cosines for two geodesic rays out of the base point: for boundary
points `ξ, η ∈ Sph n` the cosine of the hyperbolic distance between `ray ξ s` and `ray η t` is
`cosh s * cosh t - sinh s * sinh t * ⟪ξ, η⟫`.

This is the second form of the law of cosines `cosh_hdist_lvl` specialised to the rays, using
`tpart (sinh s • ξ) = cosh s` and the bilinearity of the inner product. -/
theorem rayLawCosines (n : ℕ) :
    ∀ (ξ η : Submission.Mostow.E n) (s t : ℝ), ξ ∈ Submission.Mostow.Sph n → η ∈ Submission.Mostow.Sph n →
      Real.cosh (Submission.Mostow.hdist (Work.Mostow.BdExt.ray ξ s) (Work.Mostow.BdExt.ray η t)) =
        Real.cosh s * Real.cosh t - Real.sinh s * Real.sinh t * inner ℝ ξ η := by
  intro ξ η s t hξ hη
  have hξn : ‖ξ‖ = 1 := (Work.Mostow.mem_Sph_iff ξ).mp hξ
  have hηn : ‖η‖ = 1 := (Work.Mostow.mem_Sph_iff η).mp hη
  rw [cosh_hdist, ray, ray, Work.Mostow.tpart_sinh_smul ξ s hξn,
    Work.Mostow.tpart_sinh_smul η t hηn, real_inner_smul_left, real_inner_smul_right]
  ring

end Work.Mostow.BdExt
