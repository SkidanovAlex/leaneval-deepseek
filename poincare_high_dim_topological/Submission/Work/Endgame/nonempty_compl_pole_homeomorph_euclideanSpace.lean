import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

/-!
# The complement of the pole on `𝕊ⁿ` is `ℝⁿ`

Writing `𝕊ⁿ` as the one-point compactification of `ℝⁿ` via the stereographic
homeomorphism `onePointEuclideanHomeomorphSphere n`, the complement of the image
of the point at infinity (`OnePoint.infty`, the "pole") is homeomorphic to `ℝⁿ`.

This is the composite

`ℝⁿ ≃ₜ ({∞}ᶜ : Set (OnePoint ℝⁿ)) ≃ₜ ({(onePointEuclideanHomeomorphSphere n) ∞}ᶜ : Set 𝕊ⁿ)`,

i.e. `complInftyHomeomorph` transported along the restriction of
`onePointEuclideanHomeomorphSphere n` to complements of points
(`homeomorphComplSingleton`).
-/

open Metric (sphere)
open Set Filter Topology
open scoped OnePoint

namespace Work.Endgame

/-- **The complement of the pole in `𝕊ⁿ` is `ℝⁿ`.**

Under the stereographic homeomorphism `onePointEuclideanHomeomorphSphere n`, the
point at infinity of `OnePoint (EuclideanSpace ℝ (Fin n))` is the "pole" of the
sphere; the complement of that pole (with the subspace topology) is homeomorphic
to `EuclideanSpace ℝ (Fin n)`. -/
theorem nonempty_compl_pole_homeomorph_euclideanSpace (n : ℕ) :
    Nonempty (({onePointEuclideanHomeomorphSphere n OnePoint.infty}ᶜ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
        EuclideanSpace ℝ (Fin n)) :=
  ⟨(homeomorphComplSingleton (onePointEuclideanHomeomorphSphere n) OnePoint.infty).symm.trans
    (complInftyHomeomorph (EuclideanSpace ℝ (Fin n)))⟩

end Work.Endgame
