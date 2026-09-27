import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A compact Hausdorff space `M` whose complement of a point `p` is homeomorphic to `ℝⁿ` is
homeomorphic to the one-point compactification of `ℝⁿ`.

Indeed, `onePointComplHomeomorph p : OnePoint ({p}ᶜ) ≃ₜ M` identifies `M` with the
one-point compactification of `{p}ᶜ` (the universal property of `OnePoint`,
`OnePoint.equivOfIsEmbeddingOfRangeEq`), and the one-point compactification is functorial
(`Homeomorph.onePointCongr`), so the homeomorphism `{p}ᶜ ≃ₜ ℝⁿ` transports it to a
homeomorphism `M ≃ₜ OnePoint ℝⁿ`. -/
theorem nonempty_homeomorph_onePoint_of_compl_homeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M) (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin n))) :=
  ⟨(onePointComplHomeomorph p).symm.trans h.onePointCongr⟩

end Work.Endgame
