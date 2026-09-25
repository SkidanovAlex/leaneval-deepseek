import Mathlib
import Submission.Work.ConCohomology.Defs

namespace Work.ConCohomology

/-- When the action of `G` on `M` is trivial, the `1`-cocycle condition
`f (σ * τ) = f σ + σ • f τ` collapses to additivity of `f` on the nose. -/
lemma isCocycle1_iff_of_trivial {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] (htriv : ∀ (σ : G) (m : M), σ • m = m) (f : G → M) :
    IsCocycle1 f ↔ ∀ σ τ : G, f (σ * τ) = f σ + f τ := by
  constructor
  · intro h σ τ
    simpa [htriv] using h σ τ
  · intro h σ τ
    simpa [htriv] using h σ τ

end Work.ConCohomology
