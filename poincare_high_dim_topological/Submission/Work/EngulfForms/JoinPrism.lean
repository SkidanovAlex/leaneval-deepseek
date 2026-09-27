import Submission.Work.EngulfForms.Prelude

/-!
# A1: the join-prism form `JoinPrismForm`

`Work.Engulf.JoinPrismForm N` is blueprint `G2` (Newman §13): the join of two disjoint simplices
`τ₀ ∪ τ₁` of card `q + 2` in `E N` (with `q + 1 ≤ N`) is affinely equivalent to a prism
`E (N - q - 1) × E q × ℝ` whose floor and top are the prescribed facets.  It is an immediate
weakening of A1's `Work.Geo.Prism.join_simplex_prism`: the form drops the two extra conjuncts
`ConvexPL γ₀` and `ConcavePL γ₁` from the existential.
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms

/-- **A1**: the join-prism form, from `Work.Geo.Prism.join_simplex_prism`. -/
theorem joinPrismForm (N : ℕ) : JoinPrismForm N := by
  intro q hq τ₀ τ₁ hne₀ hne₁ hdisj hcard hind
  obtain ⟨T, F, γ₀, γ₁, hFc, hFcv, hγ₀, hγ₁, -, -, hle, hfr, h4, h5, h6⟩ :=
    Work.Geo.Prism.join_simplex_prism hq τ₀ τ₁ hne₀ hne₁ hdisj hcard hind
  exact ⟨T, F, γ₀, γ₁, hFc, hFcv, hγ₀, hγ₁, hle, hfr, h4, h5, h6⟩

end Work.EngulfForms
