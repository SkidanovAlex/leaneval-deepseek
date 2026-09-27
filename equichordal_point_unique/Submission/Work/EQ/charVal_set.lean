import Mathlib
import Submission.Work.EQ.DefsCore

/-!
# The set of characteristic values is countable

Rychlik's Theorem 11 (step (141)) needs the set

`M = {1} ∪ {charVal a h ε | fan a h ε 0 = A₁}`

of "characteristic values" to be **countable**.  This is immediate: `List Bool` is countable and `M`
is the image of `List Bool` under `charVal a h` together with the single point `1`.  (The finer
`Work.EQ.charVal_props` — real, in `(0,1]`, only finitely many above any `η > 0` — is not needed for
the countability, only for the convergence in case (ii) of the trichotomy.)
-/

namespace Work.EQ

open Filter _root_.Topology

/-- Rychlik's set of characteristic values: `1` together with the characteristic values of the fan
words returning to the stable centre `A₁ = (-1/2, 0)`. -/
def charValSet (a : ℝ) (h : ℂ → ℂ) : Set ℂ :=
  {μ : ℂ | μ = 1 ∨ ∃ ε : List Bool, fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧ charVal a h ε = μ}

/-- **The set of characteristic values is countable.** -/
theorem countable_charValSet (a : ℝ) (h : ℂ → ℂ) : (charValSet a h).Countable := by
  refine Set.Countable.union (Set.countable_singleton (1 : ℂ)) ?_
  refine Set.Countable.mono ?_
    (Set.countable_univ.image (fun ε : List Bool => charVal a h ε))
  rintro μ ⟨ε, -, rfl⟩
  exact ⟨ε, trivial, rfl⟩

end Work.EQ
