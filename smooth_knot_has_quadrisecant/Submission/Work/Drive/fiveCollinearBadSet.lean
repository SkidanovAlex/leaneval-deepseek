import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.tangencyBadSet

/-!
# The bad set of five collinear points, in the coefficient space of the perturbation family

This module only *names* the set that `Work.Drive.noFiveCollinear_bad_interior_empty`
(`Submission/Work/Drive/noFiveCollinear_bad_interior_empty.lean`) proves to have empty interior, so
that the Baire assembly of the five-collinear-free density can be stated without repeating the
formula.

`Work.Drive.bad5 r r₀ k` is the set of coefficients `c` in the coefficient ball `Kv r₀` for which
there are five parameters `w₀, …, w₄ ∈ [0, 2π]`, pairwise `≥ 1/(k+1)`-separated on the parameter
circle (`csep`), whose images under the perturbed curve `pertV r c` are collinear (i.e. the two
difference vectors span at most a line).

With `f : Fin 5 → ℝ`, `f = w`, the set is *literally* the set whose empty interior is the statement of
`Work.Drive.noFiveCollinear_bad_interior_empty`; the two formulae are syntactically identical, so the
stub discharges the hypothesis of `Work.Drive.genericNoInflNoFiveDense_of_bad5` by definitional
equality.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **The bad set of five collinear points at separation scale `k`.**  Coefficients in the ball
`Kv r₀` for which the perturbed curve `pertV r c` has five collinear points at five pairwise
`1/(k+1)`-separated parameters of `[0, 2π]`. -/
def bad5 (r : ℝ → Space) (r₀ : ℝ) (k : ℕ) : Set Coeff :=
  {c : Coeff | c ∈ Kv r₀ ∧ ∃ w : Fin 5 → ℝ,
      (∀ i : Fin 5, w i ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ i j : Fin 5, i ≠ j → (1:ℝ)/(k+1) ≤ csep (w i) (w j)) ∧
      (∃ p v : Space, v ≠ 0 ∧ ∀ i : Fin 5, ∃ t : ℝ, pertV r c (w i) = p + t • v)}

end

end Work.Drive
