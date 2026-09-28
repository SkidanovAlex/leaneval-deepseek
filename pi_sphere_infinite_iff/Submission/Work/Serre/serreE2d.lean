import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.E2dInduction

/-!
# E2(d): the `E¹` page of the Serre filtration over a cube

`Work.Serre.SerreE2d` is the identification of the first page of the Serre filtration: for a Serre
fibration `p : E → B`, a map `τ : Iⁿ → B` and a point `d₀ : Iⁿ`, the relative homology of the
pullback over the cube pair `(Iⁿ, ∂Iⁿ)` is the homology of the fibre over `τ d₀`, shifted by `n`:

  `H_{k+n}(τ^*E, τ^*E|_{∂Iⁿ}) ≅ H_k(p⁻¹(τ d₀))`.

The proof is the induction developed in `Submission/Work/Serre/E2d*.lean` (see
`E2dInduction.lean` for the composition of the five isomorphisms of the induction step).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

theorem serreE2d : Work.Serre.SerreE2d := by
  intro E B _ _ p n hp τ d₀ k
  exact e2dAll n E B p hp τ d₀ k

end Work.Serre
