/-
  Work.WilE2 — area E2.  Interface for the components theorem.

  The frozen `E2_components` is reduced (in `E2_components_of_basic`) to the components of a
  *single* basic set (equations `= 0` plus strict inequalities `> 0`, cut by the cube).  That
  bound is proved in two steps, following Gabrielov–Vorobjov, *Complexity of computations with
  Pfaffian and Noetherian functions*, §3 (`sources/wilkiesE/GV02.txt`, Corollary 3.3 and
  Theorem 3.7);

  * `VarietyBound F` — Corollary 3.3: the components of the zero set `{f = 0}` of `k` EA
    functions (cut by the cube, so no `R`-truncation is needed) are polynomially bounded, the
    polynomial depending on the format bound `F`.  Its proof uses Khovanskii (`E2a`) for the
    number of non-degenerate solutions of the Morse system
    `F = ∂F/∂x_2 = ⋯ = ∂F/∂x_n = 0`, `F := Σ f_i² + ε(‖x‖² − R)`, after a generic rotation of the
    coordinates.
  * the sign-assignment step (Theorem 3.7): a basic set is one consistent sign assignment, and the
    components of one sign assignment are dominated by those of the variety
    `{∏ (g ± ε)² = δ}`, to which `VarietyBound` applies.
-/
import Mathlib
import Submission.Work.WilE2.KhoGood

set_option autoImplicit false

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- **GV Corollary 3.3** in the EA vocabulary: the components of the zero set of a finite family
of EA functions, cut by the cube, have polynomially bounded hitting sets. -/
def VarietyBound (F : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (g : Finset (EAPoly k r)), k + r ≤ F →
    ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval (∑ f ∈ g, atomDeg f) ∧
      (↑s : Set (Fin k → ℝ)) ⊆ cubeC k ∩ {x | ∀ f ∈ g, eaEval c f x = 0} ∧
      ∀ x ∈ cubeC k ∩ {x | ∀ f ∈ g, eaEval c f x = 0}, ∃ y ∈ s,
        connectedComponentIn (cubeC k ∩ {x | ∀ f ∈ g, eaEval c f x = 0}) x
          = connectedComponentIn (cubeC k ∩ {x | ∀ f ∈ g, eaEval c f x = 0}) y

end Work.WilE2
