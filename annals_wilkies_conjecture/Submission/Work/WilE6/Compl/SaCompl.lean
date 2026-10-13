/-
  WilE6 / Compl: **the effective complement of a restricted semi-Pfaffian set**, unconditional
  given the frozen `E2_components`.

  This is the one input the *frontier* conjunct of `E6_fiber_closure` needs beyond
  `E3_taylor_closure` and `E4_sa_fiber_closure` (both of which are closure statements and
  therefore cannot describe a *complement*): see `NOTES.md`.

  * `Work.WilE6.Compl.SaComplAux.saCompl_of` is the construction, with the two analytic
    ingredients as explicit hypotheses (`CellCountHyp`, `CellMeetHyp`);
  * `Work.WilE6.Compl.cellCountAll` (delegated) supplies `CellCountHyp` from `E2_components`
    (Khovanskii's component count, the same input area E5 consumes);
  * `Work.WilE6.Compl.cell_holds_of_meets` (delegated) supplies `CellMeetHyp`.
-/
import Mathlib
import Submission.Work.WilE6.Compl.SaComplAux
import Submission.Work.WilE6.Compl.cellCountAll
import Submission.Work.WilE6.Compl.cell_holds_of_meets

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE6.Compl
open WilkiesDesign WilkiesDesign.E

/-- **The effective complement of a `SemiPf`-set** (the `hcompl` hypothesis of
`Work.WilE6.E6_fiber_closure_proved_of_complement`), from the frozen `E2_components` verbatim.

For a list `basics` of basic sets over a chain `c : EAChain k r` with `k + r ≤ F`, the complement
of `X.set` (`X := ⟨r, c, basics⟩`) inside the cube is again a union of basic sets over the *same*
chain `c`, with degree bounded by a polynomial in `X.deg` (depending only on `F`). -/
theorem saCompl_proved
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∀ (F : ℕ), ∃ (p : Polynomial ℕ), ∀ (k r : ℕ) (c : EAChain k r) (basics : List (Basic k r)),
      k + r ≤ F → ∃ (basics' : List (Basic k r)),
        (basics'.map Basic.deg).sum ≤ p.eval ((basics.map Basic.deg).sum) ∧
        {x : Fin k → ℝ | x ∈ cubeC k ∧ ∃ B ∈ basics', B.holds c x} =
          cubeC k \ {x : Fin k → ℝ | x ∈ cubeC k ∧ ∃ B ∈ basics, B.holds c x} :=
  fun F => saCompl_of F (cellCountAll hE2 F) cell_holds_of_meets

end Work.WilE6.Compl
