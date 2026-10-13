/-
  WilE6 (area E6): **the closure half of `E6_fiber_closure`, unconditional**.

  From the frozen `E3_taylor_closure` (Gabrielov 1998, Lemma 3.1 — see `NOTES.md`) and the
  frozen `E4_sa_fiber_closure`, the fibrewise closure of an EA semi-Pfaffian set is again EA
  semi-Pfaffian, of format `≤ F` and degree polynomial in `X.deg`:

      E6_closure_proved hE3b hE4 F : ∃ a b, ∀ p q (X : SemiPf (p+q)), X.fmt ≤ F →
        ∃ Y : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set

  The two leading hypotheses are copied verbatim from `Submission/Work/Wilkies/E/Spec.lean`
  (`E3_taylor_closure`, `E4_sa_fiber_closure`); the proof composes the cube saturation of the
  presentation (`Work.WilE6.exists_cubeSaturated`) with the cube-saturated closure assembly
  (`Work.WilE6.E6_closure_cubeSaturated`), via `Work.WilE6.E6_closure_proved_of_parts`.

  The *frontier* conjunct `Y'.set = fiberClosure X.set \ X.set` of the frozen
  `E6_fiber_closure` is not covered: it asks for a polynomial-degree semialgebraic description
  of the complement of a DNF, which needs an effective complement / cell count; see `NOTES.md`.
-/
import Submission.Work.WilE6.Main
import Submission.Work.WilE6.exists_cubeSaturated
import Submission.Work.WilE6.E6_closure_cubeSaturated

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **The closure half of `E6_fiber_closure`.**  `hE3b` and `hE4` are the frozen
`E3_taylor_closure` and `E4_sa_fiber_closure` verbatim. -/
theorem E6_closure_proved
    (hE3b : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
      (y ∈ closure {x | B.holds c x} ↔
        y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
                         (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}))
    (hE4 : ∀ p q : ℕ, ∃ b : Polynomial ℕ, ∀ X : SA (p + q),
      ∃ Y : SA (p + q), Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set)
    (F : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set :=
  E6_closure_proved_of_parts F (exists_cubeSaturated F) (E6_closure_cubeSaturated hE3b hE4 F)

end Work.WilE6
