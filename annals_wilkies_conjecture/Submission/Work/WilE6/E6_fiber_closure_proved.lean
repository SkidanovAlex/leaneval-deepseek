/-
  WilE6: **the frozen `WilkiesDesign.E.E6_fiber_closure`, concluded.**

      E6_fiber_closure_proved hE3b hE4 hE2 :
        ∀ F, ∃ a b, ∀ p q (X : SemiPf (p + q)), X.fmt ≤ F →
          ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
            Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
            Y'.set = fiberClosure X.set \ X.set

  The two leading hypotheses `hE3b` and `hE4` are the frozen `E3_taylor_closure` and
  `E4_sa_fiber_closure`, copied verbatim.  The *third* leading hypothesis `hE2` is
  `E2_components`, also copied verbatim, and it is **not** avoidable here:

  * both `E3_taylor_closure` and `E4_sa_fiber_closure` are statements about *closures*
    (of a basic set, resp. of the fibres of a semialgebraic set).  The frontier conjunct asks
    for `fiberClosure X.set \ X.set`, i.e. it has to *remove* the points of `X`; that requires a
    description of the complement `cubeC \ X.set` of a DNF-presented set;
  * such a description is a union of the sign cells of the atoms of `X` that are disjoint from
    `X.set`, and a *polynomial* bound on the degree therefore needs the number of *realizable
    sign conditions* to be polynomial, which is Khovanskii's component count
    (`E2_components`); see `NOTES.md` for the details;
  * Gabrielov 1998, Theorem 1.1, obtains the frontier from the closure with the bound
    `N'' = N' L^N` — exponential in the number `N` of elementary sets, hence not polynomial in
    `X.deg`.  The frozen statement (polynomial in `X.deg`) is therefore strictly stronger than
    the source's Theorem 1.1, and the extra strength comes from the effective sign-condition
    count, i.e. from `E2_components`.  (GV02, Thm. 5.2, gives the polynomial count for the
    same reason.)

  The closure half alone, `Work.WilE6.E6_closure_proved`, needs only `hE3b` and `hE4`.
  The complement is isolated as `Work.WilE6.Compl.saCompl_proved`, whose only hypothesis is
  `hE2`; it is what the paper's "∂X = X̄ \ X" step costs in this formalisation.
-/
import Mathlib
import Submission.Work.WilE6.E6_fiber_closure_proved_of_complement
import Submission.Work.WilE6.Compl.SaCompl

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **The frozen `E6_fiber_closure`**, from `E3_taylor_closure`, `E4_sa_fiber_closure` and
`E2_components` (all three verbatim). -/
theorem E6_fiber_closure_proved
    (hE3b : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
      (y ∈ closure {x | B.holds c x} ↔
        y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
                         (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}))
    (hE4 : ∀ p q : ℕ, ∃ b : Polynomial ℕ, ∀ X : SA (p + q),
      ∃ Y : SA (p + q), Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∀ (F : ℕ), ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
        Y'.set = fiberClosure X.set \ X.set :=
  fun F => E6_fiber_closure_proved_of_complement hE3b hE4 (Compl.saCompl_proved hE2) F

end Work.WilE6
