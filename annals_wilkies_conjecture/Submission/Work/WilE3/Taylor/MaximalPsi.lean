/-
  annals_wilkies_conjecture, AREA E3 (`Submission.Work.WilE3`): Gabrielov's maximal-`ψ` node.

  The frozen `E3_taylor_closure` is a biconditional; its `(⇐)` direction is proved in this
  directory from the residual Łojasiewicz inequality (`Work.WilE3.Taylor.hasLoj_of_multiplicity`,
  from `Work.WilE3.MultiplicityBound`).  The `(⇒)` direction must not be assumed: the node it needs
  is Gabrielov 1998, DCG 19, Lemma 2.3 together with the proof of Lemma 2.5
  (`sources/wilkiesE/vision/gabrielov1998_frontier/p0007.md`–`p0008.md`), a *non-directional*
  statement about the set where `ψ = min_j g_j` is maximal on the spheres `|x| = max_i |x_i|`.

  Formalised here in the frozen vocabulary, in the "good approximating points" form: near every
  limit point `y` of the basic set, and for every `κ` above the format threshold, there are points
  `z` at distance `< ε` from `y` at which every equation is small to order `κ ^ 2` *with a margin*
  and every strict inequality exceeds `dist (z,y) ^ κ` *with a margin*.  The margins (`a = 1/2`,
  `b = 2`) are what let the effective Taylor remainder (`Work.WilE3.API.eaTaylor_remainder`) be
  absorbed when deriving the Taylor conditions of `taylorSet`; they are exactly Gabrielov's freedom
  in choosing `a, b > 0`, and this statement mentions neither `eaTaylor` nor the closure of a Taylor
  set, so it is not the direction it is used to prove.  Its own input is the effectively nonsingular
  decomposition (GV Cor. 4.7), which area E3 now proves as `Work.WilE3.E3_identity_proved`.
-/
import Submission.Work.WilE3.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E
namespace Work.WilE3

/-- Gabrielov 1998's maximal-`ψ` estimate, in the frozen vocabulary (`κ` above the format's
threshold `K.eval B.deg`; margins `a = 1/2`, `b = 2` as in `φ ≤ a ψ^ν`, `ψ > b |x|^κ`). -/
def MaximalPsiNode (F : ℕ) : Prop :=
  ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ)
      (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
    y ∈ closure {x | B.holds c x} →
    ∀ ε : ℝ, 0 < ε → ∃ z : Fin k → ℝ, dist z y < ε ∧
      (∀ f ∈ B.eqs, 2 * |eaEval c f z| ≤ dist z y ^ (κ ^ 2)) ∧
      (∀ g ∈ B.pos, 2 * dist z y ^ κ < eaEval c g z)

end Work.WilE3
