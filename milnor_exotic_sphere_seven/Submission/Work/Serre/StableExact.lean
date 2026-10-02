import Submission.Work.Serre.Engine
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.fibrationLES_of_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# K5: the Serre exact sequence in the stable range

Blueprint ADDENDUM 2, K5.  For a Serre fibration `p : E → B` with `B` `(b-1)`-connected and the
fibre over `b₀` `(f-1)`-connected, the map of pairs `(E, F) → (B, b₀)` induces an isomorphism on
homology in degrees `< b + f`.

The proof (K5) is the cellular induction of ADDENDUM 2: take a CW approximation `Γ → B` which is
`b`-reduced (K1, RATHUREWICZ), pull `p` back (K3), and induct on the skeleta using the cell step
`K4` together with the long exact sequences of the pairs `(E|Γ_j, E|Γ_{j-1})` and the five lemma.

This is *verbatim* the target of subproject STEMSB (`Work.StemsB.SerreExactRange`), whose
transgression form `Work.StemsB.SerreExactTransgression` is what area RATHUREWICZ consumes for the
rational Hurewicz theorem; so discharging it here also discharges STEMSB's Serre-exactness goal.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

namespace Work.Serre

noncomputable section

/-- **K5: the Serre exact sequence in the stable range**, for Serre fibrations.  If `B` is
`(b-1)`-connected and the fibre of `p` over `b₀` is `(f-1)`-connected, then
`p` induces `H_i(E, F) ≅ H_i(B, {b₀})` for `i < b + f` (equivalently, by the long exact sequence
of the pair, `H_i(E, F) → H_i(B, {b₀})` is an isomorphism in the stable range). -/
def SerreStableExact : Prop :=
  ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B)),
    Work.StemsB.IsSerreFibration p → ∀ (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (b f : ℕ),
      1 ≤ b →
      (∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) →
      (∀ i < f, Subsingleton (HomotopyGroup (Fin i) (↥{x : E | p x = b₀}) ⟨e₀, he₀⟩)) →
      ∀ i : ℕ, i < b + f → IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)

/-- **A correction to STEMSB's statement.**  `Work.StemsB.SerreExactRange` does *not* carry the
hypothesis `1 ≤ b`, and without it the statement is **false**: for a *discrete* base
`B = {b₀,b₁}` and `E = {e₀,e₁,e₁'}` with `p e₀ = b₀`, `p e₁ = p e₁' = b₁` (all points isolated),
`p` is a Serre fibration (every map from a connected cube to a discrete space is constant), the
fibre over `b₀` is a point, and yet `H₀(E,F) = ℤ² → H₀(B,{b₀}) = ℤ` is not an isomorphism.  The
corrected statement `SerreExactRangeCorrected` below carries `1 ≤ b`; it is what K5 gives, and it
is the form every application uses (`b ≥ 2` there).  Reported to subproject STEMSB. -/
def SerreExactRangeCorrected : Prop :=
  ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B)),
    Work.StemsB.IsHurewiczFibration p → ∀ (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (b f : ℕ),
      1 ≤ b →
      (∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) →
      (∀ i < f, Subsingleton (HomotopyGroup (Fin i) (↥{x : E | p x = b₀}) ⟨e₀, he₀⟩)) →
      ∀ i : ℕ, i < b + f → IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)

/-- **K5 discharges (the corrected form of) STEMSB's target** `Work.StemsB.SerreExactRange`: the
Serre statement implies the Hurewicz one with the necessary hypothesis `1 ≤ b`.  See the discussion
of `SerreExactRangeCorrected` for why `1 ≤ b` cannot be dropped. -/
theorem serreExactRangeCorrected_of_stableExact (h : SerreStableExact) :
    SerreExactRangeCorrected := by
  intro E _ B _ p hp e₀ b₀ he₀ b f hb hbconn hfconn i hi
  exact h E B p (Work.StemsB.IsHurewiczFibration.isSerreFibration hp) e₀ b₀ he₀ b f hb
    hbconn hfconn i hi

end

end Work.Serre
