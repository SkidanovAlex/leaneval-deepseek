/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The residual inputs of the ring half, at a fixed universe

`Work.ORFinal.theorem_1_1_of_hughesFree` needs the ring half's inputs at two universes: at `0`
(for the input of the group half, which is stated for groups in `Type 0` with coefficients
`ULift.{0} ℚ`) and at the universe of the coefficient field `K`.  Universes in Lean cannot be
quantified over inside a hypothesis, so — exactly as `Work.ORDunwoody.Hypotheses` does with its
anchor `Y` — the inputs at a universe are bundled into a structure `Work.ORFinal.FinalInput X`,
where the *only* role of the type `X` is to pin the universe to that of `X`.

`FinalInput X` has **two** fields, both at the universe of `X`:

* `hdiv` — **node N6**, in the form in which the JZLA20 engine is stated
  (`Work.ORHughesFree.hughesFree_exists_locallyIndicable` takes `[LocallyIndicable G]`):
  `Work.ORFinal.DivLoc K G φK`, i.e. for every *locally indicable* subgroup `H ≤ G`, the division
  closure `D H` of `K[H]` in `U(G)` is a division ring.  Nothing else of the Linnell datum — `D`,
  minimality, division-closedness, Linnell independence (I1)/(I1′) and conjugation (I2) — is
  assumed: they are *derived* from node N5's envelope in
  `Submission/Work/ORBridgeLinnell/Bridge.lean`, and `Work.ORFinal.hughesFreeInput_of_div` shows
  that `DivLoc` *alone* produces the M1 bridge's `HughesFreeInput` for a one-relator group
  (node N4 supplies local indicability of torsion-free subgroups, and node N7's Ore-field
  statement is then a theorem, `Work.ORFinal.oreFieldFrac_of_divLoc`).
* `hTor` — **nodes N3 + N8 + N9 + N1** (JL §5, Theorem 5.6): the flatness conclusion
  `Tor₂^{K[G]}(D(G), -) = 0` at the datum built from the above, for the *nontrivial* relators
  `r : FreeGroup (Fin n)`, `r ≠ 1`.  The trivial relator is discharged in
  `Submission/Work/ORFinal/FreeCase.lean` (`Work.ORFinal.flatConcl_free`), and so is node N3's
  global dimension bound in that case (`Work.ORFinal.globalDim_le_two_free`,
  `Work.ORFinal.globalDim_le_two_free_ulift`).

Node N7's Ore-field statement is therefore **not** a field any more: it was removed from this
structure once `Work.ORFinal.oreFieldFrac_of_divLoc` (this directory) proved it from `hdiv`.

Node N4 enters as a **theorem** (`Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable`),
not as a hypothesis: in particular the `IsMulTorsionFree` requirement of
`Work.ORAssembly.RingInputs` is replaced by local indicability plus
`Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn`.
-/
import Submission.Work.ORFinal.AnalyticInput

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORFinal

/-- **The residual inputs of the ring half at the universe of the anchor `X`.**

The anchor `X` plays no mathematical role; it pins the universe, just as in
`Work.ORDunwoody.Hypotheses`. -/
structure FinalInput (X : Type u) where
  /-- **Node N6** in the form of the JZLA20 engine: for every locally indicable subgroup `H`, the
  division closure `D H` of the M1 bridge is a division ring. -/
  hdiv : ∀ (K : Type u) [Field K] (G : Type u) [Group G] [Countable G] (φK : K →+* ℂ),
    DivLoc K G φK
  /-- **Nodes N3 + N8 + N9 + N1**: the flatness conclusion of JL §5 at the datum built from the
  above, for nontrivial relators. -/
  hTor : ∀ (K : Type u) [Field K] [CharZero K] (n : ℕ) (r : FreeGroup (Fin n)), r ≠ 1 →
    ∀ (φK : K →+* ℂ)
      (hin : Work.ORBridgeLinnell.HughesFreeInput K
        (ULift.{u, 0} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
        (Work.ORBridgeLinnell.countableEnvelope
          (ULift.{u, 0} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) φK),
    FlatConcl K φK hin

end Work.ORFinal
