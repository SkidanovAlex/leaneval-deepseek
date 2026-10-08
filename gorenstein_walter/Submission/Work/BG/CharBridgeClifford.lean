import Submission.Work.BG.CharBridge
import Submission.OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import Submission.OddOrder.GroupTheory.RepresentationTheory.InflationCharacter

/-!
# Aggregator: the OddOrder character library plus Clifford single-orbit / inflation

Area BG helper module.  It re-exports

* everything of `Submission.Work.BG.CharBridge` (the Feit–Thompson character library of
  `Submission/OddOrder/GroupTheory/RepresentationTheory`, Apache-2.0), and
* two further character-theory modules of the same third-party library that area `BG`
  needs for the "kernel of a `σ`-invariant irreducible character" argument of
  Gorenstein–Walter / Bender–Glauberman Lemma 3.6:
  * `CliffordSingleOrbit` — `restrictionConstituentsSingleOrbit_of_isIrreducible`,
    `restrict_eq_restrictionMultiplicity_smul_of_invariant`;
  * `InflationCharacter` — `IsIrreducibleCharacter.compHom_of_surjective`.

Delegated lemmas in area `BG` can depend on this module when they need those two APIs.
-/
