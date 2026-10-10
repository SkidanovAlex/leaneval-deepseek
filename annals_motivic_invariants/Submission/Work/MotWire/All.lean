/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotWire
-/
import Submission.Work.MotWire.Defs
import Submission.Work.MotWire.linkCertTInput_of_charNeFive
import Submission.Work.MotWire.infinite_functionField
import Submission.Work.MotWire.MotV5Input
import Submission.Work.MotWire.CertN3
import Submission.Work.MotWire.Minimal
import Submission.Work.MotWire.Wire

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/MotWire` — the wire from `Submission.lean`'s six holes to the delivered results

Read `Submission/Work/MotWire/README.md` first; the short version is

* the six statements of `Submission.lean` are proved in
  `Submission/Work/MotWire/Wire.lean` (`Work.MotWire.theorem_1_2_1_a`, `…_b`, `…_c`, `…_d`,
  `Work.MotWire.theorem_1_2_2`, `Work.MotWire.theorem_1_2_3`) from the delivered results of this
  workspace, with the single extra hypothesis `Work.MotWire.CharFiveInput`;
* `Work.MotWire.CharFiveInput` is the *only* named input of the area; it is the characteristic-`5`
  statement that no delivered route produces yet;
* `Work.MotWire.MotV5LinkCertInput` + `Work.MotWire.charFiveInputN4_of_motV5` show that the
  `n ≥ 4` half of `CharFiveInput` is exactly the certificate hypothesis of the delivered
  `Work.MotV5.not_gen_charFive_all_of_linkCert`, so only its `n = 3` half
  (`Work.MotWire.CharFiveInputThree`) is new content;
* `Submission/Work/MotWire/Patch.lean` (a separate module, importing the real `Submission.lean`)
  re-proves the six holes and checks that the binder lists agree;
* `Work.MotWire.not_gen_three_of_linkCert` (`Submission/Work/MotWire/CertN3.lean`) is the
  `n = 3` *certificate level*: a `K`-level `Work.MotV.LinkCert` with `ConstantsOnly` and rigidity
  already forces `¬ GenByPseudoRegularizable K 3`, which is the precise target of the
  characteristic-`5` residual.

The declarations here are `sorry`-free; the axiom footprint of the six theorems is exactly the
axiom footprint of `CharFiveInput` (see `Submission/Work/MotWire/Axioms.lean`).
-/
