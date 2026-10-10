/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.SilvermanReduction.Add
import Submission.Work.SilvermanReduction.Filtration
import Submission.Work.SilvermanReduction.map_redPoint
import Submission.Work.SilvermanReduction.redPoint_surjective
import Submission.Work.SilvermanReduction.tateCurve_hasGoodReduction
import Submission.Work.SilvermanReduction.hasGoodReduction_baseChange
import Submission.Work.SilvermanReduction.Marker
import Submission.Work.SilvermanReduction.TateCurve
import Submission.Work.SilvermanReduction.Conditional
import Submission.Work.SilvermanReduction.Place
import Submission.Work.SilvermanReduction.Residual
import Submission.Work.SilvermanReduction.Sharp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission.Work.SilvermanReduction` — the Silverman reduction-map chapter

`import Submission.Work.SilvermanReduction.All` gives the reduction map on the points of a
Weierstrass curve with good reduction at a discrete valuation (Silverman, *AEC*, VII.2.1–2.2),
its Galois compatibility, the filtration `E(K) ⊇ E₁(K) = ker red` with `E(K)/E₁(K) ↪ Ẽ(k)`, and
the class-(a) instantiation of the pointless-twist chain (`Work.PointlessTwist.HasReductionPlace`,
`PointlessOf`).  See `NOTES.md` for the residual and the roadmap.
-/
