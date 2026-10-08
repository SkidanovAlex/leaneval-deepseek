/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# BSW §3.0 (`BSWExistsXProp`) from the counting proof

`Work.BSW.S3.bsExistsX` is the §3 opening of Bender's proof in the shape of the leaf contract
`Work.BSW.BSWExistsXProp`: an element `x ∉ H^G`, inverted by `t`, with `i(x)` large.  The proof is
`Work.BSW.Cases.exists_notMem_HG_iFn_gt` (`Submission/Work/BSW/Cases/exists_notMem_HG_iFn_gt.lean`),
which carries out the double count `Σ_G i = I² + I` against `Σ_{H^G} i = I(k²−k+2)` and then
conjugates `x` so that `t` inverts it.
-/
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Cases.exists_notMem_HG_iFn_gt

namespace Work.BSW.S3

/-- Bender's §3 opening in the leaf-contract shape. -/
theorem bsExistsX : Work.BSW.BSWExistsXProp := by
  intro G _ _ t s K ε h hk hε hG
  exact Work.BSW.Cases.exists_notMem_HG_iFn_gt ε h hk hε hG

end Work.BSW.S3
