/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pointer module: the local embedding `K_vˣ → K_wˣ` at the same place

Aggregator (no declarations of its own), so that lemmas about
`NK.GlobalCFT.Place.localAlgebraMapUnits` can be *requested* in this workspace: the request
machinery can only name dependencies under `Submission/Work/`, and this module imports the NK
files that define and describe the local embeddings.
-/

import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.LocalInputs.Degree.localDegree_rat
import Submission.NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
