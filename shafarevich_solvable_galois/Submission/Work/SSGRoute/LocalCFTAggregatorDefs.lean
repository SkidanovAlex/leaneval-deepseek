/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pointer module: local class field theory at a `p`-adic completion

Aggregator (no declarations of its own), so that lemmas about the local reciprocity law at a
completion `Q.adicCompletion K` (norm groups, the norm index theorem, the existence theorem and
the local Artin map) can be *requested* in this workspace: the request machinery can only name
dependencies under `Submission/Work/`.
-/

import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalCFT.Reduction.Classical
import Submission.NK.NUV2.Final.Assembly
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
