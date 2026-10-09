/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.GenericKernelReduction`: umbrella import

The reduction of Theorem 14 of Schmidt–Wingberg (split embedding problems with finite nilpotent
kernel over `ℚ`) to the generic-kernel statement for each prime, together with the hypothesis
`Work.GenericKernelReduction.GenericKernelSolvable` and the final theorems
`Work.GenericKernelReduction.splitEmbeddingTheoremOverRat_of_genericKernel` and
`Work.GenericKernelReduction.realizable_of_genericKernel`.

See `Submission/Work/GenericKernelReduction/NOTES.md` for the statement of the hypothesis, the
proof plan and the honest list of what is still missing for Shafarevich's theorem.
-/

import Submission.Work.GenericKernelReduction.Defs
import Submission.Work.GenericKernelReduction.SinglePrime
import Submission.Work.GenericKernelReduction.Transport
import Submission.Work.GenericKernelReduction.Nilpotent
import Submission.Work.GenericKernelReduction.Main
import Submission.Work.GenericKernelReduction.exists_equivariant_surjection_freeGroup
import Submission.Work.GenericKernelReduction.exists_equivariant_quotient_freePQuotient
import Submission.Work.GenericKernelReduction.inClosure_of_splitEmbeddingSolvable
import Submission.Work.GenericKernelReduction.inClosure_of_surjective
import Submission.Work.GenericKernelReduction.splitEmbeddingSolvedInClosure_prod
import Submission.Work.GenericKernelReduction.splitEmbeddingSolvedInClosure_pi
import Submission.Work.GenericKernelReduction.sylow_decomposition_equivariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
