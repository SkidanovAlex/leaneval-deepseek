/-
Copyright: the martinet_totally_real_towers team.

# The long exact sequence of a short exact sequence of coefficient modules

This module collects the six exactness statements of the long exact sequence associated with a
short exact sequence `0 → A → B → C → 0` of discrete `G`-modules (`Work.ConCohomology.CoeffSES`),
in the form of one imported module per spot:

* `Work.ConCohomology.exact_H0_C`  : exactness at `H⁰(G,C)`
* `Work.ConCohomology.exact_H1_A`  : exactness at `H¹(G,A)`
* `Work.ConCohomology.exact_H1_B`  : exactness at `H¹(G,B)`
* `Work.ConCohomology.exact_H1_C`  : exactness at `H¹(G,C)`
* `Work.ConCohomology.exact_H2_A`  : exactness at `H²(G,A)`
* `Work.ConCohomology.exact_H2_B`  : exactness at `H²(G,B)`

so that the sequence
`0 → H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → H¹(C) → H²(A) → H²(B) → H²(C)`
(with connecting maps `Work.ConCohomology.connecting0`, `connecting1`) is exact at all of these
spots, each stated as `map x = 0 ↔ ∃ y, other y = x`.
-/

import Submission.Work.ConCohomology.Connecting
import Submission.Work.ConCohomology.exact_H0_C
import Submission.Work.ConCohomology.exact_H1_A
import Submission.Work.ConCohomology.exact_H1_B
import Submission.Work.ConCohomology.exact_H1_C
import Submission.Work.ConCohomology.exact_H2_A
import Submission.Work.ConCohomology.exact_H2_B
