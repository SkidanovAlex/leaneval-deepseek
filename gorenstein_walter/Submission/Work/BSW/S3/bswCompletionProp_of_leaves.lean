/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# BSW §3: `BSWCompletionProp` from the leaves

`Work.BSW.S3.bswCompletionProp_of_leaves` assembles Bender §3 from the proved leaves
`bsExistsX` (§3.0), `s31` (§3.1), `s34Arith` (§3.3/3.4 arithmetic), `case1` (§3.3, ε = +1) and
`s35` (§3.5), leaving only the §3.2 coset count (`BSWS32Prop`) and the §3.8 conclusion
(`BSWS38Prop`) as explicit hypotheses:

```
Work.BSW.S3.bswCompletionProp_of_leaves : BSWS32Prop → BSWS38Prop → BSWCompletionProp
```

Once `S3/s32` and `S3/s38` are in place the hypotheses are discharged by `Work.BSW.S3.s32` and
`Work.BSW.S3.s38`.
-/
import Submission.Work.BSW.S3.bsExistsX
import Submission.Work.BSW.S3.s31
import Submission.Work.BSW.S3.s34Arith
import Submission.Work.BSW.S3.case1
import Submission.Work.BSW.S3.s35
import Submission.Work.BSW.S3.s38
import Submission.Work.BSW.S3.s32
import Submission.Work.BSW.S3.bswCompletionPropFromLeaves

namespace Work.BSW.S3

/-- Bender §3, from the §3.0/3.1/3.3/3.4/3.5 leaves and the two remaining leaf contracts. -/
theorem bswCompletionProp_of_leaves (h32 : Work.BSW.BSWS32Prop) (h38 : Work.BSW.BSWS38Prop) :
    Work.BSW.BSWCompletionProp :=
  Work.BSW.S3.bswCompletionPropFromLeaves bsExistsX s31 h32 s34Arith case1 s35 h38

/-- **Bender §3, 3.1–3.8**: given the order `|G| = (2k ± 1)(k ± 1)(2k)` of
`Work.BSW.BSWOrderProp`, Bender's conclusion (1)–(4) holds with `q = 2k ± 1`. -/
theorem bswCompletionProp : Work.BSW.BSWCompletionProp :=
  bswCompletionProp_of_leaves s32 s38

end Work.BSW.S3
