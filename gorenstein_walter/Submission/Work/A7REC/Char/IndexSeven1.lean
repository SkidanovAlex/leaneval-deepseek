/-
Area `A7REC`: **C2 + C3 closed.**

All eight leaves of the pass-8 design (`_design_gw/Core8.lean` §1) are proved, so the assembly
`Work.A7REC.a7IndexSevenFromChar1_of_leaves` (`Excl.lean`) yields
`A7IndexSevenFromChar1Prop` — and hence, with the one-class input, the pass-4 statement
`A7IndexSevenFromCharProp`:

* `a7Config` (C2: the Suzuki configuration `(S', τ')` exists),
* `a7FixedVector` (C3a: a non-zero vector fixed by `U` and `S'`),
* `a7Stabilizer` (C3b: the stabilizer contains `U, S'` and `7 ∣ [G : H]`),
* `a7Excl24`, `a7Excl72`, `a7Excl120` (the three exclusions of the possible orders of `H`),
* `a7NoNine` (no order-`9` subgroup has all nonidentity elements conjugate into `U`),
* `a7InvCent` (involution centralizers have order `24` with a unique order-`3` subgroup).
-/
import Submission.Work.A7REC.Char.a7Config
import Submission.Work.A7REC.Char.a7FixedVector
import Submission.Work.A7REC.Char.a7Stabilizer
import Submission.Work.A7REC.Char.a7Excl24
import Submission.Work.A7REC.Char.a7Excl72
import Submission.Work.A7REC.Char.a7Excl120
import Submission.Work.A7REC.Char.a7NoNine
import Submission.Work.A7REC.Char.a7InvCent

namespace Work.A7REC

/-- **C2 + C3**: `A7IndexSevenFromChar1Prop` from the eight pass-8 leaves. -/
theorem a7IndexSevenFromChar1 : A7IndexSevenFromChar1Prop :=
  a7IndexSevenFromChar1_of_leaves Char.a7Config Char.a7FixedVector Char.a7Stabilizer
    Char.a7Excl24 Char.a7NoNine Char.a7Excl72 Char.a7Excl120 Char.a7InvCent

end Work.A7REC
