/-
Area `A7REC`: **the final assembly** — `A7Char6Prop` (C1) and `A7Rec2Prop`, from the area's leaves.

Everything here is wiring: each ingredient is proved elsewhere in the area, and none of it imports
`Char/indexSevenOfSimple2520.lean` (the area's *target*), so the chain below is **not circular**.

* C1: `Char.a7Char6_two` (the assembly of `Char/Char6Two.lean`) applied to the proved
  `Char.a7TableLemma` (the finite table lemma), `Char.a7C1b` (the table data of `G`),
  `Char.a7Bridge` (the p11 bridge), `c13_counts` (the involution counts `i(π) = 4`, `i(z) = 8`,
  `i(zσ) = 6`) and `Char.a7Y6Values2` (the corrected C1e leaf `A7Y6Values2Prop`;
  see `NOTES_A7Y6Values_correction.md`).
* C2+C3: `a7IndexSevenFromChar1` (`Char/IndexSeven1.lean`), bridged to the pass-4 statement by
  `A7IndexSevenFromCharProp_of_char1`.
* `hone` (one class of involutions, from area FUS's `InvolutionFusionProp`) is the caller's
  hypothesis; see `NOTES_LEAVES.md` §B2.5 for why it is consistent with the `A₇` model.

The superseded, circular route of `Char/a7Char6_of_table.lean` (which used the too-weak
`A7Y6ValuesProp`, proved only through the target) is kept on disk as a record but is not imported
here.
-/
import Submission.Work.A7REC.Char.a7C1b
import Submission.Work.A7REC.Char.a7TableLemma
import Submission.Work.A7REC.Char.a7Bridge
import Submission.Work.A7REC.Char.InvCounts2
import Submission.Work.A7REC.Char.IndexSeven1
import Submission.Work.A7REC.Char.Char6Two
import Submission.Work.A7REC.Char.Y6Values2

namespace Work.A7REC

/-- **C1 assembled**: `A7Char6Prop` from the proved C1 leaves and the one-class input. -/
theorem a7Char6
    (hone : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      A7RecHyps G S z U V → OneInvClass G) : A7Char6Prop :=
  Char.a7Char6_two hone Char.a7Y6Values2

/-- **The amended contract, assembled.**  `A7Rec2Prop` follows from the leaves of this area and the
one-class input: C1 (`a7Char6`) supplies the degree-`6` representation, C2+C3
(`a7IndexSevenFromChar1`) supplies a subgroup of index `7`, and the coset action identifies `G`
with `A₇`. -/
theorem a7Rec2Prop_of_leaves
    (hone : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      A7RecHyps G S z U V → OneInvClass G) : A7Rec2Prop :=
  a7Rec2Prop_of_char6_and_indexSeven (a7Char6 hone)
    (A7IndexSevenFromCharProp_of_char1 a7IndexSevenFromChar1 hone)

end Work.A7REC
