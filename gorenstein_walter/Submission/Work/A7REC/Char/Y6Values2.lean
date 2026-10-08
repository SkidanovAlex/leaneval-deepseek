/-
Area `A7REC`: **the corrected C1e leaf, proved** (`Work.A7REC.Char.a7Y6Values2`).

`A7Y6Values2Prop` (see `Char/Y6Defs.lean`) is the contracted C1e leaf `A7Y6ValuesProp` with the
missing one-class hypothesis `OneInvClass G` added.  Here it is assembled from the six proved
pieces:

* `Char/Y6SigmaLin.lean`        `Y6SigmaLin`        — the linear algebra of the value at `σ`;
* `Char/Y6ZetaSeven.lean`       `Y6ZetaSeven`       — the relation among the `7`-th roots of unity;
* `Char/Y6PowerThree.lean`      `Y6PowerThree`      — the cyclotomic power map `g ↦ g³`;
* `Char/Y6SevenValue.lean`      `Y6SevenValue`      — the value at order-`7` elements ∈ {-1, 6};
* `Char/Y6TraceFinrank.lean`    `Y6TraceFinrank`    — trace `= finrank` at order `7` forces `1`;
* `Char/Y6RepNeOne.lean`        `Y6RepNeOne`        — faithfulness in a simple group;

with the local input `Basic.exists_involution_inverting` (an involution inverting `σ`) supplied
by the `A₇` configuration, and the assembly `a7Y6Values2_of_pieces` of `Char/Y6Main.lean`.

The older file `Char/a7Y6Values.lean` (whose proof went through the *target*
`Char/indexSevenOfSimple2520.lean`, hence circular) is superseded by this one and is not an input
of anything the area delivers.
-/
import Submission.Work.A7REC.Char.Y6Main
import Submission.Work.A7REC.Char.Y6SigmaLin
import Submission.Work.A7REC.Char.Y6ZetaSeven
import Submission.Work.A7REC.Char.Y6PowerThree
import Submission.Work.A7REC.Char.Y6SevenValue
import Submission.Work.A7REC.Char.Y6TraceFinrank
import Submission.Work.A7REC.Char.Y6RepNeOne

namespace Work.A7REC.Char

/-- **C1e′**: the values of the degree-`6` character, proved from the six pieces. -/
theorem a7Y6Values2 : Work.A7REC.A7Y6Values2Prop :=
  a7Y6Values2_of_pieces Y6SigmaLin Y6ZetaSeven Y6PowerThree Y6SevenValue Y6TraceFinrank
    Y6RepNeOne

end Work.A7REC.Char
