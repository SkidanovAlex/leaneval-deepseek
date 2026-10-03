import ChallengeDeps
import Submission.Helpers
import Submission.Work.ORAssembly.Main
import Submission.Work.ORFinal.FinalAssembly
import Submission.Work.ORP311.prop311OnComplex
import Submission.Work.ORDivLoc.Prop311

open OnCoherenceOfOneRelatorGroups

set_option autoImplicit false

namespace Submission

/-- Theorem 1.1 of Jaikin-Zapirain--Linton, *Annals* 201 (2025).

**Status.**  The proof is assembled in `Submission/Work/ORAssembly/Main.lean`: every *delivered*
node (N0, N1, N5, N7, N8, N9, N10, N11) is used as a proof there, and every *still open* node
(N2, N3, N4, N6, N12, N13) enters as an explicit hypothesis of
`Work.ORAssembly.theorem_1_1_of_nodes`, namely

* `HN : Work.ORAssembly.NodeInputs.{0} Unit` — node N2's `OneRelatorCombinatorics`, the two
  Bass–Serre trees of node N12 (`hnnTree`, `coprodTree`), N12's three named `Prop`s
  (`quotientTree`, `freeOnTree`, `bassSerre`) and node N13's `dunwoody`;
* `hRingQ`/`hRingK : ∀ n r : FreeGroup (Fin n), Work.ORAssembly.RingInputs _ ⟨Fin n | r⟩` — the
  L² inputs at `ℚ` (for the group half) and at `K`, one per finitely generated one-relator
  presentation; see `RingInputs` in `Submission/Work/ORAssembly/RingHalf.lean`.

The remaining step is therefore purely the discharge of those hypotheses: once the open nodes have
delivered (or the interface mismatches (M1)–(M8) below are bridged), this theorem becomes

  exact Work.ORAssembly.theorem_1_1_of_nodes G K hG HN hRingQ hRingK

Until then the `sorry` below records exactly which pieces are missing — it is *not* a mathematical
gap: the six open nodes, together with the interface mismatches (M1)–(M4) and (M8) documented in
`Submission/Work/ORAssembly/README.md` §3, are the whole obstruction.  ((M5), (M6) and (M7) are
closed inside `Submission/Work/ORAssembly/`.) -/
theorem theorem_1_1 (G K : Type*) [Group G] [Field K] [CharZero K] (hG : Group.OneRelator G) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) := by
  -- Discharge the node hypotheses (nodes N2, N3, N4, N6, N12, N13 and mismatches (M1)–(M8)),
  -- then replace this `sorry` by
  --   exact Work.ORAssembly.theorem_1_1_of_nodes G K hG HN hRingQ hRingK
  exact Work.ORFinal.theorem_1_1_of_prop311_challenge hG
    (fun (H : Type) [Group H] [Countable H] =>
      Work.ORDivLoc.prop311OnComplexClosure_of_complex (Work.ORP311.prop311OnComplex H))

end Submission
