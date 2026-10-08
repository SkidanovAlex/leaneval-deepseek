/-
Area BG (Bender–Glauberman 1981): the last step of the final assembly — **Theorem C,
unconditional**.  Everything up to and including Theorem B (and all the leaf-discharge
theorems) is in `Submission.Work.BG.Assembly`; this module only adds C3-4 (`BG/c3Degree`) and
then `thmC_of_leaves`.

(`BG/Assembly.lean` has no `c3Degree` import on purpose: `c3Degree` imports `BG/kNeOneAlt`,
which needs Theorem B, so `c3Degree` must sit strictly above the Theorem A/B assembly.)
-/
import Mathlib
import Submission.Work.BG.Assembly
import Submission.Work.BG.c3Degree

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-- **C3-4 is CLOSED** (`BG/c3Degree`, via `C24.lemma36_thmC` + `BG/kInvNormal` + `BG/lemma36`;
`#print axioms` clean). -/
theorem c3DegAll : C3DegAll :=
  fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
      (K1 K2 : Subgroup G) =>
    c3Degree D C K1 K2

/-- **Theorem C**, with every leaf discharged except `C3-4` (kept as a parameter for reference). -/
theorem bgThmC_of_c3deg (hc3deg : C3DegAll) : BGThmCProp :=
  bgThmC_of coherenceAll decompAll s4All c3IdAll c3NtAll hc3deg c4IdAll c4ValAll c4DegAll

/-- **Theorem C, unconditional.** -/
theorem bgThmC : BGThmCProp := bgThmC_of_c3deg c3DegAll

end Work.BG
