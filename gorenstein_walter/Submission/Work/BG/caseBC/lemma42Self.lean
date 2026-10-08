/-
Alias file: the case-B/C design name `Work.BG.caseBC.lemma42Self` for Bender--Glauberman's
Lemma 4.2 in the `|S| = 4` case, i.e. `Work.GW2.C23.Lemma42Prop`.

The statement is *literally* the one proved in `BG/lemma42.lean`:

  `Work.BG.lemma42 : Work.GW2.C23.Lemma42Prop D C`,  for `D : BGData G`, `C : Sec2Ctx G`.

That proof is complete and `#print axioms`-clean (it depends only on `propext`,
`Classical.choice`, `Quot.sound`); it rests on the four separately verified inputs
`l42S4grid` (`S ≅ V₄`, `S# = {t, t₁, t₂}`), `l42Ngrid` (the `N_G(S)`-orbit structure of `S`),
`l42BNinv` (`N_G(S)` normalises `B`, `C_G(S)` acts on `B` by inner automorphisms) and
`l42HatOdd` (the parity lemma on the odd-order group `B`), glued by the assembly
`l42_assembly` (Frobenius reciprocity for `K = S · B` + the value of `δ_ν` on `S · b`).

So this file is an alias in the style of `BG/s02_noFail.lean` / `BG/s02_noFailThm.lean`:
it re-exports the verified leaf under the name the case-B/C assembly asks for, rather than
duplicating the ~900 lines of character theory.  (Originally the case-B/C wave could not rely
on the design path `BG/lemma42`, which was still `sorry`-carrying; that is no longer the case:
`lake build Submission.Work.BG.lemma42` succeeds and the leaf is axiom-clean.)
-/
import Submission.Work.BG.lemma42

namespace Work.BG.caseBC

theorem lemma42Self {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.Lemma42Prop D C :=
  Work.BG.lemma42 D C

end Work.BG.caseBC
