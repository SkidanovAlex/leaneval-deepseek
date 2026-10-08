import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.Sec4Extra
import Submission.Work.BG.comb413
import Submission.Work.BG.s4L41
import Submission.Work.BG.lemma42
import Submission.Work.BG.congContra
import Submission.Work.BG.caseB

/-
Area BG, Theorem 4.3, case (b): `Work.GW2.C23.CaseBProp` (T43-B).

Bender–Glauberman 1981, Theorem 4.3, case (b), pp. 213–214 top: in the situation `|S| = 4`
(`D.n = 2`), if `ν ∈ 𝒮₄(C)` and *every* hat in the component of `ν` in the graph `Δ` is fixed by
`N_G(S)`, then the component of `ν` is a singleton — i.e. `¬ Adj C β₂ ν μ` for every `μ`.

The whole content of Theorem 4.3 is already reduced (in `Work.BG.caseB_of_leaves`, proved in
`Submission.Work.BG.caseB`) to the four §4 leaves

* `Work.GW2.C23.Comb413Prop`  — the pure combinatorial `{0,±1}`-matrix lemma of p. 213
  (`Work.BG.comb413`),
* `Work.GW2.C16.Lemma41Prop`  — Lemma 4.1 (i), (ii), (iv) (`Work.BG.s4L41`),
* `Work.GW2.C23.Lemma42Prop`  — Lemma 4.2, the odd-multiplicity criterion (`Work.BG.lemma42`),
* `Work.GW2.C23.CongContraProp` — CONG-CONTRA, pp. 213 bottom – 214 top (`Work.BG.congContra`),

all four of which are proved and axiom-clean in the workspace.  This file records the resulting
instance for case (b): the component of a `ν` all of whose hats are `N_G(S)`-fixed is a single
point.
-/

namespace Work.BG.thm43

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
/-- **Theorem 4.3, case (b)** (Bender–Glauberman 1981, p. 213 – 214 top).

If all hats in the `Δ`-component of `ν ∈ 𝒮₄(C)` are `N_G(S)`-fixed, then no `μ ∈ 𝒮₄(C)` is
adjacent to `ν`: the component of `ν` is a singleton.

The proof is the reduction to the four §4 leaves: `Comb413Prop` supplies the configuration
`j₁ j₂ j₃ | i₀, p₁ p₂ p₃`, `Lemma41Prop`/`Lemma42Prop` give the support and parity data of the
matrix of inner products, and `CongContraProp` refutes that configuration. -/
theorem caseB {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.CaseBProp D C :=
  Work.BG.caseB_of_leaves D C Work.BG.comb413 (Work.BG.s4L41 D C) (Work.BG.lemma42 D C)
    (Work.BG.congContra D C)

end Work.BG.thm43
