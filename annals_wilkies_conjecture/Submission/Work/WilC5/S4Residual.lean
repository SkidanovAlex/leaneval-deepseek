/-
  WilC5 — **the residual of area C5**, now decomposed into vdDMM's one-element step.

  The area's residual used to be stated directly as vdDMM Theorem 4.1 for `TE` (`Work.WilC5.S4SubTE`,
  `S4SubTE.lean`).  It is now reduced to the *one-element step* of §4:

  * `Work.WilC5.S4OnePoint` (`S4OnePoint.lean`) — in the situation of the iteration
    (`K, L ⊨ TE`, `L` `κ`-saturated with `κ > |K|`, `A ≤ K` an invariant domain, `σ : A → L` a
    log-preserving `LRc`-embedding), extend `σ` past any prescribed `x ∈ K`.  This is the common
    conclusion of vdDMM's Lemmas 4.2, 4.3 and 4.4;
  * `Work.WilC5.S4SubTE_of_S4OnePoint` (`S4SubTE_of_S4OnePoint.lean`) — **the Zorn assembly**,
    proved: `hMCr`, `hOM` and the one-element step give `S4SubTE`.  The iteration is seeded at the
    given submodel `F₀ ⊨ TE` (`Work.WilC5.dcl_substructure_subset`,
    `Work.WilC5.logFun_mem_of_substructure`), chain unions are handled by
    `Work.WilC5.dcl_iUnion_chain` (plus the union of a chain of substructures), and at the top the
    log-preserving `LRc`-embedding of models of `TE` is upgraded to an `LEc`-embedding by
    `Work.WilC5.expE_of_logFun_preserving`;
  * `Work.WilC5.S4OnePoint_proved` — **the single `sorry` of the directory**;
  * `Work.WilC5.S4SubTE_proved` — `S4SubTE` from it, hence the frozen
    `WilkiesDesign.CG.C5_TE_modelComplete_proved`, with `sorryAx` appearing only through
    `S4OnePoint_proved`.

  What remains is therefore a single element-at-a-time statement, whose three cases are vdDMM
  Lemmas 4.2 (no new value), 4.3 (adjunction of an exponential) and 4.4 (the general case, with the
  sequence `x_{n+1} = εₙ(log xₙ − βₙ)` and Claims 1–5).  The pieces of those lemmas that are
  already formalized are listed in `S4_LAYER.md` §3–§5.
-/
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.S4OnePointCases
import Submission.Work.WilC5.S4OnePoint_exp_proved
import Submission.Work.WilC5.S4OnePoint_general_proved
import Submission.Work.WilC5.ValProp
import Submission.Work.WilC5.S4SubTE
import Submission.Work.WilC5.S4SubTE_of_S4OnePoint

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/- **The one-element step of vdDMM §4** is now proved from its two cases: the `exp` case (Lemma
4.3, `Work.WilC5.S4OnePoint_exp_proved`) needs none of the extra hypotheses, and the general case
(Lemmas 4.2 and 4.4, `Work.WilC5.S4OnePoint_general_proved`) is proved **under the lead-sanctioned
extra hypothesis** `hVP : Work.WilC5.ValProp` — vdDMM's valuation property (3.7), true for `TR` but
not derivable from `hMCr`, `hOM`, `hVI`, discharged by a separate lead node. -/

/-- **The one-element step of §4, under `hVP`** — proved, no `sorry`: the `exp` case is
`Work.WilC5.S4OnePoint_exp_proved` (Lemma 4.3) and the general case (Lemmas 4.2 and 4.4) is
`Work.WilC5.S4OnePoint_general_proved` under the lead-sanctioned `hVP`. -/
theorem S4OnePoint_proved (hMCr : ModelComplete TR) (hOM : OMinModels)
    (hVI : ValIneq) (hVP : ValProp) : S4OnePoint :=
  S4OnePoint_of_cases (S4OnePoint_exp_proved hMCr hOM hVI)
    (S4OnePoint_general_proved hMCr hOM hVI hVP)

/-- **vdDMM Theorem 4.1 for `TE`, under `hVP`**: the proved assembly
(`Work.WilC5.S4SubTE_of_S4OnePoint`) applied to `Work.WilC5.S4OnePoint_proved`.  No `sorry`. -/
theorem S4SubTE_proved (hMCr : ModelComplete TR) (hOM : OMinModels)
    (hVI : ValIneq) (hVP : ValProp) : S4SubTE :=
  S4SubTE_of_S4OnePoint hMCr hOM (S4OnePoint_proved hMCr hOM hVI hVP)

/- The `hVP`-free form of the frozen statement is **out of scope for area C5** by the lead's ruling
(`ValProp.lean`): vdDMM's valuation property (3.7) is true for `TR` but not derivable from `hMCr`,
`hOM`, `hVI`, and it is discharged by a separate lead node.  Nothing here is left as a `sorry`;
every theorem of this area closes with `[propext, Classical.choice, Quot.sound]` once `hVP` is
supplied. -/

end Work.WilC5
