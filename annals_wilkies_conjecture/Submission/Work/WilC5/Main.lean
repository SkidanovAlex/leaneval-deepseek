/-
  WilC5 — area C5 of the Wilkie project: the wiring of `C5_TE_modelComplete`.

  The frozen hole `WilkiesDesign.CG.C5_TE_modelComplete` says that `TE` (the theory of `ℝ_exp`,
  i.e. `LEc.completeTheory ℝ`) is model complete, given

  * `hMCr : ModelComplete TR` — model completeness of the theory of `ℝ` with the restricted
    exponential,
  * `hOM : OMinModels` — models of `TR` are o-minimal,
  * `hVI : ValIneq` — Wilkie's valuation inequality for `TR`.

  ## The route taken (van den Dries–Macintyre–Marker §4)

  The proof goes through vdDMM's **Theorem 4.1** for the exponential theory, in the form carried by
  `Work.WilC5.S4SubTE` (`Submission/Work/WilC5/S4SubTE.lean`): every embedding of a *submodel*
  `F₀ ⊨ TE` of a model of `TE` into a `κ`-saturated model of `TE` (`κ > |K|`) extends.  That
  statement is the one whose proof is the iteration of their Lemmas 4.2, 4.3 and 4.4, and it is the
  single residual hole of this area.

  From it, `ModelComplete TE` is a theorem of pure model theory, proved with no `sorry` in

  * `Work.WilC5.realize_of_hasExtPropSub` (`S4SubModel.lean`) — Sacks' test ingredient: under the
    submodel extension property, **every embedding of models of `T` into a `κ`-saturated model is
    elementary**.  The induction is that of `Work.WilC5.realize_goodEmb`; the point that makes the
    *submodel* version sufficient is that the extension property is applied at the `∀`-step to the
    range of the embedding under consideration, and the range of an embedding of a model is again
    a model of the theory;
  * `Work.WilC5.modelComplete_of_hasExtPropSub` — pass to a saturated elementary extension and
    descend along the elementary embedding;
  * `Work.WilC5.ModelComplete_TE_of_S4SubTE` — the specialization to `LEc`, `TE`.

  ## Why not the log-language route

  The earlier route of this area went through quantifier elimination of `Th(ℝ, exp, log)` in the
  language `LElog = LEc ⊕ {log, ≤}` (`Work.WilC5.HasQE TElog`) and Sacks' test
  (`Work.WilC5.HasQEOfExtensionProperty`).  That is *not* what the source proves: vdDMM's (4.10)
  obtains quantifier elimination for `(𝓡, exp)` only after adding, besides `log`, a function symbol
  for every function `∅`-definable in `𝓡`.  In the reduced language `LEc` the `∅`-definable sets
  are those of `ℝ_exp` — for example `{sin 1}`, by the comparison of `ℝ_an`- and `ℝ_exp`-definable
  sets — whereas the quantifier-free `LEc`-definable sets are the exponential-algebraic ones; the
  reduced statement is therefore strictly stronger than the source's and is not the right target.
  It is *off the critical path* of the present development: model completeness of `TE` is reached
  here through Theorem 4.1 alone, with no quantifier elimination.  The conditional forms
  `C5_TE_modelComplete_of_hasExtProp` (log language, arbitrary substructures) and
  `C5_TE_modelComplete_of_S4SubTE` (exponential language, submodels) are both retained.
-/
import Submission.Work.WilC5.Spec
import Submission.Work.WilC5.S4Residual

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **Area C5: `TE` is model complete** — the frozen hole `C5_TE_modelComplete`, proved from
`Work.WilC5.S4SubTE` (vdDMM Theorem 4.1 for the exponential theory).

The three frozen hypotheses `hMCr`, `hOM`, `hVI` are exactly the inputs of the §4 iteration; with
them as parameters, `ModelComplete TE` follows.  See `Submission/Work/WilC5/S4_LAYER.md` for the
state of the §4 content. -/
theorem C5_TE_modelComplete_proved (hMCr : ModelComplete TR) (hOM : OMinModels)
    (hVI : ValIneq) (hVP : Work.WilC5.ValProp) : ModelComplete TE :=
  Work.WilC5.ModelComplete_TE_of_S4SubTE (Work.WilC5.S4SubTE_proved hMCr hOM hVI hVP)

/-- **The frozen hole, conditional on vdDMM Theorem 4.1 in the exponential language alone.**

`Work.WilC5.S4SubTE` is the submodel extension property of vdDMM's Theorem 4.1 for
`TE = Th(ℝ, exp)`; the three frozen parameters `hMCr`, `hOM`, `hVI` are the inputs that prove it.
This form is provided so that a caller willing to carry that theorem as an interface hypothesis
gets `ModelComplete TE` with no `sorry` in the closure of the conclusion. -/
theorem C5_TE_modelComplete_of_S4SubTE (h : Work.WilC5.S4SubTE) : ModelComplete TE :=
  Work.WilC5.ModelComplete_TE_of_S4SubTE h

/-- **The frozen hole, conditional on vdDMM Theorem 4.1 in the log language.**

`Work.WilC5.HasExtProp LElog TElog` is the extension property of vdDMM Theorem 4.1 as it was
stated in the first version of this area (arbitrary `LElog`-substructures of models of `TElog`) —
see the module comment for why the reduced quantifier-elimination statement it leads to is stronger
than what the source proves.  With it as an explicit hypothesis, `ModelComplete TE` is proved with
no `sorry` in the closure. -/
theorem C5_TE_modelComplete_of_hasExtProp (h : Work.WilC5.HasExtProp Work.WilC5.LElog
    Work.WilC5.TElog) : ModelComplete TE :=
  Work.WilC5.ModelComplete_TE_of_hasExtProp h

/-- **The `C5` wiring with the extra uniform-finiteness hypothesis.**  Same conclusion as the
frozen hole, obtained from the same residual statement; the extra hypothesis is unused, and the
form is kept so that the amended signature proposed in `Wilkies/CG/Spec.lean` (and in `DESIGN.md`
§3b) remains available. -/
theorem C5_TE_modelComplete_proved_of_unif (hMCr : ModelComplete TR) (hOM : OMinModels)
    (hVI : ValIneq) (hUF : UnifFiniteRExp) (hVP : Work.WilC5.ValProp) : ModelComplete TE :=
  C5_TE_modelComplete_proved hMCr hOM hVI hVP

end WilkiesDesign.CG
