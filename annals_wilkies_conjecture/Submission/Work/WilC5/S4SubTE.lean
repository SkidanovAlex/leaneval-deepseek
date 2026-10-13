/-
  WilC5 — **the residual content of area C5**, in the form in which van den Dries–Macintyre–Marker
  prove it, together with the (proved) assembly into the frozen conclusion `ModelComplete TE`.

  ## Why this file replaces the `TElog` / `DMM41` route

  The frozen hole of area C5 is `WilkiesDesign.CG.C5_TE_modelComplete`, i.e. (given the three
  inputs `hMCr`, `hOM`, `hVI` of the surrounding project) model completeness of
  `TE = Th(ℝ, exp)`.  The route followed until now went through

  `HasQE TElog`  (quantifier elimination of `Th(ℝ, exp, log)` in the language `LElog = LEc ⊕ {log, ≤}`)

  via Sacks' quantifier-elimination test.  That formulation is **not** the one the source supports:
  vdDMM's (4.10) proves quantifier elimination for `(𝓡, exp)` only in the language of `𝓡` together
  with `log` *and a function symbol for every function that is `∅`-definable in `𝓡`*.  In the
  reduced language `LEc = ring ⊕ exp ⊕ ℝ` the definable sets are those of `ℝ_exp` — for instance
  the singleton `{sin 1}`, by the comparison `ℝ_an ⊆ ℝ_exp`-definable — while the sets
  quantifier-free definable in `LEc` are the exponential-algebraic ones; quantifier elimination in
  `LEc` is therefore not the statement of the source, and the test cannot be expected to apply.

  What the source does prove, and what is formalized here, is their **Theorem 4.1**:

  > Suppose `K ⊨ T_an(exp)`, `F₀ ⊆ K` is log-closed and `F₀ ⊨ T_an`.  If `L ⊨ T_an(exp)` is
  > `|K|⁺`-saturated and `σ₀ : F₀ → L` is a log-preserving embedding, then `σ₀` extends to a
  > log-preserving embedding of `K` into `L`.

  In the language of this development: `HasExtPropSub LEc TE` (`S4SubTE` below) — the *submodel*
  extension property.  It differs from the previous residual `DMM41` in two ways, both essential:

  * the domain is required to be a **model of the theory** (`F₀ ⊨ TE`), not an arbitrary
    substructure — the requirement "every substructure of a model of `TElog` is a model of `TElog`"
    (vdDMM's Corollary 4.6 in the language `L_an(exp,log)`) is a consequence of the *richness* of
    `L_an` and fails in the reduced language `LElog`; and
  * nothing about quantifier elimination in `LEc` or `LElog` is needed, so the doubtful
    `LElog`-only quantifier elimination is off the critical path.

  `S4SubTE` is *provably equivalent* to the frozen conclusion: `ModelComplete_TE_of_S4SubTE` below
  is the direction proved in `S4SubModel.lean`, and `S4SubTE_of_ModelComplete_TE` is
  `Work.WilC5.hasExtProp_of_modelComplete`.  Its proof in the source is the iteration of Lemmas
  4.2, 4.3 and 4.4 over a well-ordering of `K`, maintaining a `T_an`-submodel `F` that is
  log-closed and a log-preserving embedding `F → L`; the §4 lemmas are the content that remains.

  ## State of the pieces (see `S4_LAYER.md`)

  Proved and importable: the `LRc`-half of Lemma 4.2 (`dmm42_cut_extend`, `cut_determines_type_F`,
  `realizes_cut`, `decomposition_of_same_value`), the log algebra (`logFun_one_add_rexp`,
  `logFun_eq_of_rexp_eq`, `logFun_mul`, `expE_lt_iff_logFun_lt`), the value input of Lemma 4.4
  (`valIneq_span`) and the saturation machinery (`IsSaturated`, `ExistsSaturated`,
  `extendable_of_elementary`).  The outstanding content is the one-element extension step of
  Lemmas 4.2–4.4 in the `exp`/`log` language, i.e. exactly this file's `S4SubTE_proved`.
-/
import Submission.Work.WilC5.S4SubModel
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.HasQEOfExtensionProperty
import Submission.Work.WilC5.hasExtProp_of_modelComplete

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The residual content of area C5**: van den Dries–Macintyre–Marker, *Theorem 4.1*, for the
theory `TE = Th(ℝ, exp)` of the real exponential field — the extension property for *submodels*.

Every embedding `σ : F₀ → L` of a substructure `F₀` of a model `K ⊨ TE` which is itself a model of
`TE` into a `κ`-saturated model `L ⊨ TE` with `κ > |K|` extends to an embedding of `K` into `L`.

This is precisely the statement whose proof is "iterate Lemmas 4.2, 4.3 and 4.4" (vdDMM, after
Lemma 4.4), with `hMCr` (model completeness of `TR`) supplying the elementarity of each partial
map, `hOM` (o-minimality of models of `TR`) the "the cut determines the type over `dcl`-closed
sets" step, and `hVI` (Wilkie's valuation inequality, through `Work.WilC5.valIneq_span`) the
value-group bookkeeping. -/
def S4SubTE : Prop :=
  Work.WilC5.HasExtPropSub WilkiesDesign.CG.LEc WilkiesDesign.CG.TE

/-- **Model completeness of `TE` from the submodel extension property** (proved in
`S4SubModel.lean`): the saturated-extension part of the argument, with no §4 content. -/
theorem ModelComplete_TE_of_S4SubTE (h : S4SubTE) :
    WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TE :=
  Work.WilC5.modelComplete_of_hasExtPropSub h

/-- **The converse** (proved): model completeness gives the submodel extension property, via
`Work.WilC5.hasExtProp_of_modelComplete`.  Together with the previous theorem this shows that
`S4SubTE` is exactly the residual content of the frozen hole `C5_TE_modelComplete`. -/
theorem S4SubTE_of_ModelComplete_TE (h : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TE) :
    S4SubTE :=
  Work.WilC5.hasExtProp_of_modelComplete h

/- **Where `S4SubTE` is proved from**: `S4Residual.lean` reduces it to the one-element step
`Work.WilC5.S4OnePoint` (`Work.WilC5.S4SubTE_of_S4OnePoint`), and defines
`Work.WilC5.S4OnePoint_proved` (the residual hole) and `Work.WilC5.S4SubTE_proved`.

In the meantime, all the pieces of the iteration of vdDMM's Lemmas 4.2, 4.3 and 4.4 are listed in
`S4_LAYER.md` §3–§5: the cut/type extension of Lemma 4.2 in the `rexp` language
(`Work.WilC5.dmm42_cut_extend`), the residue-field decomposition
(`Work.WilC5.decomposition_of_same_value`), the log algebra (`Work.WilC5.logFun_one_add_rexp`,
`Work.WilC5.logFun_eq_of_rexp_eq`), the value input of Lemma 4.4 (`Work.WilC5.valIneq_span`) and
the chain/initial-domain/upgrade lemmas of `S4_LAYER.md` §5. -/

end Work.WilC5
