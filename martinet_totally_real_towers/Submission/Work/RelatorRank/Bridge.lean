import Submission.Work.RelatorRank.Transfer

/-!
# `Work.RelatorRank` -- the bridge: from a relation bound to the presentation-independent bound

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Bridge`.

The mathematical content of this module is the *diagnosis* of the bridge requested in
`Submission/PLAN.md` §§20--22 and in the workspace's `Submission/NumberField/TamePresentationDatum.lean`:

> an arithmetic theorem produces a presentation of `Γ` on **some** dense generating `d`-family
> (`HasProP2Presentation Γ d r`, or in cohomological form `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ r`), while the
> intended consumer wants the *presentation-independent* form `RelatorHalfOf Γ d r` -- a relator
> set of size `≤ r` for **every** dense generating `d`-family.

The two are equivalent for a finitely generated pro-`p` group `Γ` with `d = GeneratorRank Γ`,
because the minimal number of relations is then the *presentation invariant*
`r(Γ) = dim_{𝔽₂} H²(Γ, 𝔽₂)`.  This module:

* `relationRankInvariant_iff` : the bridge hypothesis is equivalent to the conjunction of its two
  halves -- trivially, but it fixes the interface;
* `relatorHalfOf_of_hasProP2Presentation_of_aut_transitive` : **the automorphism argument**, in the
  exact form in which it is valid: a presentation datum plus the statement that every dense
  generating `d`-family is the image of the presented one under a continuous automorphism of `Γ`
  gives `RelatorHalfOf`.  The extra hypothesis is *false* in general -- see the `README.md` for the
  counterexample `Γ = ℤ/4 × ℤ/2`, where `Aut Γ` has only `8` elements while there are `24` ordered
  generating pairs -- so this does **not** prove the bridge;
* `relator_half_of_relation_rank_le_six` : the requested statement, carrying the missing invariance
  `RelationRankInvariant Γ 5 6` as an explicit hypothesis (with the workspace's minimality
  hypothesis `¬ HasDenseGeneratingFamily Γ 4`, i.e. `Submission.NumberField.GeneratorMinimal`);
* the general-`d` and abstract-group versions of the same;
* `noSmallerGeneratingFamily_five_iff` : the minimality hypothesis in the workspace's exact shape.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## The minimality hypothesis in the workspace's shape -/

/-- **`NoSmallerGeneratingFamily Γ 5` is exactly the workspace's `GeneratorMinimal`**: the absence
of a dense generating family of four elements.  (A dense generating family of `d' < 5` elements pads
to one of four elements by `HasDenseGeneratingFamily.mono`.) -/
theorem noSmallerGeneratingFamily_five_iff :
    NoSmallerGeneratingFamily Γ 5 ↔ ¬ HasDenseGeneratingFamily Γ 4 := by
  constructor
  · intro h h4
    exact h 4 (by norm_num) h4
  · intro h d hd hgen
    exact h (hgen.mono (by omega))

/-- General form: `NoSmallerGeneratingFamily Γ d` is the absence of a dense generating family of
`d - 1` elements, given that a dense generating family of size `d` exists. -/
theorem noSmallerGeneratingFamily_iff_not_hasDenseGeneratingFamily_pred {d : ℕ} (hd : 0 < d)
    (hex : HasDenseGeneratingFamily Γ d) :
    NoSmallerGeneratingFamily Γ d ↔ ¬ HasDenseGeneratingFamily Γ (d - 1) := by
  constructor
  · intro h
    exact h (d - 1) (by omega)
  · intro h d' hd' hgen
    exact h (hgen.mono (by omega))

/-! ## The bridge hypothesis -/

/-- The bridge hypothesis is the implication from the `∃`-form to the presentation-independent
form; stated here as an `iff` to fix the interface. -/
theorem relationRankInvariant_iff {d r : ℕ} :
    RelationRankInvariant Γ d r ↔ (HasProP2Presentation Γ d r → RelatorHalfOf Γ d r) := Iff.rfl

/-- `RelatorHalfOf Γ d r` is monotone in `r`. -/
theorem RelatorHalfOf.mono {d r r' : ℕ} (h : RelatorHalfOf Γ d r) (hr : r ≤ r') :
    RelatorHalfOf Γ d r' := by
  intro gen hgen
  obtain ⟨rel, hcard, hker⟩ := h gen hgen
  exact ⟨rel, le_trans hcard hr, hker⟩

/-- `RelatorHalfOf Γ d r` gives the `∃`-form for every dense generating family, in particular for
one. -/
theorem HasProP2Presentation.of_relatorHalfOf {d r : ℕ} (h : RelatorHalfOf Γ d r)
    (hex : HasDenseGeneratingFamily Γ d) : HasProP2Presentation Γ d r := by
  obtain ⟨gen, hgen⟩ := hex
  obtain ⟨rel, hcard, hker⟩ := h gen hgen
  exact ⟨⟨gen, rel, hgen, hcard, hker⟩⟩

/-- **The bridge for the canonical generator number.**  For a dense generating family of size
`GeneratorRank Γ` there is, by definition of the rank, a presentation on `GeneratorRank Γ`
generators; with the invariance hypothesis the bound holds for every dense generating family of that
size. -/
theorem relatorHalfOf_generatorRank_of_relatorRankLe {r : ℕ} (h : RelatorRankLe Γ r)
    (hinv : RelationRankInvariant Γ (GeneratorRank Γ) r) : RelatorHalfOf Γ (GeneratorRank Γ) r :=
  hinv h

/-! ## The automorphism argument, in the form in which it is correct -/

/-- **The automorphism argument.**  If `P` is a presentation of `Γ` on `d` generators with at most
`r` relators, and every dense generating `d`-family of `Γ` is the image of `P.gen` under a
*continuous automorphism* of `Γ`, then every dense generating `d`-family admits at most `r`
relators.

The second hypothesis ("two minimal generating tuples are related by an automorphism of `Γ`",
`Submission/PLAN.md` §21) is **false** -- see `README.md` -- so this lemma isolates exactly the gap
between what is proved and what the bridge needs. -/
theorem relatorHalfOf_of_hasProP2Presentation_of_aut_transitive {d r : ℕ}
    (P : ProP2PresentationData Γ d r)
    (htrans : ∀ gen : Fin d → Γ, DenseGenerating gen → ∃ e : Γ ≃ₜ* Γ, ∀ i, gen i = e (P.gen i)) :
    RelatorHalfOf Γ d r :=
  relatorHalfOf_of_aut_transitive P.gen P.dense P.rel P.card_le P.ker_eq htrans

/-- The `∃`-form plus the automorphism-transitivity hypothesis implies the presentation-independent
bound. -/
theorem relatorHalfOf_of_relationRankInvariant_of_aut_transitive {d r : ℕ}
    (h : HasProP2Presentation Γ d r)
    (htrans : ∀ P : ProP2PresentationData Γ d r, ∀ gen : Fin d → Γ, DenseGenerating gen →
      ∃ e : Γ ≃ₜ* Γ, ∀ i, gen i = e (P.gen i)) :
    RelatorHalfOf Γ d r := by
  obtain ⟨P⟩ := h
  exact relatorHalfOf_of_hasProP2Presentation_of_aut_transitive P (htrans P)

/-! ## The requested bridge, with the missing invariance made explicit -/

/-- **THE BRIDGE (workspace shape, with the missing group-theoretic input explicit).**

Let `Γ` be a topological group (in the applications `Γ = K ≃ₐ[ℚ] K`, a finitely generated pro-`2`
group with the Krull topology), suppose

* `¬ HasDenseGeneratingFamily Γ 4` -- the minimality of the five-element generating families
  (`Submission.NumberField.GeneratorMinimal`);
* `HasProP2Presentation Γ 5 6` -- the arithmetic `∃`-form: five generators, six relators;
* `RelationRankInvariant Γ 5 6` -- **the missing input**: the number of relations of a presentation
  on five generators does not depend on the chosen dense generating family;

then *every* dense generating five-element family admits at most six relators -- the form
`Submission.NumberField.RelatorHalf` consumes.

The third hypothesis is not a technicality: it is the classical theorem
`r(Γ) = dim_{𝔽₂} H²(Γ, 𝔽₂)` for finitely generated pro-`2` groups, which is *not* formalised (it
requires the continuous cohomology of profinite groups and the five-term exact sequence).  What *is*
proved here is that this hypothesis is exactly what the bridge needs
(`relationRankInvariant_iff`, `relatorHalfOf_of_aut_transitive`), together with the automorphism
invariance of the relation kernel (`ker_lift_comp_continuousMulEquiv`). -/
theorem relator_half_of_relation_rank_le_six (hmin : ¬ HasDenseGeneratingFamily Γ 4)
    (hinv : RelationRankInvariant Γ 5 6) (h : HasProP2Presentation Γ 5 6) :
    ∀ gen : Fin 5 → Γ, DenseGenerating gen →
      ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
        MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) := by
  -- `hmin` makes the given presentation *minimal*, i.e. identifies it with the canonical
  -- relation-rank bound `RelatorRankLe Γ 6`
  have hex : HasDenseGeneratingFamily Γ 5 := h.to_hasDenseGeneratingFamily
  have hmin' : NoSmallerGeneratingFamily Γ 5 := noSmallerGeneratingFamily_five_iff.mpr hmin
  have hcanon : RelatorRankLe Γ 6 :=
    (relatorRankLeSix_iff_hasProP2Presentation hmin' hex).mpr h
  exact hinv ((relatorRankLeSix_iff_hasProP2Presentation hmin' hex).mp hcanon)

/-- **The bridge in the general-`d`, general-`r` form.** -/
theorem relator_half_of_relation_rank_le {d r : ℕ} (hmin : NoSmallerGeneratingFamily Γ d)
    (hinv : RelationRankInvariant Γ d r) (h : HasProP2Presentation Γ d r) :
    RelatorHalfOf Γ d r := by
  have hex : HasDenseGeneratingFamily Γ d := h.to_hasDenseGeneratingFamily
  have hcanon : RelatorRankLe Γ r := (relatorRankLe_iff_hasProP2Presentation hmin hex).mpr h
  exact hinv ((relatorRankLe_iff_hasProP2Presentation hmin hex).mp hcanon)

/-- **The bridge from the canonical relation-rank bound alone** (i.e. when the arithmetic input is
already stated on `GeneratorRank Γ` generators, as it is in the cohomological form
`dim_{𝔽₂} H²(Γ,𝔽₂) ≤ r`). -/
theorem relatorHalfOf_of_relatorRankLe {r : ℕ} (h : RelatorRankLe Γ r)
    (hinv : RelationRankInvariant Γ (GeneratorRank Γ) r) : RelatorHalfOf Γ (GeneratorRank Γ) r :=
  hinv h

/-! ## The abstract core -/

section Abstract

variable {G : Type*} [Group G]

/-- The abstract analogue of the bridge: with the invariance of the relation count on `d`-generator
presentations, the `∃`-form gives the presentation-independent form for every generating family. -/
theorem abstractRelatorHalfOf_of_abstractRelationRankInvariant {d r : ℕ}
    (hinv : AbstractRelationRankInvariant G d r) (h : HasAbstractPresentation G d r) :
    AbstractRelatorHalfOf G d r :=
  hinv h

/-- **The abstract core of the bridge**, in the workspace's shape with `d = 5`, `r = 6`. -/
theorem abstractRelatorHalfOf_of_abstractRelationRankInvariant_six
    (hinv : AbstractRelationRankInvariant G 5 6) (h : HasAbstractPresentation G 5 6) :
    ∀ gen : Fin 5 → G, Generating gen →
      ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
        MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) :=
  hinv h

/-- The abstract `∃`-form is implied by the abstract presentation-independent form. -/
theorem HasAbstractPresentation.of_abstractRelatorHalfOf {d r : ℕ}
    (h : AbstractRelatorHalfOf G d r) (hex : HasGeneratingFamily G d) :
    HasAbstractPresentation G d r := by
  obtain ⟨gen, hgen⟩ := hex
  obtain ⟨rel, hcard, hker⟩ := h gen hgen
  exact ⟨⟨gen, rel, hgen, hcard, hker⟩⟩

end Abstract

end Work.RelatorRank
