import Submission.Work.RelatorRank.Cohomology
import Submission.Work.ConCohomology.Defs

/-!
# `Work.RelatorRank` -- the continuous cohomology `H²(Γ, 𝔽₂)` and Gaschütz's dictionary

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.CohomologyH2`.

`Cohomology.lean` states the cohomological relation bound `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ r` in the
*presentation* form `H2DimLe`, because at the time the chapter was written the workspace had no
continuous cohomology of profinite groups.  That substrate now exists: the parallel chapter
`Submission.Work.ConCohomology` builds the continuous cohomology of a topological group with
*discrete* coefficients, `Work.ConCohomology.H2 Γ M`, as the quotient of the locally constant
`2`-cocycles by the `2`-coboundaries.  This module

* instantiates it at the coefficient module `𝔽₂ = ℤ/2` with the **trivial** action, giving a
  genuine cohomology group `contH2 Γ = H²(Γ, 𝔽₂)` for a topological group `Γ`
  (`f2TrivialAction`, `f2Discrete`, `contH2`);
* defines the honest cohomological bound
  `ContH2DimLe Γ r` : `𝔽₂`-dimension of `H²(Γ, 𝔽₂) ≤ r`, phrased without a dimension function as
  `∃ k ≤ r, Nat.card (contH2 Γ) = 2 ^ k` (so the statement is *false* when `H²` is infinite, as it
  should be);
* states **Gaschütz's dictionary** `GaschutzDictionary Γ : Prop`, namely
  `∀ r, ContH2DimLe Γ r ↔ RelatorRankLe Γ r` -- the classical identification "minimal number of
  relators `=` `dim_{𝔽₂} H²(Γ,𝔽₂)`" for finitely generated pro-`p` groups
  (Neukirch--Schmidt--Wingberg I §4.3, Koch Ch. 11);
* derives from the dictionary both the previously stated presentation-form results
  (`h2_le_six_of_relationRankLeSix`, `relatorRankLe_of_h2_le_six`) and the bridge
  `relatorHalfOf_of_gaschutzDictionary`: a genuine cohomological bound `dim_{𝔽₂} H²(Γ,𝔽₂) ≤ 6`
  together with the dictionary gives `RelatorHalfOf Γ 5 6`, i.e. six relators for **every** dense
  generating five-element family.

## What is *not* proved here

`GaschutzDictionary` itself.  It is the single classical input of the chapter; its proof needs the
five-term exact sequence of `1 → K → F → Γ → 1` for the free pro-`p` group `F` together with
Nakayama's lemma for the completed group algebra `𝔽_p[[Γ]]`, neither of which is available.  See
`README.md` §3 for the precise statement of the gap and the reduction chain, and §5 for the two
machine-checkable traps that rule out the "cheap" proofs.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Work.RelatorRank

/-- The **trivial** `Γ`-action on `𝔽₂ = ℤ/2`. -/
@[reducible] def f2TrivialAction (Γ : Type*) [Group Γ] : DistribMulAction Γ (ZMod 2) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- With the trivial action, `𝔽₂` is a discrete `Γ`-module in the sense needed for continuous
cohomology: the stabilizer of every point is all of `Γ`. -/
theorem f2Discrete (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    letI := f2TrivialAction Γ
    Work.ConCohomology.IsDiscreteGModule Γ (ZMod 2) := by
  letI := f2TrivialAction Γ
  refine ⟨fun m => ?_⟩
  show IsLocallyConstant (fun _ : Γ => m)
  exact IsLocallyConstant.const m

/-- **The continuous cohomology group `H²(Γ, 𝔽₂)`** of a topological group `Γ`, with trivial
coefficients: the quotient of the locally constant `2`-cocycles `Γ × Γ → 𝔽₂` by the
`2`-coboundaries (`Work.ConCohomology.H2`).  For a profinite `Γ` this is the group denoted
`H²(Γ, 𝔽₂)` in the Galois-cohomology literature; it differs from the *abstract* group cohomology of
the underlying discrete group (for `Γ = ℤ₂` the abstract `H²` is `𝔽₂` whereas `cd(ℤ₂) = 1`). -/
noncomputable abbrev contH2 (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Type _ :=
  letI := f2TrivialAction Γ
  letI : Work.ConCohomology.IsDiscreteGModule Γ (ZMod 2) := f2Discrete Γ
  Work.ConCohomology.H2 Γ (ZMod 2)

/-- **The `𝔽₂`-dimension of the continuous cohomology `H²(Γ, 𝔽₂)` is at most `r`.**  Phrased
without a dimension function: `H²` has `2 ^ k` elements for some `k ≤ r`.  (If `H²` is infinite the
statement is false for every `r`, as it should be.) -/
def ContH2DimLe (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (r : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ r ∧ Nat.card (contH2 Γ) = 2 ^ k

/-- `ContH2DimLe` is monotone in `r`. -/
theorem ContH2DimLe.mono {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {r r' : ℕ} (h : ContH2DimLe Γ r) (hr : r ≤ r') : ContH2DimLe Γ r' := by
  obtain ⟨k, hk, hcard⟩ := h
  exact ⟨k, le_trans hk hr, hcard⟩

/-- **Gaschütz's cohomological value theorem.**  The minimal number of relators of a presentation
of `Γ` on `GeneratorRank Γ` generators is `dim_{𝔽₂} H²(Γ, 𝔽₂)`: the presentation bound
`RelatorRankLe Γ r` and the cohomological bound `ContH2DimLe Γ r` are the same condition.  This is
the classical theorem of Neukirch--Schmidt--Wingberg I §4.3 / Koch, *Galois theory of
`p`-extensions* Ch. 11 for finitely generated pro-`p` groups.

This is one of the two named classical inputs of the chapter.  Its proof needs the five-term exact
sequence of `1 → K → F → Γ → 1` (`F` the free pro-`p` group) together with the identification of
`H¹(K,𝔽₂)^Γ` with the generators of the relation module `K/(K^p[K,K])`, plus Nakayama's lemma for
`𝔽_p[[Γ]]`.  See `README.md` §3. -/
def GaschutzCohomologicalValue (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Prop :=
  ∀ r : ℕ, RelatorRankLe Γ r ↔ ContH2DimLe Γ r

/-- From the value theorem, a cohomological bound on `H²` gives the presentation bound. -/
theorem relatorRankLe_of_contH2DimLe {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hdict : GaschutzCohomologicalValue Γ) {r : ℕ} (h : ContH2DimLe Γ r) :
    RelatorRankLe Γ r :=
  (hdict r).mpr h

/-- Conversely, the presentation bound gives the cohomological bound. -/
theorem contH2DimLe_of_relatorRankLe {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hdict : GaschutzCohomologicalValue Γ) {r : ℕ} (h : RelatorRankLe Γ r) :
    ContH2DimLe Γ r :=
  (hdict r).mp h

/-- **A presentation on five generators with six relators gives `dim_{𝔽₂} H²(Γ,𝔽₂) ≤ 6`**, stated
with the genuine continuous cohomology group `H²(Γ,𝔽₂)`. -/
theorem contH2DimLe_six_of_hasProP2Presentation {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hdict : GaschutzCohomologicalValue Γ) (hmin : NoSmallerGeneratingFamily Γ 5)
    (h : HasProP2Presentation Γ 5 6) : ContH2DimLe Γ 6 :=
  (hdict 6).mp
    ((relatorRankLeSix_iff_hasProP2Presentation hmin h.to_hasDenseGeneratingFamily).mpr h)

/-- **The bridge, from a genuine cohomological bound.**  If the arithmetic input is stated as
`dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ 6` in the *continuous* cohomology of Γ, then -- together with the
generator half `HasDenseGeneratingFamily Γ 5`, the minimality of five-element generating families,
the cohomological value theorem and the invariance of the relation count -- **every** dense
generating five-element family of `Γ` admits a relator set of at most six elements. -/
theorem relatorHalfOf_of_contH2DimLe {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hdict : GaschutzCohomologicalValue Γ)
    (hinv : RelationRankInvariant Γ 5 6) (hmin : ¬ HasDenseGeneratingFamily Γ 4)
    (hex : HasDenseGeneratingFamily Γ 5) (h : ContH2DimLe Γ 6) :
    ∀ gen : Fin 5 → Γ, DenseGenerating gen →
      ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
        MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) := by
  have hmin' : NoSmallerGeneratingFamily Γ 5 := noSmallerGeneratingFamily_five_iff.mpr hmin
  have hpres : HasProP2Presentation Γ 5 6 :=
    (relatorRankLeSix_iff_hasProP2Presentation hmin' hex).mp (relatorRankLe_of_contH2DimLe hdict h)
  exact relator_half_of_relation_rank_le_six hmin hinv hpres

end Work.RelatorRank
