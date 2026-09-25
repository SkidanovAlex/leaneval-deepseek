import Mathlib
import Submission.Work.AbstractDictionary.Defs
import Submission.Work.AbstractDictionary.Helpers
import Submission.Work.TameSalle.generatorRank_eq_five_of_isMaximalTamePro2
import Submission.Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame

/-!
# `Work.AbstractDictionary` -- the relation-rank dictionary for the maximal tame pro-`2` extension

**Namespace** `Work.AbstractDictionary`; module `Submission.Work.AbstractDictionary.Main`.

This is the area's theorem: the second input of the assembled endgame

```lean
Work.TameRelation.tameRelationBound (shaTameInjection) (gaschutzCohomologicalValue)
```

-- the `sorry` at `Submission.lean:89`, in the `gaschutzCohomologicalValue` declaration -- is reduced to **one** named classical theorem
and **one** named residual finiteness side condition, with everything else -- the generator count
`d(Γ) = 5`, the presentation bookkeeping, and the closed/abstract conversion -- proved.

## The reduction

For `K` a maximal tame pro-`2` extension of `ℚ` (`Work.TameArithmetic.IsMaximalTamePro2 K`,
`Γ = Gal(K/ℚ) = K ≃ₐ[ℚ] K`, `S = {17,41,73,89,97}`) the dictionary

  `Work.RelatorRank.GaschutzCohomologicalValue Γ`
  = `∀ r, RelatorRankLe Γ r ↔ ContH2DimLe Γ r`

is the conjunction of the two implications

* **`⟸` (presentation from cohomology)**: the classical Gaschütz value theorem in the *closed*
  normalisation (`Work.AbstractDictionary.GaschutzProP2Value`) produces, from
  `dim_{𝔽₂} H²_cont(Γ,𝔽₂) ≤ r`, a relator set `S` generating the relation kernel as a **closed**
  normal subgroup (`Work.HopfGaschutz.ClosedNormalGenerates`).  The named side condition
  `Work.AbstractDictionary.ResidualTwoFinitenessPresentations` -- residually `2`-finiteness of the
  abstract group presented by `S` -- then upgrades this to the **abstract** kernel equality
  (`Work.AbstractDictionary.ker_eq_normalClosure_of_residualTwoFiniteness`, resting on
  `Work.ShafarevichKoch.ker_eq_normalClosure_of_closed`), giving
  `HasProP2Presentation Γ 5 r` and hence, because `d(Γ) = 5`
  (`Work.TameSalle.generatorRank_eq_five_of_isMaximalTamePro2`), `RelatorRankLe Γ r`.
  `gen` is supplied by `Work.TameArithmetic.dense_generatingFamily_of_isMaximalTamePro2`.
* **`⟹` (cohomology from presentation)**: `RelatorRankLe Γ r` gives an abstract presentation, whose
  relators automatically satisfy the *closed* condition, so the `⟸`-half of
  `GaschutzProP2Value` -- the "easy" half, classically proved by the pro-`2` five-term sequence --
  returns `dim_{𝔽₂} H²_cont(Γ,𝔽₂) ≤ r`.

## What is *not* assumed

Neither the arithmetic Sha bound (`Work.ShaAssembly.ShaTameInjection`, the sibling area
`Submission/Work/ShaBound`) nor the open efficiency question
(`Work.HopfGaschutz.GaschutzDictionary`, `Submission/PLAN.md` §30) is used anywhere.  The
`GaschutzDictionary` route is the *discrete* normalisation and is open in general (Mann's question
18; Gardam arXiv:1705.02040); the closed normalisation used here is the classical theorem.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical

namespace Work.AbstractDictionary

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

/-! ## The generator count `d(Γ) = 5` and the canonical presentation form -/

/-- **`Γ = Gal(K/ℚ)` is residually a finite `2`-group** for a maximal tame pro-`2` extension `K`
of `ℚ` (re-exported from `Work.TameArithmetic`). -/
theorem residuallyFiniteTwoGroup_galoisGroup (hK : Work.TameArithmetic.IsMaximalTamePro2 K) :
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup (K ≃ₐ[ℚ] K) :=
  Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame hK

/-- **`d(Γ) = 5`, in the canonical presentation form**: for `K` a maximal tame pro-`2` extension of
`ℚ`, the relation-rank bound `RelatorRankLe Γ r` is the `∃`-form with five generators. -/
theorem relatorRankLe_iff_hasProP2Presentation_five
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K) (r : ℕ) :
    Work.RelatorRank.RelatorRankLe (K ≃ₐ[ℚ] K) r ↔
      Work.RelatorRank.HasProP2Presentation (K ≃ₐ[ℚ] K) 5 r := by
  rw [Work.RelatorRank.relatorRankLe_iff,
    Work.TameSalle.generatorRank_eq_five_of_isMaximalTamePro2 K hK]

/-! ## The two implications of the dictionary -/

/-- **Cohomology from presentation** (the `⟹`-direction of
`Work.RelatorRank.GaschutzCohomologicalValue`).

`RelatorRankLe Γ r` provides an abstract presentation `⟨gen | rel⟩` of `Γ` with `|rel| ≤ r`; its
relators satisfy the closed normal generation condition for the trivial reason that their abstract
normal closure *is* the kernel, so the `⟸`-half of the closed value theorem
(`Work.AbstractDictionary.GaschutzProP2Value`) gives `dim_{𝔽₂} H²_cont(Γ,𝔽₂) ≤ r`.

Note the asymmetry with the other direction: *this* one needs no residual finiteness side
condition, only the classical half of the value theorem. -/
theorem contH2DimLe_of_relatorRankLe (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hvalue : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen)
    (r : ℕ) (h : Work.RelatorRank.RelatorRankLe (K ≃ₐ[ℚ] K) r) :
    Work.RelatorRank.ContH2DimLe (K ≃ₐ[ℚ] K) r := by
  obtain ⟨P⟩ := (relatorRankLe_iff_hasProP2Presentation_five hK r).mp h
  refine (hvalue P.gen P.dense).contH2DimLe ⟨P.rel, P.card_le, ?_, ?_⟩
  · intro s hs
    rw [← MonoidHom.mem_ker, P.ker_eq]
    exact Subgroup.subset_normalClosure hs
  · intro Q _ _ hQ φ hφ
    rw [P.ker_eq]
    exact Subgroup.normalClosure_le_normal fun s hs => MonoidHom.mem_ker.mpr (hφ s hs)

/-- **Presentation from cohomology** (the `⟸`-direction of
`Work.RelatorRank.GaschutzCohomologicalValue`).

From `dim_{𝔽₂} H²_cont(Γ,𝔽₂) ≤ r` the closed value theorem produces a *closed* presentation with
`≤ r` relators; residually `2`-finiteness of the presented abstract group upgrades it to an abstract
presentation with the same generators and relators; and `d(Γ) = 5` converts that into
`RelatorRankLe Γ r`. -/
theorem relatorRankLe_of_contH2DimLe (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hvalue : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen)
    (hres : ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K))
    (r : ℕ) (hcont : Work.RelatorRank.ContH2DimLe (K ≃ₐ[ℚ] K) r) :
    Work.RelatorRank.RelatorRankLe (K ≃ₐ[ℚ] K) r := by
  obtain ⟨gen, hgen⟩ := Work.TameArithmetic.dense_generatingFamily_of_isMaximalTamePro2 K hK
  obtain ⟨S, hS, hkill, hclosed⟩ := (hvalue gen hgen).exists_closedRelators hcont
  have hker : MonoidHom.ker (FreeGroup.lift gen) =
      Subgroup.normalClosure (S : Set (FreeGroup (Fin 5))) :=
    ker_eq_normalClosure_of_residualTwoFiniteness hres hgen hkill hclosed
  refine (relatorRankLe_iff_hasProP2Presentation_five hK r).mpr ⟨?_⟩
  exact ⟨gen, S, hgen, hS, hker⟩

/-! ## The area's theorem -/

/-- **The relation-rank dictionary for the maximal tame pro-`2` extension** (the `sorry` at
`Submission.lean:89`), from the two named inputs.

This is `Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K)`, i.e.
`∀ r, RelatorRankLe Γ r ↔ ContH2DimLe Γ r`, for every `K` with `IsMaximalTamePro2 K`, given

* `hvalue` -- the classical Gaschütz value theorem in the closed normalisation, for every dense
  generating five-family (`Work.AbstractDictionary.GaschutzProP2Value`), and
* `hres` -- the residual `2`-finiteness side condition
  (`Work.AbstractDictionary.ResidualTwoFinitenessPresentations`). -/
theorem gaschutzCohomologicalValue_of_inputs (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hvalue : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen)
    (hres : ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K)) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  fun r => ⟨contH2DimLe_of_relatorRankLe hK hvalue r, relatorRankLe_of_contH2DimLe hK hvalue hres r⟩

/-- **The two named inputs of the dictionary, bundled**, at a fixed maximal tame pro-`2`
extension `K`. -/
def DictionaryInputs (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (_hK : Work.TameArithmetic.IsMaximalTamePro2 K) : Prop :=
  (∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen) ∧
    ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K)

/-- The dictionary from the bundled inputs. -/
theorem gaschutzCohomologicalValue_of_dictionaryInputs (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (h : DictionaryInputs K hK) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  gaschutzCohomologicalValue_of_inputs hK h.1 h.2

/-- **THE COMPOSITION WITNESS.**

The statement that replaces the `sorry` in `Submission.lean`'s
`theorem gaschutzCohomologicalValue (K) ... (hK) : GaschutzCohomologicalValue (K ≃ₐ[ℚ] K)`,
proved from the two named inputs of this area, stated for all `K` simultaneously so that it drops
into the endgame unchanged.

`Submission.lean` can be edited to

```lean
theorem gaschutzProP2Value_granted (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K) (gen : Fin 5 → (K ≃ₐ[ℚ] K))
    (hgen : Work.RelatorRank.DenseGenerating gen) :
    Work.AbstractDictionary.GaschutzProP2Value 5 gen := by sorry

theorem residualTwoFiniteness_granted (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K) :
    Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K) := by sorry

theorem gaschutzCohomologicalValue (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  Work.AbstractDictionary.gaschutzCohomologicalValue_of_classicalInputs
    gaschutzProP2Value_granted residualTwoFiniteness_granted K hK
```

so that the single `sorry` of that declaration is replaced by a *proof*, at the cost of two
further `sorry`s which are exactly the two named classical inputs of this area (and not the open
efficiency question, nor the Sha bound of the sibling area). -/
theorem gaschutzCohomologicalValue_of_classicalInputs
    (hValue : ∀ (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K],
      Work.TameArithmetic.IsMaximalTamePro2 K →
        ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
          GaschutzProP2Value 5 gen)
    (hRes : ∀ (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K],
      Work.TameArithmetic.IsMaximalTamePro2 K →
        ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K))
    (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  gaschutzCohomologicalValue_of_inputs hK (hValue K hK) (hRes K hK)

/-! ## The consumer's shape (`Work.TameArithmetic.TamePro2Presentation`) -/

/-- **The five-generator six-relator presentation**, in the shape the arithmetic chapters consume
(`Work.TameArithmetic.TamePro2Presentation`, the field-by-field translation of
`Work.RelatorRank.ProP2PresentationData`), from a cohomological bound
`dim_{𝔽₂} H²(Γ,𝔽₂) ≤ 6` and the two named inputs.

This is the precise interface through which the arithmetic endgame (`Work.TameRelation`, whose
`relationRankHopf_of_gaschutz` consumes exactly this) is fed. -/
theorem nonempty_tamePro2Presentation_of_contH2DimLe_six
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hvalue : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen)
    (hres : ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K))
    (h : Work.RelatorRank.ContH2DimLe (K ≃ₐ[ℚ] K) 6) :
    Nonempty (Work.TameArithmetic.TamePro2Presentation K) := by
  obtain ⟨P⟩ := (relatorRankLe_iff_hasProP2Presentation_five hK 6).mp
    (relatorRankLe_of_contH2DimLe hK hvalue hres 6 h)
  exact ⟨{ rel := P.rel, gen := P.gen, rel_card := P.card_le, ker_eq := P.ker_eq, dense := P.dense }⟩

end Work.AbstractDictionary
