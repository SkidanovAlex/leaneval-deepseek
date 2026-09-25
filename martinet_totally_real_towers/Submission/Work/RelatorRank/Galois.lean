import Submission.Work.RelatorRank.Cohomology

/-!
# `Work.RelatorRank` -- instantiation to `Gal(K/ℚ)`

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Galois`.

The workspace's bridge is stated for `Γ = Gal(K/ℚ) = K ≃ₐ[ℚ] K`, a finitely generated pro-`2` group
with the Krull topology (`Mathlib.FieldTheory.KrullTopology` supplies `IsTopologicalGroup`, and
`Mathlib.FieldTheory.Galois.Profinite` supplies `CompactSpace` for `[IsGalois ℚ K]`), and its three
halves are named in `Submission/NumberField/TamePresentationDatum.lean`:

```lean
Submission.NumberField.GeneratorHalf K        -- ∃ gen : Fin 5 → Γ, dense
Submission.NumberField.RelatorHalf K          -- ∀ gen : Fin 5 → Γ, dense → ∃ rel, card ≤ 6, ker = nc rel
Submission.NumberField.RelationRankLeSix K    -- ∃ gen rel : Fin 5, dense, card ≤ 6, ker = nc rel
Submission.NumberField.GeneratorMinimal K     -- ¬ ∃ gen : Fin 4 → Γ, dense
```

That module cannot be imported here (it belongs to the arithmetic chapter), so the four predicates
are restated in this namespace, together with the proof that they are *definitionally* the
corresponding statements of this chapter (`GaloisRelatorHalf K ↔ RelatorHalfOf (K ≃ₐ[ℚ] K) 5 6`,
and so on).  A caller inside the arithmetic chapter only has to write the one-line identifications.

The bridge itself is inherited from `Submission.Work.RelatorRank.Bridge` -- and comes with the
missing invariance hypothesis `RelationRankInvariant (K ≃ₐ[ℚ] K) 5 6`; see the `README.md`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

variable (K : Type) [Field K] [Algebra ℚ K] [IsGalois ℚ K]

/-- **`Submission.NumberField.RelatorHalf K`**, restated in this namespace: for every five-element
topologically generating family of `Γ = Gal(K/ℚ)` there is a relator set of at most six words
presenting `Γ` on that family. -/
def GaloisRelatorHalf : Prop :=
  ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤ →
    ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))

/-- **`Submission.NumberField.RelationRankLeSix K`**, restated in this namespace: some five-element
topologically generating family of `Γ = Gal(K/ℚ)` is presented by at most six relators. -/
def GaloisRelationRankLeSix : Prop :=
  ∃ (gen : Fin 5 → (K ≃ₐ[ℚ] K)) (rel : Finset (FreeGroup (Fin 5))),
    (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤ ∧ rel.card ≤ 6 ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))

/-- **`Submission.NumberField.GeneratorHalf K`**, restated in this namespace. -/
def GaloisGeneratorHalf : Prop :=
  ∃ gen : Fin 5 → (K ≃ₐ[ℚ] K), (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤

/-- **`Submission.NumberField.GeneratorMinimal K`**, restated in this namespace: there is no
four-element topologically generating family of `Γ = Gal(K/ℚ)`. -/
def GaloisGeneratorMinimal : Prop :=
  ¬ ∃ gen : Fin 4 → (K ≃ₐ[ℚ] K), (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤

/-- The restated relator half is the chapter's presentation-independent relation bound for
`Γ = Gal(K/ℚ)`, `d = 5`, `r = 6`. -/
theorem galoisRelatorHalf_iff : GaloisRelatorHalf K ↔ RelatorHalfOf (K ≃ₐ[ℚ] K) 5 6 := Iff.rfl

/-- The restated `∃`-form is the chapter's `HasProP2Presentation (Gal(K/ℚ)) 5 6`. -/
theorem galoisRelationRankLeSix_iff :
    GaloisRelationRankLeSix K ↔ HasProP2Presentation (K ≃ₐ[ℚ] K) 5 6 := by
  constructor
  · rintro ⟨gen, rel, hdense, hcard, hker⟩
    exact ⟨{ gen := gen, rel := rel, dense := hdense, card_le := hcard, ker_eq := hker }⟩
  · rintro ⟨P⟩
    exact ⟨P.gen, P.rel, P.dense, P.card_le, P.ker_eq⟩

/-- The restated generator half is `HasDenseGeneratingFamily (Gal(K/ℚ)) 5`. -/
theorem galoisGeneratorHalf_iff :
    GaloisGeneratorHalf K ↔ HasDenseGeneratingFamily (K ≃ₐ[ℚ] K) 5 := Iff.rfl

/-- The restated minimality is `¬ HasDenseGeneratingFamily (Gal(K/ℚ)) 4`. -/
theorem galoisGeneratorMinimal_iff :
    GaloisGeneratorMinimal K ↔ ¬ HasDenseGeneratingFamily (K ≃ₐ[ℚ] K) 4 := Iff.rfl

/-- **The bridge in the shape used by the arithmetic chapter.**  From

* the `∃`-form `GaloisRelationRankLeSix K` (what the Shafarevich--Koch relation bound produces),
* the minimality `GaloisGeneratorMinimal K` (no four-element generating family, proved
  arithmetically from the multiquadratic level), and
* the missing group-theoretic invariance `RelationRankInvariant (Gal(K/ℚ)) 5 6`,

conclude the presentation-independent relator half `GaloisRelatorHalf K`. -/
theorem galoisRelatorHalf_of_relationRankLeSix (hmin : GaloisGeneratorMinimal K)
    (hinv : RelationRankInvariant (K ≃ₐ[ℚ] K) 5 6) (h : GaloisRelationRankLeSix K) :
    GaloisRelatorHalf K :=
  relator_half_of_relation_rank_le_six (galoisGeneratorMinimal_iff K |>.mp hmin) hinv
    ((galoisRelationRankLeSix_iff K).mp h)

/-- The same bridge with the cohomological form of the arithmetic input
(`dim_{𝔽₂} H²(Gal(K/ℚ), 𝔽₂) ≤ 6`), which needs the generator half `GaloisGeneratorHalf K`. -/
theorem galoisRelatorHalf_of_h2_le_six (hmin : GaloisGeneratorMinimal K)
    (hgen : GaloisGeneratorHalf K) (hinv : RelationRankInvariant (K ≃ₐ[ℚ] K) 5 6)
    (h : H2DimLe (K ≃ₐ[ℚ] K) 6) : GaloisRelatorHalf K :=
  relator_half_of_h2_le_six
    (noSmallerGeneratingFamily_five_iff.mpr ((galoisGeneratorMinimal_iff K).mp hmin))
    ((galoisGeneratorHalf_iff K).mp hgen) hinv h

end Work.RelatorRank
