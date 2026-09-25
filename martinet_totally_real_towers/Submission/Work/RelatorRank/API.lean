import Submission.Work.RelatorRank.Defs

/-!
# `Work.RelatorRank` -- the basic API of the relation-rank invariants

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.API`.

Elementary lemmas about `DenseGenerating`, `HasDenseGeneratingFamily`, `GeneratorRank`,
`HasProP2Presentation`, `RelatorRankLe` and the abstract analogues:

* `denseGenerating_comp_surjective` -- re-indexing a dense generating family along a surjection;
* `HasDenseGeneratingFamily.mono` -- a dense generating `d`-family is one of size `d' ≥ d`;
* `hasDenseGeneratingFamily_generatorRank` / `hasDenseGeneratingFamily_of_generatorRank_le` --
  the `sInf` characterisation of `GeneratorRank`;
* `generatorRank_eq_of` -- **the minimality computation**: a dense generating family of size `d`
  with no smaller one has `GeneratorRank Γ = d`;
* `generatorRank_eq_iff` -- `GeneratorRank Γ = d ↔ HasDenseGeneratingFamily Γ d ∧
  NoSmallerGeneratingFamily Γ d` (given that a finite dense generating family exists);
* `HasProP2Presentation.mono_right` -- the relator bound is monotone in `r`;
* `HasProP2Presentation.to_hasDenseGeneratingFamily`;
* `relatorRankLe_iff` and `relationRankLeSix_iff_relatorRankLe` -- **the decoupling**: under
  minimality the arithmetic `∃`-form on five generators is equivalent to the canonical relation-rank
  bound.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.RelatorRank

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## Dense generation -/

/-- Re-indexing a dense generating family along a surjection is again dense generating. -/
theorem denseGenerating_comp_surjective {ι ι' : Type*} (gen : ι → Γ)
    (hgen : DenseGenerating gen) (e : ι' → ι) (he : Function.Surjective e) :
    DenseGenerating (gen ∘ e) := by
  rw [denseGenerating_iff] at hgen ⊢
  have hrange : Set.range (gen ∘ e) = Set.range gen := by
    rw [Set.range_comp, he.range_eq, Set.image_univ]
  rw [hrange, hgen]

/-- A dense generating family of size `d` is a dense generating family of every size `d' ≥ d`
(pad with the identity element). -/
theorem HasDenseGeneratingFamily.mono {d d' : ℕ} (h : d ≤ d')
    (hG : HasDenseGeneratingFamily Γ d) : HasDenseGeneratingFamily Γ d' := by
  obtain ⟨gen, hgen⟩ := hG
  refine ⟨fun i : Fin d' => if hi : (i : ℕ) < d then gen ⟨i.1, hi⟩ else 1, ?_⟩
  rw [denseGenerating_iff] at hgen ⊢
  refine top_le_iff.mp ?_
  rw [← hgen]
  refine Subgroup.topologicalClosure_mono (Subgroup.closure_mono ?_)
  rintro x ⟨j, rfl⟩
  exact ⟨⟨j.1, lt_of_lt_of_le j.2 h⟩, by simp only [dite_eq_left j.2]⟩

/-- `GeneratorRank Γ ≤ d` when a dense generating family of size `d` exists. -/
theorem generatorRank_le_of_hasDenseGeneratingFamily {d : ℕ}
    (h : HasDenseGeneratingFamily Γ d) : GeneratorRank Γ ≤ d :=
  Nat.sInf_le h

/-- The least size of a dense generating family is attained, when a finite one exists. -/
theorem hasDenseGeneratingFamily_generatorRank (h : ∃ d : ℕ, HasDenseGeneratingFamily Γ d) :
    HasDenseGeneratingFamily Γ (GeneratorRank Γ) :=
  Nat.sInf_mem h

/-- If a finite dense generating family exists and `GeneratorRank Γ ≤ d`, then there is a dense
generating family of size `d`. -/
theorem hasDenseGeneratingFamily_of_generatorRank_le (hex : ∃ d : ℕ, HasDenseGeneratingFamily Γ d)
    {d : ℕ} (h : GeneratorRank Γ ≤ d) : HasDenseGeneratingFamily Γ d :=
  (hasDenseGeneratingFamily_generatorRank hex).mono h

/-- **The minimality computation.**  A dense generating family of size `d` is *minimal* -- there is
no dense generating family of smaller size -- if and only if `GeneratorRank Γ = d`.

This is the form in which the workspace's `Submission.NumberField.GeneratorMinimal` (the absence of
a dense generating family of size `< 5`) meets the generator rank. -/
theorem generatorRank_eq_of {d : ℕ} (hex : HasDenseGeneratingFamily Γ d)
    (hmin : NoSmallerGeneratingFamily Γ d) : GeneratorRank Γ = d := by
  refine le_antisymm (generatorRank_le_of_hasDenseGeneratingFamily hex) ?_
  by_contra h
  exact hmin (GeneratorRank Γ) (Nat.lt_of_not_le h) (hasDenseGeneratingFamily_generatorRank ⟨d, hex⟩)

/-- `GeneratorRank Γ = d` is characterised by density in size `d` plus minimality, whenever a
finite dense generating family exists. -/
theorem generatorRank_eq_iff {d : ℕ} (hex : HasDenseGeneratingFamily Γ d) :
    GeneratorRank Γ = d ↔ NoSmallerGeneratingFamily Γ d := by
  constructor
  · intro h d' hd' hgen
    have : GeneratorRank Γ ≤ d' := generatorRank_le_of_hasDenseGeneratingFamily hgen
    omega
  · exact generatorRank_eq_of hex

/-- A dense generating `d`-family is a minimal dense generating family iff `GeneratorRank Γ = d`. -/
theorem isMinimalDenseGeneratingFamily_iff_generatorRank_eq {d : ℕ} (gen : Fin d → Γ)
    (hgen : DenseGenerating gen) :
    IsMinimalDenseGeneratingFamily d gen ↔ GeneratorRank Γ = d := by
  constructor
  · intro h
    exact generatorRank_eq_of ⟨gen, hgen⟩ h.2
  · intro h
    refine ⟨hgen, fun d' hd' hgen' => ?_⟩
    have : GeneratorRank Γ ≤ d' := generatorRank_le_of_hasDenseGeneratingFamily hgen'
    omega

/-! ## Presentation data -/

/-- The relator bound is monotone in `r`. -/
theorem HasProP2Presentation.mono_right {d r r' : ℕ} (h : HasProP2Presentation Γ d r)
    (hr : r ≤ r') : HasProP2Presentation Γ d r' := by
  obtain ⟨P⟩ := h
  exact ⟨{ P with card_le := le_trans P.card_le hr }⟩

/-- A presentation datum densely generates. -/
theorem HasProP2Presentation.denseGenerating {d r : ℕ} (h : HasProP2Presentation Γ d r) :
    ∃ gen : Fin d → Γ, DenseGenerating gen := by
  obtain ⟨P⟩ := h
  exact ⟨P.gen, P.dense⟩

theorem HasProP2Presentation.to_hasDenseGeneratingFamily {d r : ℕ}
    (h : HasProP2Presentation Γ d r) : HasDenseGeneratingFamily Γ d :=
  h.denseGenerating

/-- The generator rank is bounded by the number of generators of any presentation. -/
theorem generatorRank_le_of_hasProP2Presentation {d r : ℕ}
    (h : HasProP2Presentation Γ d r) : GeneratorRank Γ ≤ d :=
  generatorRank_le_of_hasDenseGeneratingFamily h.to_hasDenseGeneratingFamily

/-! ## The decoupling: the canonical relation-rank bound -/

theorem relatorRankLe_iff {r : ℕ} :
    RelatorRankLe Γ r ↔ HasProP2Presentation Γ (GeneratorRank Γ) r := Iff.rfl

theorem relatorRankOfLe_iff {d r : ℕ} :
    RelatorRankOfLe Γ d r ↔ Nonempty (ProP2PresentationData Γ d r) := Iff.rfl

theorem RelatorRankLe.mono {r r' : ℕ} (h : RelatorRankLe Γ r) (hr : r ≤ r') :
    RelatorRankLe Γ r' := h.mono_right hr

/-- **The decoupling.**  Under the minimality hypothesis `GeneratorRank Γ = 5`, the arithmetic
`∃`-form with five generators and six relators is *equivalent* to the canonical relation-rank
bound `RelatorRankLe Γ 6`.  This is the sense in which an arithmetic relation bound is decoupled
from the particular presentation it is produced by: it can always be consumed through the
canonical generator number. -/
theorem relatorRankLeSix_iff_hasProP2Presentation {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (hmin : NoSmallerGeneratingFamily Γ 5)
    (hex : HasDenseGeneratingFamily Γ 5) :
    RelatorRankLe Γ 6 ↔ HasProP2Presentation Γ 5 6 := by
  have hgr : GeneratorRank Γ = 5 := generatorRank_eq_of hex hmin
  rw [relatorRankLe_iff, hgr]

/-- The general-`d` form of `relatorRankLeSix_iff_hasProP2Presentation`. -/
theorem relatorRankLe_iff_hasProP2Presentation {d r : ℕ}
    (hmin : NoSmallerGeneratingFamily Γ d) (hex : HasDenseGeneratingFamily Γ d) :
    RelatorRankLe Γ r ↔ HasProP2Presentation Γ d r := by
  have hgr : GeneratorRank Γ = d := generatorRank_eq_of hex hmin
  rw [relatorRankLe_iff, hgr]

/-! ## The abstract core -/

section Abstract

variable {G : Type*} [Group G]

/-- Re-indexing a generating family along a surjection is again generating. -/
theorem generating_comp_surjective {ι ι' : Type*} (gen : ι → G)
    (hgen : Generating gen) (e : ι' → ι) (he : Function.Surjective e) :
    Generating (gen ∘ e) := by
  rw [generating_iff] at hgen ⊢
  have hrange : Set.range (gen ∘ e) = Set.range gen := by
    rw [Set.range_comp, he.range_eq, Set.image_univ]
  rw [hrange, hgen]

/-- A generating family of size `d` is a generating family of every size `d' ≥ d`. -/
theorem HasGeneratingFamily.mono {d d' : ℕ} (h : d ≤ d') (hG : HasGeneratingFamily G d) :
    HasGeneratingFamily G d' := by
  obtain ⟨gen, hgen⟩ := hG
  refine ⟨fun i : Fin d' => if hi : (i : ℕ) < d then gen ⟨i.1, hi⟩ else 1, ?_⟩
  rw [generating_iff] at hgen ⊢
  refine top_le_iff.mp ?_
  rw [← hgen]
  refine Subgroup.closure_mono ?_
  rintro x ⟨j, rfl⟩
  exact ⟨⟨j.1, lt_of_lt_of_le j.2 h⟩, by simp only [dite_eq_left j.2]⟩

theorem genRank_le_of_hasGeneratingFamily {d : ℕ} (h : HasGeneratingFamily G d) : GenRank G ≤ d :=
  Nat.sInf_le h

theorem hasGeneratingFamily_genRank (h : ∃ d : ℕ, HasGeneratingFamily G d) :
    HasGeneratingFamily G (GenRank G) :=
  Nat.sInf_mem h

theorem genRank_eq_of {d : ℕ} (hex : HasGeneratingFamily G d)
    (hmin : ∀ d' : ℕ, d' < d → ¬ HasGeneratingFamily G d') : GenRank G = d := by
  refine le_antisymm (genRank_le_of_hasGeneratingFamily hex) ?_
  by_contra h
  exact hmin (GenRank G) (Nat.lt_of_not_le h) (hasGeneratingFamily_genRank ⟨d, hex⟩)

/-- The relator bound is monotone in `r`, abstract version. -/
theorem HasAbstractPresentation.mono_right {d r r' : ℕ} (h : HasAbstractPresentation G d r)
    (hr : r ≤ r') : HasAbstractPresentation G d r' := by
  obtain ⟨P⟩ := h
  exact ⟨{ P with card_le := le_trans P.card_le hr }⟩

theorem HasAbstractPresentation.to_hasGeneratingFamily {d r : ℕ}
    (h : HasAbstractPresentation G d r) : HasGeneratingFamily G d := by
  obtain ⟨P⟩ := h
  exact ⟨P.gen, P.generating⟩

end Abstract

end Work.RelatorRank
