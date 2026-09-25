import Mathlib
import Submission.Work.AbstractDictionary.All
import Submission.Work.ShafarevichKoch.KcCohomology
import Submission.Work.ShafarevichKoch.exists_generatingSet_card_five_Kc
import Submission.Work.ShafarevichKoch.KcRealization

/-!
# `Work.ShafarevichKoch.GaschutzClosedBridge` -- the crux from the *closed* Gaschütz dictionary

The chapter's crux `KcProTwoPresentationInput` is (proved equivalent, `Crux.lean`, to) the existence
of a presentation of `G_∅ = Gal(Kc_∅/Kc)` on `5 = rank₂ Cl(Kc)` generators with at most
`6 = 5 + d₂(O_{Kc}^×)` relators.  This module reduces it to **the same two named classical inputs
that the sibling area `Submission/Work/AbstractDictionary` uses for the tame setting**, together with
the single arithmetic bound `dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`:

* `Work.AbstractDictionary.GaschutzProP2Value 5 gen` -- the classical Gaschütz value theorem in the
  **closed** (pro-`2`) normalisation, for a dense generating five-family `gen` of `G_∅`
  (Gaschütz 1953; Koch, *Galois theory of `p`-extensions*, Ch. 11; Neukirch--Schmidt--Wingberg
  I §4.3).  Pure pro-`2` group theory;
* `Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := G_∅)` -- the *seam* between the
  closed and the abstract normalisation;
* `Work.RelatorRank.ContH2DimLe (G_∅) 6` -- the deliverable's item (2) in cohomological form, which
  the chapter has already reduced (`Gaschutz/WeakUnitInput`, `CruxOneByte`, `H2Half`, `CountZ`) to
  the single inequality `#H³(G_∅,ℤ)[2] ≤ 2`.

Why the closed normalisation.  The workspace's `Work.RelatorRank.GaschutzCohomologicalValue` states
the dictionary with the **abstract** normal closure, and the passage from the classical *closed*
statement to it is not a formality: for `Γ = ℤ/2`, `gen` the generator and `S = {x⁶}` the closed
condition holds while `⟪x⁶⟫ = 6ℤ ⊊ 2ℤ = ker` (`Work.HopfGaschutz.Counterexample`,
`Work.AbstractDictionary.not_residualTwoFinitenessPresentations_trivial`).  The sibling area
`Submission/Work/AbstractDictionary` isolates the correct pair (`GaschutzProP2Value`,
`ResidualTwoFinitenessPresentations`) and proves that they give the dictionary
(`gaschutzCohomologicalValue_of_inputs`); this module performs the same assembly for the
**unramified** group `G_∅` of `Kc`, where the generator count `d(G_∅) = 5` is the chapter's item (1)
(`exists_generatingSet_card_five_Kc`) and the dense generating family comes from it.

## Main declarations

* `proP2PresentationData_of_contH2DimLe_closed` -- the two named inputs and the cohomological bound
  produce a five-generator, six-relator presentation of `G_∅`;
* `relatorRankLe_six_galoisGroup_of_contH2DimLe_closed`,
  `hasProTwoPresentation_six_of_contH2DimLe_closed` -- the two resulting forms;
* `kcProTwoPresentationInput_of_contH2DimLe_closed` (per `M`) and
  `kcProTwoPresentationInput_of_kochCohomologyBound_closed` (the `∀ M`/`∃ M` form) -- **the crux**;
* `infiniteProTwoExtension_Kc_of_kochCohomologyBound_closed`,
  `unramifiedPro2TowerWall_of_kochCohomologyBound_closed`,
  `boundedRdTowerWall_of_kochCohomologyBound_closed` -- the walls;
* `kochCohomologyBound_of_kcProTwoPresentationInput_closed` -- the converse (the easy half of the
  closed value theorem), so in this normalisation the crux *is* the arithmetic bound;
* `hasProTwoPresentation_six_of_closedRelators` -- the minimal, most elementary form of the
  group-theoretic input: a dense five-family, a relator set of at most six elements satisfying the
  *closed* condition, and residual `2`-finiteness of the group it presents.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## The closed Gaschütz dictionary

The two named inputs are those of the sibling area `Submission/Work/AbstractDictionary`: the closed
value theorem `GaschutzProP2Value` and the residual seam `ResidualTwoFinitenessPresentations`. -/

/-- **A five-generator, six-relator pro-`2` presentation of `G_∅`**, from the two named classical
inputs of the sibling area `Submission/Work/AbstractDictionary` and the arithmetic bound
`dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`.

The dense generating five-family is the chapter's item (1) (`exists_generatingSet_card_five_Kc`); the
closed value theorem produces the relators; the residual seam converts the closed normal closure into
the abstract one (`Work.AbstractDictionary.ker_eq_normalClosure_of_residualTwoFiniteness`). -/
theorem proP2PresentationData_of_contH2DimLe_closed
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hvalue : ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
      Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    Nonempty (Work.RelatorRank.ProP2PresentationData (galoisGroup M) 5 6) := by
  obtain ⟨S, hcard, htop⟩ := exists_generatingSet_card_five_Kc_aux M
  have hgen : Work.RelatorRank.HasDenseGeneratingFamily (galoisGroup M) 5 :=
    hcard ▸ hasDenseGeneratingFamily_of_finset htop
  obtain ⟨gen, hdense⟩ := hgen
  obtain ⟨T, hTcard, hTkill, hTclosed⟩ := (hvalue gen hdense).exists_closedRelators hcont
  have hker : MonoidHom.ker (FreeGroup.lift gen) =
      Subgroup.normalClosure (T : Set (FreeGroup (Fin 5))) :=
    Work.AbstractDictionary.ker_eq_normalClosure_of_residualTwoFiniteness hres hdense hTkill hTclosed
  exact ⟨{ gen := gen, rel := T, dense := hdense, card_le := hTcard, ker_eq := hker }⟩

/-- **The relation-rank bound `RelatorRankLe (G_∅) 6`** from the two named inputs of the closed
dictionary and the arithmetic bound. -/
theorem relatorRankLe_six_galoisGroup_of_contH2DimLe_closed
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hvalue : ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
      Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    Work.RelatorRank.RelatorRankLe (galoisGroup M) 6 := by
  rw [Work.RelatorRank.relatorRankLe_iff, generatorRank_galoisGroup_Kc M]
  exact proP2PresentationData_of_contH2DimLe_closed M hvalue hres hcont

/-- **The chapter's presentation interface** `HasProTwoPresentation Kc 5 6`, from the two named
classical inputs of the closed dictionary and the arithmetic bound. -/
theorem hasProTwoPresentation_six_of_contH2DimLe_closed
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hvalue : ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
      Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    HasProTwoPresentation Kc 5 6 :=
  hasProTwoPresentation_of_relatorRankLe_six M
    (relatorRankLe_six_galoisGroup_of_contH2DimLe_closed M hvalue hres hcont)

/-- **THE CRUX, per maximal unramified pro-`2` extension `M`**, from the two named classical inputs
of the closed dictionary and the arithmetic bound `dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`. -/
theorem kcProTwoPresentationInput_of_contH2DimLe_closed
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hvalue : ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
      Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_five_six
    (hasProTwoPresentation_six_of_contH2DimLe_closed M hvalue hres hcont)

/-! ## The `∀ M`/`∃ M` forms and the walls -/

/-- **THE CRUX** from the `∀ M` forms of the two named group-theoretic inputs and the arithmetic
bound in its `∃ M` form (`KcKochCohomologyBound`). -/
theorem kcProTwoPresentationInput_of_kochCohomologyBound_closed
    (hvalue : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (h : KcKochCohomologyBound) : KcProTwoPresentationInput := by
  obtain ⟨M, hM⟩ := h
  exact kcProTwoPresentationInput_of_contH2DimLe_closed M (hvalue M) (hres M) hM

/-- **`InfiniteProTwoExtension Kc`** (the deliverable's conclusion) from the two named classical
inputs of the closed dictionary and the arithmetic bound. -/
theorem infiniteProTwoExtension_Kc_of_kochCohomologyBound_closed
    (hvalue : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (h : KcKochCohomologyBound) : Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_Kc_of_input
    (kcProTwoPresentationInput_of_kochCohomologyBound_closed hvalue hres h)

/-- **`Submission.NumberField.UnramifiedPro2TowerWall`** from the two named classical inputs of the
closed dictionary and the arithmetic bound. -/
theorem unramifiedPro2TowerWall_of_kochCohomologyBound_closed
    (hvalue : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (h : KcKochCohomologyBound) : Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_input
    (kcProTwoPresentationInput_of_kochCohomologyBound_closed hvalue hres h)

/-- **`Submission.NumberField.BoundedRdTowerWall`** (the benchmark's wall) from the two named
classical inputs of the closed dictionary and the arithmetic bound. -/
theorem boundedRdTowerWall_of_kochCohomologyBound_closed
    (hvalue : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (h : KcKochCohomologyBound) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input
    (kcProTwoPresentationInput_of_kochCohomologyBound_closed hvalue hres h)

/-! ## The converse: the crux implies the arithmetic bound, through the *easy* half -/

/-- **The easy half, in the chapter's setting.**  A presentation of `G_∅` on a dense five-family
with at most six relators (whose abstract normal closure is the relation kernel) gives
`dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`.

Only the `⟸`-half of `GaschutzProP2Value` is used, and no residual-finiteness input is needed: the
relators of an abstract presentation satisfy the closed condition for the trivial reason that their
abstract normal closure *is* the kernel.  Consequently the crux *implies*
`KcKochCohomologyBound`, so the arithmetic bound is not a weakening of it. -/
theorem kochCohomologyBound_of_kcProTwoPresentationInput_closed
    (hvalue : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (h : KcProTwoPresentationInput) : KcKochCohomologyBound := by
  obtain ⟨M, gen, w, hker, hdense⟩ := hasProTwoPresentation_six_of_input h
  refine ⟨M, (hvalue M gen hdense).contH2DimLe ⟨Finset.univ.image w, ?_, ?_, ?_⟩⟩
  · simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 6))) (f := w)
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  · intro Q _ _ hQ φ hφ
    rw [hker]
    refine Subgroup.normalClosure_le_normal fun s hs => MonoidHom.mem_ker.mpr ?_
    obtain ⟨i, rfl⟩ := hs
    exact hφ (w i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-! ## The minimal form of the group-theoretic input -/

/-- **The spelling bridge to the sibling chapter's closed condition.**  For a relator *family*
`w : Fin r → FreeGroup (Fin d)`, the sibling area's `ClosedNormalGeneratesTwo` for the finite set
`univ.image w` is exactly the statement that every finite `2`-group quotient of the free group
killing each `w i` kills the whole relation kernel -- i.e. the second conjunct of this chapter's
`Work.ShafarevichKoch.ClosedRelationData`, in the `Fin`-indexed spelling. -/
theorem closedNormalGeneratesTwo_image_iff {d r : ℕ} {G : Type*} [Group G]
    (gen : Fin d → G) (w : Fin r → FreeGroup (Fin d)) :
    Work.AbstractDictionary.ClosedNormalGeneratesTwo
        (MonoidHom.ker (FreeGroup.lift gen)) (Finset.univ.image w) ↔
      (∀ (Q : Type) [Group Q] [Fintype Q], IsPGroup 2 Q →
        ∀ φ : FreeGroup (Fin d) →* Q, (∀ i, φ (w i) = 1) →
          MonoidHom.ker (FreeGroup.lift gen) ≤ MonoidHom.ker φ) := by
  constructor
  · intro h Q _ _ hQ φ hφ
    exact h Q hQ φ (fun s hs => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
      exact hφ i)
  · intro h Q _ _ hQ φ hφ
    exact h Q hQ φ (fun i => hφ (w i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

/-- **The minimal form of the group-theoretic input.**  A dense generating five-family `gen` of
`G_∅`, a relator *family* `w` of at most six words that die in `G_∅` and whose *closed* normal
closure is the relation kernel (the second conjunct of `Work.ShafarevichKoch.ClosedRelationData`),
together with residual `2`-finiteness of the abstract group `FreeGroup (Fin 5) ⧸ ⟪w⟫` it presents,
give the presentation form of the crux.

The residual-finiteness hypothesis cannot be dropped (the `ℤ/6` of `Work.HopfGaschutz.Counterexample`
satisfies everything else), and it is exactly what
`Work.ShafarevichKoch.ker_eq_normalClosure_of_closed` consumes.  With the spelling bridge
`closedNormalGeneratesTwo_image_iff` this is the form in which the sibling area's
`Work.AbstractDictionary.GaschutzProP2Value` produces its output. -/
theorem hasProTwoPresentation_six_of_closedFamily
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    {gen : Fin 5 → galoisGroup M} (hdense : Work.RelatorRank.DenseGenerating gen)
    {r : ℕ} (hr : r ≤ 6) (w : Fin r → FreeGroup (Fin 5))
    (hkill : ∀ i, FreeGroup.lift gen (w i) = 1)
    (hclosed : ∀ (Q : Type) [Group Q] [Fintype Q], IsPGroup 2 Q →
      ∀ φ : FreeGroup (Fin 5) →* Q, (∀ i, φ (w i) = 1) →
        MonoidHom.ker (FreeGroup.lift gen) ≤ MonoidHom.ker φ)
    (hres : ResiduallyFiniteTwoGroup
      (FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (Set.range w))) :
    HasProTwoPresentation Kc 5 6 := by
  have hkill' : ∀ i, w i ∈ MonoidHom.ker (FreeGroup.lift gen) := fun i =>
    MonoidHom.mem_ker.mpr (hkill i)
  have hker := ker_eq_normalClosure_of_closed gen w hkill' hclosed hres
  have hdense' : (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤ := hdense
  exact hasProTwoPresentation_mono
    (hasProTwoPresentation_of_hasProP2Presentation M
      (hasProP2Presentation_of_relators M gen w hker hdense')) hr


/-! ## The seam-free route (the sibling area's route (b))

`Work.AbstractDictionary.GaschutzPresentationExists Γ` states the hard half of the value theorem
*in the abstract normalisation, for one suitable generating family*, and therefore needs no residual
`2`-finiteness side condition.  By §31.3 of the README the seam-based route is the fragile one (the
seam is machine-checked false at `Nat.card Γ = 2`,
`Work.ShafarevichKoch.not_residualTwoFinitenessPresentations_of_card_two`), so these are the
statements a future session should aim at. -/

/-- **The crux from the seam-free input.**  `GaschutzPresentationExists (G_∅)` (the sibling area's
route (b)) and the arithmetic bound `dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6` give the presentation form of the
crux. -/
theorem hasProTwoPresentation_six_of_gaschutzPresentationExists
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (h : Work.AbstractDictionary.GaschutzPresentationExists (galoisGroup M))
    (hcont : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    HasProTwoPresentation Kc 5 6 := by
  obtain ⟨gen, hdense, hpres⟩ := h
  obtain ⟨rel, hcard, hker⟩ := hpres 6 hcont
  exact hasProTwoPresentation_of_hasProP2Presentation M
    ⟨{ gen := gen, rel := rel, dense := hdense, card_le := hcard, ker_eq := hker }⟩

/-- **THE CRUX from the seam-free input** (`∀ M` form of `GaschutzPresentationExists`) and the
arithmetic bound in its `∃ M` form. -/
theorem kcProTwoPresentationInput_of_gaschutzPresentationExists
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (galoisGroup M))
    (h : KcKochCohomologyBound) : KcProTwoPresentationInput := by
  obtain ⟨M, hM⟩ := h
  exact kcProTwoPresentationInput_of_five_six
    (hasProTwoPresentation_six_of_gaschutzPresentationExists M (hpres M) hM)

/-- **The benchmark's wall** from the seam-free input and the arithmetic bound. -/
theorem boundedRdTowerWall_of_gaschutzPresentationExists
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (galoisGroup M))
    (h : KcKochCohomologyBound) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input
    (kcProTwoPresentationInput_of_gaschutzPresentationExists hpres h)

/-! ## The weakest form of the group-theoretic input

`Work.HopfGaschutz.ProPHopfCohomologicalInput 2 5 Γ gen` is the **hard half only** of the closed
Gaschütz value theorem, for **one** dense generating family: `dim_{𝔽₂} H²_cont(Γ,𝔽₂) ≤ r` produces
`r` relators that span the relation kernel modulo `K²[K,Γ]` at every finite `2`-quotient (the
transgression plus Nakayama for `𝔽₂[[Γ]]`).  The sibling area proves
`GaschutzProP2Value d gen ↔ ProPHopfCohomologicalInput … ∧ ProPHopfCohomologicalBound …`
(`Work.AbstractDictionary.gaschutzProP2Value_iff`), so using only `ProPHopfCohomologicalInput` is a
strictly weaker hypothesis than the `GaschutzProP2Value` of §31.0, and it is the weakest form of the
group-theoretic input this chapter needs. -/

/-- **The crux from the weakest group-theoretic input, per `M`.** -/
theorem hasProTwoPresentation_six_of_proPHopfCohomologicalInput
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    {gen : Fin 5 → galoisGroup M} (hdense : Work.RelatorRank.DenseGenerating gen)
    (h : Work.HopfGaschutz.ProPHopfCohomologicalInput 2 5 (galoisGroup M) gen)
    (hres : Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    HasProTwoPresentation Kc 5 6 := by
  obtain ⟨S, hScard, hkill, hclosed⟩ :=
    Work.HopfGaschutz.closedPresentation_of_contH2DimLe gen h hcont
  have hker : MonoidHom.ker (FreeGroup.lift gen) =
      Subgroup.normalClosure (S : Set (FreeGroup (Fin 5))) :=
    Work.AbstractDictionary.ker_eq_normalClosure_of_residualTwoFiniteness hres hdense hkill hclosed
  exact hasProTwoPresentation_of_hasProP2Presentation M
    ⟨{ gen := gen, rel := S, dense := hdense, card_le := hScard, ker_eq := hker }⟩

/-- **The crux from the weakest group-theoretic input**, `∃ M` form of the arithmetic bound and the
`∀ M` form of the two group-theoretic inputs. -/
theorem kcProTwoPresentationInput_of_proPHopfCohomologicalInput
    (h : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.HopfGaschutz.ProPHopfCohomologicalInput 2 5 (galoisGroup M) gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : KcKochCohomologyBound) : KcProTwoPresentationInput := by
  obtain ⟨M, hM⟩ := hcont
  obtain ⟨S, hcard, htop⟩ := exists_generatingSet_card_five_Kc_aux M
  have hgen : Work.RelatorRank.HasDenseGeneratingFamily (galoisGroup M) 5 :=
    hcard ▸ hasDenseGeneratingFamily_of_finset htop
  obtain ⟨gen, hdense⟩ := hgen
  exact kcProTwoPresentationInput_of_five_six
    (hasProTwoPresentation_six_of_proPHopfCohomologicalInput M hdense
      (h M gen hdense) (hres M) hM)

/-- **The benchmark's wall** from the weakest group-theoretic input and the arithmetic bound. -/
theorem boundedRdTowerWall_of_proPHopfCohomologicalInput
    (h : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.HopfGaschutz.ProPHopfCohomologicalInput 2 5 (galoisGroup M) gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (hcont : KcKochCohomologyBound) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input
    (kcProTwoPresentationInput_of_proPHopfCohomologicalInput h hres hcont)

/-! ## The fragility of the closed condition under cubing a relator -/

/-- **Cubing a relator preserves the closed condition.**

If `S` is a closed relator set for the relation kernel `K` and `r ∈ S`, then so is
`S.erase r ∪ {r ^ 3}`, with the same cardinality.  The reason is that a finite `2`-group has no
element of order `3`: a quotient `φ` with `φ r ^ 3 = 1` already has `φ r = 1`, hence kills `S`.

This is the elementary mechanism behind the warning of README §31.3: the *closed* condition cannot
distinguish `r` from `r ^ 3`, while the *abstract* normal closure `⟪r ^ 3⟫` can be strictly smaller
than `⟪r⟫` (for `FreeGroup (Fin 1) = ℤ` and `r = x²`: `6ℤ ⊊ 2ℤ`).  Hence a closed datum can always
be "cubed" into one with a smaller abstract closure, so the seam statement
`Work.AbstractDictionary.ResidualTwoFinitenessPresentations` is a genuinely strong side
condition. -/
theorem closedNormalGeneratesTwo_cube_relator {α : Type} [Fintype α]
    {K : Subgroup (FreeGroup α)} {S : Finset (FreeGroup α)}
    (h : Work.AbstractDictionary.ClosedNormalGeneratesTwo K S) {r : FreeGroup α} (hr : r ∈ S) :
    Work.AbstractDictionary.ClosedNormalGeneratesTwo K (S.erase r ∪ {r ^ 3}) := by
  intro Q _ _ hQ φ hφ
  refine h Q hQ φ ?_
  intro s hs
  rcases eq_or_ne s r with hsr | hne
  · rw [hsr]
    have h3 : φ (r ^ 3) = 1 := hφ _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rw [map_pow] at h3
    obtain ⟨n, hn⟩ := hQ (φ r)
    have hdiv2 : orderOf (φ r) ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
    have hdiv3 : orderOf (φ r) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
    have h3not : ¬ (3 ∣ orderOf (φ r)) := by
      intro hdd
      have h' : 3 ∣ 2 ^ n := dvd_trans hdd hdiv2
      have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) h'
      omega
    rcases Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3) (orderOf (φ r)) hdiv3 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (by rw [h1]) h3not
  · exact hφ s (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hs⟩))

/-! ## The deliverable's item (3) -/

/-- **Item (3) of the deliverable** in the closed-dictionary normalisation:
`Work.ClassFieldTower.ProTwoShafarevichKochInput Kc` from the three named inputs (G'), (G''), (U) of
README §31.0 together with the realization clause `RealizationClauseKc` (which is *independent* of
the relation bound, §28; note that the two *walls* do not need it: see
`unramifiedPro2TowerWall_of_kochCohomologyBound_closed` and
`boundedRdTowerWall_of_kochCohomologyBound_closed`). -/
theorem proTwoShafarevichKochInput_Kc_of_kochCohomologyBound_closed
    (hvalue : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      ∀ gen : Fin 5 → galoisGroup M, Work.RelatorRank.DenseGenerating gen →
        Work.AbstractDictionary.GaschutzProP2Value 5 gen)
    (hres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := galoisGroup M))
    (h : KcKochCohomologyBound) (hreal : RealizationClauseKc) :
    ProTwoShafarevichKochInput Kc :=
  proTwoShafarevichKochInput_Kc_of_input_and_realization
    (kcProTwoPresentationInput_of_kochCohomologyBound_closed hvalue hres h) hreal

end Work.ShafarevichKoch


