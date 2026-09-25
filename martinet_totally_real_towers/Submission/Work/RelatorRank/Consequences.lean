import Submission.Work.RelatorRank.Galois
import Submission.Work.RelatorRank.Transfer.hasProP2Presentation_pad_generators
import Submission.Work.RelatorRank.Transfer.ker_lift_comp_mulEquiv
import Submission.Work.RelatorRank.Transfer.hasAbstractPresentation_of_mulEquiv
import Submission.Work.RelatorRank.GeneratorRank.hasDenseGeneratingFamily_of_continuous_surjective
import Submission.Work.RelatorRank.ProPFrattini.pFrattini_normal
import Submission.Work.RelatorRank.API.hasProP2Presentation_zero_iff
import Submission.Work.RelatorRank.API.hasDenseGeneratingFamily_zero_iff

/-!
# `Work.RelatorRank` -- consequences and the tuple-wise form of the missing input

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Consequences`.

This module collects the corollaries that need the delegated lemmas
(`HasProP2Presentation` padding, transport along isomorphisms, generator ranks under continuous
surjections) and states the *tuple-wise* form of the missing relation-rank invariance, which is
probably the most convenient shape for a future proof of the classical theorem
`r(Γ) = dim_{𝔽₂} H²(Γ, 𝔽₂)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

variable {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']

/-! ## The generator rank under continuous surjections -/

/-- **The generator rank does not increase under a continuous surjection.** -/
theorem generatorRank_le_of_continuous_surjective (f : Γ →* Γ') (hf : Continuous f)
    (hsurj : Function.Surjective f) (hex : ∃ d : ℕ, HasDenseGeneratingFamily Γ d) :
    GeneratorRank Γ' ≤ GeneratorRank Γ := by
  exact Nat.sInf_le (Work.RelatorRank.GeneratorRank.hasDenseGeneratingFamily_of_continuous_surjective
    f hf hsurj (hasDenseGeneratingFamily_generatorRank hex))

/-- `GeneratorRank Γ ≤ d` when there is a dense generating `d`-family. -/
theorem generatorRank_le_of_hasDenseGeneratingFamily' {d : ℕ}
    (h : HasDenseGeneratingFamily Γ d) : GeneratorRank Γ ≤ d :=
  generatorRank_le_of_hasDenseGeneratingFamily h

/-! ## Padding the generator count -/

/-- Padding a presentation with `k` extra generators (mapped to `1`) costs at most `k` relators. -/
theorem RelatorRankLe.mono_generators {r k : ℕ} (h : RelatorRankLe Γ r) :
    HasProP2Presentation Γ (GeneratorRank Γ + k) (r + k) :=
  Work.RelatorRank.Transfer.hasProP2Presentation_pad_generators h

/-! ## The missing input, tuple-wise -/

/-- **The missing relation-rank invariance, in the tuple-wise form.**  `RelationRankInvariant Γ d r`
is equivalent to: the *existence* of a presentation of `Γ` on `d` generators by at most `r` relators
is a property of `Γ` and `d` alone, independent of the dense generating family.

The direction `→` is the bridge; the direction `←` is the trivial half.  This is the shape in which
the classical theorem `r(Γ) = dim_{𝔽₂} H²(Γ, 𝔽₂)` should be formalised: it makes the minimal
number of relators a function of `(Γ, d)`. -/
theorem relationRankInvariant_iff_forall_dense_generating {d r : ℕ} :
    RelationRankInvariant Γ d r ↔
      (∀ gen gen' : Fin d → Γ, DenseGenerating gen → DenseGenerating gen' →
        ((∃ rel : Finset (FreeGroup (Fin d)), rel.card ≤ r ∧
          MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin d))))
        ↔
        (∃ rel' : Finset (FreeGroup (Fin d)), rel'.card ≤ r ∧
          MonoidHom.ker (FreeGroup.lift gen') = Subgroup.normalClosure (rel' : Set (FreeGroup (Fin d)))))) := by
  constructor
  · intro hinv gen gen' hgen hgen'
    constructor
    · rintro ⟨rel, hc, hk⟩
      exact hinv ⟨{ gen := gen, rel := rel, dense := hgen, card_le := hc, ker_eq := hk }⟩ gen' hgen'
    · rintro ⟨rel', hc, hk⟩
      exact hinv ⟨{ gen := gen', rel := rel', dense := hgen', card_le := hc, ker_eq := hk }⟩ gen hgen
  · intro hpair
    rw [RelationRankInvariant]
    rintro ⟨P⟩ gen' hgen'
    exact (hpair P.gen gen' P.dense hgen').mp ⟨P.rel, P.card_le, P.ker_eq⟩


end Work.RelatorRank
