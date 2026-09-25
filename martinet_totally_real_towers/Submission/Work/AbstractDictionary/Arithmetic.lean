import Mathlib
import Submission.Work.AbstractDictionary.Main
import Submission.Work.AbstractDictionary.residualTwoFinitenessPresentations_iff_kernelEquality
import Submission.Work.AbstractDictionary.gaschutzProP2Value_iff

/-!
# `Work.AbstractDictionary` -- the seam in the arithmetic normalisation

**Namespace** `Work.AbstractDictionary`; module `Submission.Work.AbstractDictionary.Arithmetic`.

`Work.AbstractDictionary.Main` reduces the dictionary
`Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K)` of a maximal tame pro-`2` extension to the
closed Gaschütz value theorem plus the residual `2`-finiteness side condition
`ResidualTwoFinitenessPresentations`.  This file records the second, equivalent, face of that side
condition, obtained from
`Work.AbstractDictionary.residualTwoFinitenessPresentations_iff_kernelEquality`
(`Submission/Work/AbstractDictionary/residualTwoFinitenessPresentations_iff_kernelEquality.lean`)
together with the *proved* residual `2`-finiteness of `Γ = Gal(K/ℚ)`
(`Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame`):

> for `K` maximal tame pro-`2`, `ResidualTwoFinitenessPresentations Γ` is *equivalent* to

> `∀ gen S, DenseGenerating gen → (∀ s ∈ S, lift gen s = 1) →`
> `  ClosedNormalGeneratesTwo (ker (FreeGroup.lift gen)) S → ker (FreeGroup.lift gen) = ⟪S⟫`,

i.e. to the statement that **the closed (pro-`2`) relation condition already determines the abstract
relation kernel**.  So the side condition of the dictionary is precisely the closed ⟹ abstract seam
and nothing else: a caller who prefers to assume the seam directly can use
`gaschutzCohomologicalValue_of_closedValue_and_kernelEquality`.

The two sides of the equivalence are *not* vacuous: for `Γ = ℤ/2` (which is not a maximal tame
pro-`2` Galois group, but is an honest pro-`2` group) both fail, with `gen` the generator and
`S = {x⁶}` -- the closed condition holds while `⟪x⁶⟫ = 6ℤ ⊊ 2ℤ = ker`
(`Work.HopfGaschutz.Counterexample`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.AbstractDictionary

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

/-- **The seam in the arithmetic normalisation.**  For `K` a maximal tame pro-`2` extension of `ℚ`,
the residual `2`-finiteness side condition of the dictionary is *equivalent* to the statement that
the closed relation condition on a relator set determines the abstract relation kernel.

The `⟸`-direction is the content (`⟹` is
`Work.AbstractDictionary.ker_eq_normalClosure_of_residualTwoFiniteness`); the equivalence rests on
the residual `2`-finiteness of `Γ = Gal(K/ℚ)`, which is a theorem of
`Work.TameArithmetic` (`residuallyFiniteTwoGroup_galoisGroup_tame`), *not* an extra input. -/
theorem residualTwoFiniteness_iff_kernelEquality_of_isMaximalTamePro2
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K) :
    ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K) ↔
      (∀ (d : ℕ) (gen : Fin d → (K ≃ₐ[ℚ] K)) (S : Finset (FreeGroup (Fin d))),
        Work.RelatorRank.DenseGenerating gen →
        (∀ s ∈ S, FreeGroup.lift gen s = 1) →
        ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S →
        MonoidHom.ker (FreeGroup.lift gen) =
          Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))) :=
  residualTwoFinitenessPresentations_iff_kernelEquality (residuallyFiniteTwoGroup_galoisGroup hK)

/-- **The dictionary from the closed value theorem plus the seam, in kernel-equality form.**

Same statement as `Work.AbstractDictionary.gaschutzCohomologicalValue_of_inputs`, with the side
condition `ResidualTwoFinitenessPresentations` replaced by its equivalent kernel-equality form
(`residualTwoFiniteness_iff_kernelEquality_of_isMaximalTamePro2`). -/
theorem gaschutzCohomologicalValue_of_closedValue_and_kernelEquality
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hvalue : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen)
    (hker : ∀ (d : ℕ) (gen : Fin d → (K ≃ₐ[ℚ] K)) (S : Finset (FreeGroup (Fin d))),
      Work.RelatorRank.DenseGenerating gen →
      (∀ s ∈ S, FreeGroup.lift gen s = 1) →
      ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S →
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  gaschutzCohomologicalValue_of_inputs hK hvalue
    ((residualTwoFiniteness_iff_kernelEquality_of_isMaximalTamePro2 hK).mpr hker)

/-- **The assembled upgrade**: a *closed* presentation of `Γ = Gal(K/ℚ)` on a dense generating
family with `|S|` relators, together with the residual finiteness side condition, is a presentation
in the workspace's sense, i.e. gives `RelatorRankLe Γ S.card`.

This is the explicit form of the `⟸`-direction of the dictionary, made independent of how the
closed presentation was produced: it can be fed by the arithmetic Shafarevich--Koch input, by the
closed Gaschütz value theorem, or by any other source of a closed presentation. -/
theorem relatorRankLe_of_closedRelators (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hres : ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K))
    {gen : Fin 5 → (K ≃ₐ[ℚ] K)} (hgen : Work.RelatorRank.DenseGenerating gen)
    {S : Finset (FreeGroup (Fin 5))} (hS : ∀ s ∈ S, FreeGroup.lift gen s = 1)
    (hclosed : ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S) :
    Work.RelatorRank.RelatorRankLe (K ≃ₐ[ℚ] K) S.card := by
  have hker : MonoidHom.ker (FreeGroup.lift gen) =
      Subgroup.normalClosure (S : Set (FreeGroup (Fin 5))) :=
    ker_eq_normalClosure_of_residualTwoFiniteness hres hgen hS hclosed
  refine (relatorRankLe_iff_hasProP2Presentation_five hK S.card).mpr ⟨gen, S, hgen, le_rfl, hker⟩

/-- **The `⟸`-direction of the dictionary in the form of the assembled upgrade**: the closed
Gaschütz value theorem produces, from `ContH2DimLe Γ r`, the relator set that
`relatorRankLe_of_closedRelators` consumes. -/
theorem relatorRankLe_of_contH2DimLe' (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hvalue : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      GaschutzProP2Value 5 gen)
    (hres : ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K))
    (r : ℕ) (h : Work.RelatorRank.ContH2DimLe (K ≃ₐ[ℚ] K) r) :
    Work.RelatorRank.RelatorRankLe (K ≃ₐ[ℚ] K) r := by
  obtain ⟨gen, hgen⟩ := Work.TameArithmetic.dense_generatingFamily_of_isMaximalTamePro2 K hK
  obtain ⟨S, hS, hkill, hclosed⟩ := (hvalue gen hgen).exists_closedRelators h
  exact (relatorRankLe_of_closedRelators hK hres hgen hkill hclosed).mono hS

/-- **The dictionary from the workspace's existing named input, its missing half, and the seam.**

This is the shape requested of this area, with the two named inputs spelled out: the classical
input of `Work.HopfGaschutz.ProPHopfCohomologicalInput` (in the *closed* normalisation), the
missing half `ProPHopfCohomologicalBound`, and the residual finiteness side condition — the latter
being the closed ⟹ abstract seam of §3 of `README.md`.  The two halves together are equivalent to
`GaschutzProP2Value` (`Work.AbstractDictionary.gaschutzProP2Value_iff`), and `GaschutzProP2Value`
alone is *not* enough for the `⟹`-direction of the dictionary: the bound half is what converts a
presentation into a cohomological bound. -/
theorem gaschutzCohomologicalValue_of_proPHopfInput_and_bound_and_residual
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hinput : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      Work.HopfGaschutz.ProPHopfCohomologicalInput.{0, 0} 2 5 (K ≃ₐ[ℚ] K) gen)
    (hbound : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      ProPHopfCohomologicalBound 5 gen)
    (hres : ResidualTwoFinitenessPresentations (Γ := K ≃ₐ[ℚ] K)) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  gaschutzCohomologicalValue_of_inputs hK
    (fun gen hgen =>
      (gaschutzProP2Value_iff (Γ := K ≃ₐ[ℚ] K) gen).mpr ⟨hinput gen hgen, hbound gen hgen⟩)
    hres

end Work.AbstractDictionary
