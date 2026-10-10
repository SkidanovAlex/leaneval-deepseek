import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Extending a level-`K` representative set along an enlargement of the place set

`Work.SSGRoute.ZConstruction.exists_KConj_reps` produces, for a finite set `S` of finite places, a set
`T` containing one representative per level-`K` (`KConj`-)class of `cs(S)`.

This file proves the *extension* statement used by the section-4 level step: if `Se` is an enlargement
of `S` whose `k`-classes contain those of `S`, and `T` is a representative set of `cs(S)`, then there
is a representative set `Te ⊇ T` of `cs(Se)`.  The representatives of `T` are kept (each of them is
already `k`-conjugate into `S`, hence into `Se`), and one representative is added for each further
level-`K`-class of `cs(Se)`.

The construction is the one used in `Work.SSGRoute.auxExists_of_pairing_and_realisation`, where the
enlarged place set is `S' = S ∪ Ram(N|k)`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false

/-- **A level-`K` representative set of `cs(S)` extends to one of `cs(Se)`.**  See the module
docstring. -/
theorem exists_KConj_reps_extends {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {S Se : Finset (ValuationSubring Ω)} (hSefin : ∀ A ∈ Se, SSGRoute.IsFinPlace k A)
    (hSSe : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ Se, SSGRoute.IsConjPlace k A' B)
    {T : Finset (ValuationSubring Ω)}
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B)
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hTcov : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ T, KConj K A' B) :
    ∃ Te : Finset (ValuationSubring Ω), (∀ A ∈ T, A ∈ Te) ∧
      (∀ A ∈ Te, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ Te, ∀ B ∈ Te, KConj K A B → A = B) ∧
      (∀ A ∈ Te, ∃ A' ∈ Se, SSGRoute.IsConjPlace k A' A) ∧
      (∀ B : ValuationSubring Ω, (∃ A ∈ Se, SSGRoute.IsConjPlace k A B) →
        ∃ A' ∈ Te, KConj K A' B) := by
  classical
  obtain ⟨T₀, hT₀fin, hT₀disj, hT₀conj, hT₀cov⟩ := exists_KConj_reps K Se hSefin
  refine ⟨T ∪ T₀.filter (fun A => ¬ ∃ t ∈ T, KConj K t A), ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    exact Finset.mem_union_left _ hA
  · intro A hA
    rw [Finset.mem_union] at hA
    rcases hA with hA | hA
    · exact hTfin A hA
    · exact hT₀fin A (Finset.mem_filter.mp hA).1
  · intro A hA B hB hAB
    rw [Finset.mem_union] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hTdisj A hA B hB hAB
    · exact absurd ⟨A, hA, hAB⟩ (Finset.mem_filter.mp hB).2
    · exact absurd ⟨B, hB, kConj_symm hAB⟩ (Finset.mem_filter.mp hA).2
    · exact hT₀disj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hAB
  · intro A hA
    rw [Finset.mem_union] at hA
    rcases hA with hA | hA
    · obtain ⟨A'', hA'', hc⟩ := hTconj A hA
      obtain ⟨A''', hA''', hc'⟩ := hSSe A ⟨A'', hA'', hc⟩
      exact ⟨A''', hA''', hc'⟩
    · exact hT₀conj A (Finset.mem_filter.mp hA).1
  · intro B hB
    obtain ⟨A₀, hA₀, hc⟩ := hT₀cov B hB
    by_cases hnew : ∃ t ∈ T, KConj K t A₀
    · obtain ⟨t, ht, htA⟩ := hnew
      exact ⟨t, Finset.mem_union_left _ ht, kConj_trans htA hc⟩
    · exact ⟨A₀, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA₀, hnew⟩), hc⟩

end Work.SSGRoute.ZConstruction
