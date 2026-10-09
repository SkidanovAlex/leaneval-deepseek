import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps_extends
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The new places of an enlarged representative set are outside `cs(S)`

First step of (a'), the datum-specific orthogonality at the enlarged place set.

Let `T` be a level-`K` representative set of `cs(S)` (clause 4 below is the covering clause, and
`T⁺` its extension to a representative set of `cs(S⁺)`, with `T⁺` `KConj`-nonsingular).  A place
`A ∈ T⁺∖T` is **not** `k`-conjugate into `S`: if it were, the covering clause of `T` would produce
`t ∈ T` with `KConj K t A`, and the `KConj`-nonsingularity of `T⁺` (applied to the two elements
`t, A ∈ T⁺`) would give `t = A`, contradicting `A ∉ T`.

This is exactly what makes `auxDatum K S ν` vanish at the new places, hence the extra summands of the
reciprocity sum at `T⁺∖T` vanish (`pair_zero_left`).
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

/-- A place of `T⁺∖T` is not `k`-conjugate into `S`.  See the module docstring. -/
theorem not_exists_isConjPlace_of_mem_sdiff {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] {S T Te : Finset (ValuationSubring Ω)}
    (hTcov : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ T, KConj K A' B)
    (hTeT : ∀ A ∈ T, A ∈ Te)
    (hTedisj : ∀ A ∈ Te, ∀ B ∈ Te, KConj K A B → A = B)
    {A : ValuationSubring Ω} (hA : A ∈ Te) (hAnT : A ∉ T) :
    ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A := by
  rintro ⟨A', hA', hc⟩
  obtain ⟨t, ht, htA⟩ := hTcov A ⟨A', hA', hc⟩
  have htTe : t ∈ Te := hTeT t ht
  have hEq : t = A := hTedisj t htTe A hA htA
  exact hAnT (hEq ▸ ht)

end Work.SSGRoute
