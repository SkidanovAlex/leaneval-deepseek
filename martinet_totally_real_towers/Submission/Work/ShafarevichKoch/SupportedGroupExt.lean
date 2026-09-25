import Mathlib
import Submission.Work.ConCohomology.Extension
import Submission.Work.ShafarevichKoch.SupportedComparison
import Submission.Work.ShafarevichKoch.kEmptyMaximalProP

/-!
# `Work.ShafarevichKoch.SupportedGroupExt` -- `1 → H_S → G_S → G_∅ → 1` as a `GroupExt`

`SupportedComparison.lean` produces the surjection `restrictToEmpty F p S : G_S →* G_∅` with
kernel `H_S = HSupported F p S`; `kEmptyMaximalProP.lean` makes `G_∅` the concrete group
`Gal(k_∅/F) = galoisGroup (kEmptyMaximalProP F)` by `rfl`.  This module packages the two into the
`Work.ConCohomology.GroupExt` object consumed by the Hochschild--Serre machinery
(`Work.ConCohomology.ker_H2Res_eq_range_tg`, `Work.ConCohomology.H2Res`,
`Work.ShafarevichKoch.natCard_ker_H2Res_le_two_pow_of_continuousSection`):

```lean
Work.ShafarevichKoch.groupExtHSupported F p S :
  Work.ConCohomology.GroupExt (↥(k_S) ≃ₐ[F] ↥(k_S))
    (↥(k_∅) ≃ₐ[F] ↥(k_∅)) (HSupported F p S)
```

The codomain is written in the *tower* spelling `↥(k_∅) ≃ₐ[F] ↥(k_∅)`; its carrier is the same
expression as `Work.ClassFieldTower.galoisGroup (kEmptyMaximalProP F)` **by `rfl`**
(`kEmptyMaximalProP_K`), but the two `Group` instances are synthesized from different expressions
and are therefore *not* defeq, so a consumer who wants the `galoisGroup` spelling must transport
along the `rfl` equality of carriers explicitly.

with `q = restrictToEmpty F p S` and `i = (HSupported F p S).subtype`.  The carrier of the middle
group and the two topology/coefficient instances are the canonical ones, so any counting statement
about this `GroupExt` is a statement about the chapter's own `G_∅`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- The group extension `1 → H_S → Gal(k_S/F) → G_∅ → 1`, with `G_∅` the concrete Galois group of
`k_∅ = kSupported F 2 ∅`. -/
def groupExtHSupported (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) :
    Work.ConCohomology.GroupExt (↥(kSupported F p S) ≃ₐ[F] ↥(kSupported F p S))
      (↥(kSupported F p (∅ : Finset ℕ)) ≃ₐ[F] ↥(kSupported F p (∅ : Finset ℕ)))
      (HSupported F p S) where
  q := restrictToEmpty F p S
  i := (HSupported F p S).subtype
  ker_eq := fun g => ⟨fun h => ⟨⟨g, h⟩, rfl⟩,
    by rintro ⟨n, rfl⟩; exact n.2⟩
  injective_i := Subtype.coe_injective

/-- The projection of `groupExtHSupported` is the restriction map, by `rfl`. -/
theorem groupExtHSupported_q (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : (groupExtHSupported F p S).q = restrictToEmpty F p S := rfl

/-- The projection of `groupExtHSupported` is surjective (so `G_∅` is a quotient of `G_S`). -/
theorem groupExtHSupported_q_surjective (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] (S : Finset ℕ) :
    Function.Surjective (groupExtHSupported F p S).q :=
  restrictToEmpty_surjective F p S

end Work.ShafarevichKoch
