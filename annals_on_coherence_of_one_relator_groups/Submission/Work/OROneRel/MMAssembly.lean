/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Assembling the Magnus--Moldavanskii hierarchy from its one-step form

`HasMMStepData r` records a single Magnus--Moldavanskii decomposition of `⟨α | r⟩`: a strictly shorter
relator `r'` over a generating type `β` -- terminal, or again cyclically reduced and nontrivial, so
that the induction on `relatorNorm` applies -- Magnus subgroups `A`, `B` of `⟨β | r'⟩` and an
isomorphism between them exhibiting `⟨α | r⟩` as an HNN extension of `⟨β | r'⟩`.

`magnusMoldavanskiiAt_of_stepData` shows that `magnus_moldavanskii_at` follows once one step is
available at every cyclically reduced non-terminal relator.  This file is `sorry`-free: it can be
imported by lemma requests without depending on the unproved hierarchy statement.
-/

import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.OROneRel

universe u

/-- The one-step data of a Magnus--Moldavanskii decomposition of `⟨α | r⟩`: a strictly shorter
relator `r'` over a generating type `β` -- terminal, or again cyclically reduced and nontrivial, so
that the induction on `relatorNorm` applies -- Magnus subgroups `A`, `B` of `⟨β | r'⟩` and an
isomorphism between them making `⟨α | r⟩` an HNN extension of `⟨β | r'⟩`. -/
def HasMMStepData {α : Type u} (r : FreeGroup α) : Prop :=
  ∃ (β : Type u) (r' : FreeGroup β), relatorNorm r' < relatorNorm r ∧
    (IsTerminalRelator r' ∨ (IsCyclicallyReducedRelator r' ∧ r' ≠ 1)) ∧
    ∃ (A B : Subgroup (PresentedGroup ({r'} : Set (FreeGroup β)))),
      IsMagnusSubgroup A ∧ IsMagnusSubgroup B ∧ ∃ (φ : A ≃* B),
        Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({r'} : Set (FreeGroup β))) A B φ)

/-- One step of the decomposition, together with a hierarchy for the (strictly shorter) level, gives
a hierarchy for `r`: this is the `HasMMHierarchy.step` constructor with its data unpacked. -/
theorem hasMMHierarchy_of_stepData {α : Type u} {r : FreeGroup α}
    (hr' : HasMMStepData r) (hsub : ∀ {β : Type u} (r' : FreeGroup β), relatorNorm r' < relatorNorm r →
      (IsTerminalRelator r' ∨ (IsCyclicallyReducedRelator r' ∧ r' ≠ 1)) →
      HasMMHierarchy β r') :
    HasMMHierarchy α r := by
  obtain ⟨β, r', hlt, hcase, A, B, hA, hB, φ, ⟨e⟩⟩ := hr'
  exact HasMMHierarchy.step r r' hlt (hsub r' hlt hcase) A B hA hB φ e

/-- **Assembly of the Magnus--Moldavanskii hierarchy from its one-step form.**  If every cyclically
reduced nontrivial non-terminal relator admits a Magnus--Moldavanskii decomposition step over a
strictly shorter relator (which is either terminal, or again cyclically reduced and nontrivial), then
`magnus_moldavanskii_at` holds. -/
theorem magnusMoldavanskiiAt_of_stepData
    (hstep : ∀ {α : Type u} (r : FreeGroup α), IsCyclicallyReducedRelator r → r ≠ 1 →
      ¬ IsTerminalRelator r → HasMMStepData r) :
    ∀ {α : Type u} (r : FreeGroup α), MagnusMoldavanskiiAt r := by
  intro α
  suffices main : ∀ n, ∀ {α : Type u} (r : FreeGroup α), relatorNorm r = n →
      IsCyclicallyReducedRelator r → r ≠ 1 → HasMMHierarchy α r by
    intro r hr h1
    exact main (relatorNorm r) r rfl hr h1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α r hn hr h1
    by_cases hterm : IsTerminalRelator r
    · exact HasMMHierarchy.base r hterm
    · obtain ⟨β, r', hlt, hcase, hdata⟩ := hstep r hr h1 hterm
      refine hasMMHierarchy_of_stepData ⟨β, r', hlt, hcase, hdata⟩ (fun {β} r' hlt' hcase' => ?_)
      rcases hcase' with ht | ⟨hcr, hne⟩
      · exact HasMMHierarchy.base r' ht
      · exact ih (relatorNorm r') (by simpa [hn] using hlt') r' rfl hcr hne

end Work.OROneRel
