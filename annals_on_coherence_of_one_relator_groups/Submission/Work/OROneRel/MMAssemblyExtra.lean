/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

Two further pieces of the assembly of `magnus_moldavanskii_at`:

* `isTerminalRelator_of_relatorNorm_le_one` : a relator of norm at most one is terminal, i.e. the
  base case of a Magnus--Moldavanskii hierarchy (this is what turns `¬ IsTerminalRelator r` into
  `2 ≤ relatorNorm r` for a relator `r ≠ 1`);
* `magnusMoldavanskiiAt_of_pieces` : the final assembly, combining the two cases of the one-step
  theorem (exponent sum zero, resp. no exponent sum zero in the letters of `r`) with the
  Freiheitssatz hypothesis, into the statement `magnus_moldavanskii_at`.
-/

import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MMAssembly

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A relator of norm at most one is terminal (`1`, a generator, or the inverse of a generator). -/
theorem isTerminalRelator_of_relatorNorm_le_one {r : FreeGroup α} (h : relatorNorm r ≤ 1) :
    IsTerminalRelator r := by
  classical
  have hlen : r.toWord.length ≤ 1 := h
  rcases lt_or_eq_of_le hlen with hlt | heq
  · refine Or.inl (FreeGroup.toWord_eq_nil_iff.mp (List.length_eq_zero_iff.mp ?_))
    omega
  · obtain ⟨p, hsingle⟩ := List.length_eq_one_iff.mp heq
    rw [← FreeGroup.mk_toWord (x := r), hsingle]
    obtain ⟨a, b⟩ := p
    cases b
    · refine Or.inr ⟨a, -1, by norm_num, ?_⟩
      rw [zpow_neg_one, show FreeGroup.of a = FreeGroup.mk [(a, true)] from rfl, FreeGroup.inv_mk]
      rfl
    · exact Or.inr ⟨a, 1, by norm_num, by rw [zpow_one]; rfl⟩

/-- **Final assembly.**  Assume the Freiheitssatz, and assume the one-step theorem
`HasMMStepData` in both cases: when some letter of the relator has exponent sum zero, and when no
letter of the relator has exponent sum zero (the relator being cyclically reduced, nontrivial and
non-terminal).  Then `magnus_moldavanskii_at` holds. -/
theorem magnusMoldavanskiiAt_of_pieces
    (hF : ∀ {γ : Type u} (s : FreeGroup γ), FreiheitssatzAt s)
    (hzero : ∀ {γ : Type u} (s : FreeGroup γ) (t : γ), IsCyclicallyReducedRelator s → s ≠ 1 →
      t ∈ relatorLetters s → eps t s = 0 → HasMMStepData s)
    (hpos : ∀ {γ : Type u} (s : FreeGroup γ), IsCyclicallyReducedRelator s → s ≠ 1 →
      ¬ IsTerminalRelator s → (∀ t : γ, t ∈ relatorLetters s → eps t s ≠ 0) →
      HasMMStepData s) :
    ∀ {γ : Type u} (s : FreeGroup γ), MagnusMoldavanskiiAt s := by
  classical
  refine magnusMoldavanskiiAt_of_stepData (fun {γ} s hs h1 hnt => ?_)
  by_cases hex : ∃ t : γ, t ∈ relatorLetters s ∧ eps t s = 0
  · obtain ⟨t, ht, ht0⟩ := hex
    exact hzero s t hs h1 ht ht0
  · exact hpos s hs h1 hnt fun t ht h0 => hex ⟨t, ht, h0⟩

end Work.OROneRel
