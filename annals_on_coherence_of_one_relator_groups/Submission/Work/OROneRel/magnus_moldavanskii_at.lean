/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus--Moldavanskii hierarchy at a relator (`magnus_moldavanskii_at`)

The target statement is `MagnusMoldavanskiiAt r`, i.e. for a cyclically reduced `r ≠ 1` the one-relator
group `⟨α | r⟩` admits a Magnus--Moldavanskii hierarchy: a chain of HNN extensions

  `PresentedGroup {r} ≅ HNNExtension (PresentedGroup {r'}) A B φ`,  `relatorNorm r' < relatorNorm r`,

over Magnus subgroups `A`, `B` of the strictly shorter level, ending at a terminal relator
`1` or `of x ^ m` (`HasMMHierarchy`, `Submission.Work.OROneRel.Basic`).

## State of the proof

**Assembly (proved, `sorry`-free).**

* `Submission.Work.OROneRel.MMAssembly` -- `HasMMStepData r` (the one-step data), and
  `magnusMoldavanskiiAt_of_stepData`: the target follows from one step at every cyclically reduced
  nontrivial non-terminal relator, by strong induction on `relatorNorm`.
* `Submission.Work.OROneRel.MMAssemblyExtra` -- `isTerminalRelator_of_relatorNorm_le_one` (a relator of
  norm `≤ 1` is terminal) and `magnusMoldavanskiiAt_of_pieces`: the target follows from the two cases
  of the one-step theorem below plus the Freiheitssatz.

**The Magnus rewriting (proved, `sorry`-free).**

* `Submission.Work.OROneRel.MagnusRewrite` -- `wordEps`, `magRew` (delete the `t`-letters, decorate each
  remaining letter by the exponent sum of `t` in the prefix), `rho` (`(x,i) ↦ t^i x t^{-i}`), `eps`,
  `magnet` (the rewritten relator).
* `Submission.Work.OROneRel.rho_magRew` -- the telescoping identity
  `rho (mk (magRew t acc L)) = t^acc * mk L * t^(-(acc + wordEps t L))`.
* `Submission.Work.OROneRel.rho_magnet` -- consequently `rho (magnet r t) = r` when `eps t r = 0`.
* `Submission.Work.OROneRel.rho_injective` -- `rho t` is injective: the conjugates `t^i x t^{-i}`
  freely generate the kernel of the exponent-sum map.  Hence `F(β) ≅ ker σ_t` for `β = {x // x ≠ t} × ℤ`
  and the vertex group `PresentedGroup {magnet r t}` is the subgroup of `PresentedGroup {r}` generated
  by the classes of those conjugates.
* `Submission.Work.OROneRel.coprod_normalClosure` -- normal closures in a free factor (used to descend
  the index shift `φ` to finite index ranges).

**Remaining inputs.**

* `Submission.Work.OROneRel.mmStepData_of_expsum_zero` -- the exponent-sum-zero step: if `t` occurs in
  `r` with `eps t r = 0` then `HasMMStepData r` (given the Freiheitssatz).  The rewritten relator
  `magnet r t` has strictly smaller norm; the associated subgroups are the two letter-generated Magnus
  subgroups cut out by the index ranges used by the rewriting, identified by the index shift, and the
  isomorphism is the map induced by `t ↦ t`, `x ↦ (x,0)`.
* `Submission.Work.OROneRel.mmStepData_of_pos_expsums` -- the complementary case, in which no letter of
  `r` has exponent sum zero.  This is the genuinely hard (Masters / Linton) case: the reduction is by
  Nielsen ("Euclidean") transformations, and the strict decrease `relatorNorm r' < relatorNorm r` is
  the crux (the transformed relator may be longer than `r`).
* `Submission.Work.OROneRel.freiheitssatz_at` -- the Freiheitssatz (Magnus 1930), a sibling node; it
  supplies the freeness/injectivity of Magnus subgroups used by both steps.
-/

import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MMAssembly
import Submission.Work.OROneRel.MMAssemblyExtra
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.hasMMHierarchy_of_subst
import Submission.Work.OROneRel.two_letters_of_not_terminal

namespace Work.OROneRel

universe u

/-- **The strong induction underlying `magnus_moldavanskii_at`.**  For every bound `N` on the norm,
every cyclically reduced nontrivial relator of norm at most `N` admits a Magnus--Moldavanskii
hierarchy.  The two cases of the step are the exponent-sum-zero Magnus rewriting
(`mmStepData_of_expsum_zero`, giving an HNN `step`) and, when no letter has exponent sum zero,
Magnus's embedding `r ↪ ψ r` into a relator with a zero exponent sum and a strictly shorter Magnus
rewriting (`hasMMHierarchy_of_subst`, giving an `embed` step). -/
theorem magnusMoldavanskiiAt_of_norm_le (N : ℕ) :
    ∀ {α : Type u} (r : FreeGroup α), relatorNorm r ≤ N →
      IsCyclicallyReducedRelator r → r ≠ 1 → HasMMHierarchy α r := by
  classical
  induction N with
  | zero =>
      intro α r hN _hr hr1
      have hlen : (FreeGroup.toWord r).length = 0 := by
        simpa [relatorNorm, FreeGroup.norm] using hN
      exact absurd (FreeGroup.toWord_eq_nil_iff.mp (List.length_eq_zero_iff.mp hlen)) hr1
  | succ N ih =>
      intro α r hN hr hr1
      have ih' : ∀ {β : Type u} (s : FreeGroup β), relatorNorm s < relatorNorm r →
          (IsTerminalRelator s ∨ (IsCyclicallyReducedRelator s ∧ s ≠ 1)) →
          HasMMHierarchy β s := by
        intro β s hs hcase
        have hsN : relatorNorm s ≤ N := by omega
        rcases hcase with hterm | ⟨hcr, hne⟩
        · exact HasMMHierarchy.base s hterm
        · exact ih s hsN hcr hne
      by_cases hterm : IsTerminalRelator r
      · exact HasMMHierarchy.base r hterm
      · by_cases hz : ∃ t : α, t ∈ relatorLetters r ∧ eps t r = 0
        · obtain ⟨t, ht, h0⟩ := hz
          exact hasMMHierarchy_of_stepData
            (mmStepData_of_expsum_zero r t (fun {γ : Type u} (s : FreeGroup γ) =>
              freiheitssatz_at s) hr hr1 ht h0) ih'
        · have hσ : ∀ t : α, t ∈ relatorLetters r → eps t r ≠ 0 := by
            intro t ht
            by_contra h
            exact hz ⟨t, ht, h⟩
          obtain ⟨x, hx, y, hy, hxy⟩ := two_letters_of_not_terminal (u := r) hr hr1 hterm
          exact hasMMHierarchy_of_subst (t := y) (x := x) r hxy hr hy hx (hσ x hx) ih'

/-- The exponent-sum-zero case is now a theorem (`mmStepData_of_expsum_zero`), so
`magnus_moldavanskii_at` follows from the Freiheitssatz and from the complementary case in which no
letter of the relator has exponent sum zero. -/
theorem magnus_moldavanskii_at_of_pos_expsums
    (hF : ∀ {γ : Type u} (s : FreeGroup γ), FreiheitssatzAt s)
    (hpos : ∀ {γ : Type u} (s : FreeGroup γ), IsCyclicallyReducedRelator s → s ≠ 1 →
      ¬ IsTerminalRelator s → (∀ t : γ, t ∈ relatorLetters s → eps t s ≠ 0) →
      HasMMStepData s) :
    ∀ {γ : Type u} (s : FreeGroup γ), MagnusMoldavanskiiAt s :=
  magnusMoldavanskiiAt_of_pieces hF
    (fun s t hs h1 ht h => mmStepData_of_expsum_zero s t hF hs h1 ht h) hpos

/-- With the Freiheitssatz (`freiheitssatz_at`) available, `magnus_moldavanskii_at` follows from the
single remaining case: the one-step theorem for relators in which no letter has exponent sum zero. -/
theorem magnus_moldavanskii_at_of_general
    (hpos : ∀ {γ : Type u} (s : FreeGroup γ), IsCyclicallyReducedRelator s → s ≠ 1 →
      ¬ IsTerminalRelator s → (∀ t : γ, t ∈ relatorLetters s → eps t s ≠ 0) →
      HasMMStepData s) :
    ∀ {γ : Type u} (s : FreeGroup γ), MagnusMoldavanskiiAt s :=
  magnus_moldavanskii_at_of_pos_expsums (fun s => freiheitssatz_at s) hpos

theorem magnus_moldavanskii_at {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.MagnusMoldavanskiiAt r := by
  intro hr hr1
  exact magnusMoldavanskiiAt_of_norm_le (relatorNorm r) r le_rfl hr hr1

end Work.OROneRel
