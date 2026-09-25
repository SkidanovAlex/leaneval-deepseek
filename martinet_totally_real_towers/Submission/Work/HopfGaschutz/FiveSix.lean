import Submission.Work.HopfGaschutz.CohomologicalDictionary
import Submission.Work.HopfGaschutz.le_relFrattini_of_minimal_generating
import Submission.GroupTheory.GolodShafarevichFromCommons

/-!
# `Work.HopfGaschutz.FiveSix` -- the endgame consequence in the arithmetic language

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.FiveSix`.

The chapter's p-group-internal consequence (`Dictionary.lean`, `exists_relatorSet_five_six`) was
stated with the *presentation-theoretic* relation rank `h2DimOf`.  Here it is restated with the
bound in the language in which the arithmetic chapters produce it: the `𝔽₂`-dimension of the
continuous cohomology `H²(Q,𝔽₂) = Work.RelatorRank.contH2 Q`.

The conversion is
`CohomologicalDictionary.h2DimOf_eq_log_card_contH2` (the relation rank *is* `dim H²`, proved by the
transgression) together with `le_relFrattini_of_minimal_generating` (a minimal generating family of
a finite `p`-group has its relation kernel inside the Frattini subgroup, so that the transgression
computes the relation rank exactly).  Both of those are theorems of this chapter; the only remaining
input is `GaschutzDictionary 2` (the `p`-group efficiency statement, see `README.md` §3).

## What this buys a consumer

A chapter that has proved

```lean
h : Nat.log 2 (Nat.card (Work.RelatorRank.contH2 (K ≃ₐ[ℚ] K))) ≤ 6
```

for the maximal tame pro-`2` Galois group `Γ = K ≃ₐ[ℚ] K` (together with `d(Γ) = 5`, i.e. the
minimality `hmin` below) can invoke `exists_relatorSet_five_six_of_le_log_contH2` and obtain the
presentation — no `h2DimOf` bookkeeping, no cohomological input left in the group-theoretic step.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.HopfGaschutz

open Work.ConCohomology

/-- **The endgame consequence, in the arithmetic (`H²`) language.**  Let `Q` be a finite `2`-group
with a minimal generating family `gen : Fin 5 → Q` (five generators, no four), and suppose the
continuous `H²(Q,𝔽₂)` has `𝔽₂`-dimension at most `6` (i.e. `Nat.card = 2^k` with `k ≤ 6`).  Then
`Q` has a presentation on that family with at most six relators.

The hypothesis is `Nat.log 2 (Nat.card (contH2 Q)) ≤ 6`, i.e. literally `dim_{𝔽₂} H²(Q,𝔽₂) ≤ 6`. -/
theorem exists_relatorSet_five_six_of_le_log_contH2 (hdict : GaschutzDictionary 2)
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    [Fintype Q] [TopologicalSpace (FreeGroup (Fin 5))] [DiscreteTopology (FreeGroup (Fin 5))]
    (hQ : IsPGroup 2 Q) (gen : Fin 5 → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h : Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) ≤ 6) :
    ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) := by
  refine exists_relatorSet_five_six hdict hQ gen hgen hmin ?_
  rw [h2DimOf_eq_log_card_contH2 gen hgen
    (le_relFrattini_of_minimal_generating hQ gen hgen hmin)]
  exact h

/-- **The finite level of the endgame is vacuous, in the `H²` language.**  A finite `2`-group with
five minimal generators and `dim_{𝔽₂} H² ≤ 6` is trivial.  The finite `p`-group
Golod--Shafarevich inequality is *proved* in this workspace
(`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`), so the only input here is
`GaschutzDictionary 2`.

So the pair of numbers `(d, r) = (5, 6)` of the arithmetic input cannot describe a finite quotient of
`Γ`: the content of the bound `dim H²(Γ,𝔽₂) ≤ 6` is that `Γ` is *infinite*. -/
theorem subsingleton_of_log_card_contH2_le_six (hdict : GaschutzDictionary 2)
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    [Fintype Q] [TopologicalSpace (FreeGroup (Fin 5))] [DiscreteTopology (FreeGroup (Fin 5))]
    (hQ : IsPGroup 2 Q) (gen : Fin 5 → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h : Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) ≤ 6) : Subsingleton Q := by
  refine subsingleton_of_h2DimOf_le_six hdict
    (Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons 2) hQ gen hgen hmin ?_
  rw [h2DimOf_eq_log_card_contH2 gen hgen
    (le_relFrattini_of_minimal_generating hQ gen hgen hmin)]
  exact h

end Work.HopfGaschutz
