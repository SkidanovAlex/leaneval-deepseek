/-
# BMAX — the deliverable: Bender 1981, Lemma 2.3

`Work.GW2.Lemma23Prop` is the contract's statement of Bender 1981 Lemma 2.3 in the
minimal-counterexample context `BenderCtx` / `BenderSetup`.  This file derives it from

* `Work.GW2.BMAXToolkit` — Bender 1970, 1.1 (**proved** in `Thompson.lean`), 1.6,
  1.7(i)+(ii) and 1.7(iii) for `D`-groups, plus the `π`-equality step `FstarSamePrimeProp`
  of 1.6, and
* `Work.GW2.DihOrCycSubgroupProp` — the Sylow-2 heredity, **proved** in `DihOrCycSub.lean`.

The second input is what makes `Ĥ` and `M` `D`-groups inside `BenderCtx`: they are proper
(so `BenderCtx.ih` applies) and their Sylow 2-subgroups are cyclic or dihedral (heredity
from `BenderCtx.sylow`).  See `NOTES_FALSE_Bender17Prop.md` for why the `D`-group
hypotheses cannot be dropped.

The derivation:

* `A := Ĥ` is coatomic (`BenderSetup.Hhat_coatom`) and `B := M ≠ ⊤`, so the (i), (ii)
  clauses of `Bender17Prop` apply with `BRel B.Hhat M`;
* for (iii) let `A := Ĥ`, `B := M`, both coatomic with `A ⇝ B` and `B ⇝ A`:
  * if at least one of `F*(A)`, `F*(B)` is not a p-group, `Bender17iiiProp` gives
    `F*(A) ≤ B` and `F*(B) ≤ A`, and `Bender16Prop` supplies a common prime;
  * if both are p-groups, then (with either of them trivial the conclusion is immediate)
    the primes agree by `FstarSamePrimeProp`, the `π`-equality step of Bender's proof
    of 1.6.

In both cases the second disjunct of `Lemma23Prop`(iii) is produced, so no appeal to
B81's Lemma 2.4 (Glauberman's `Z(J)`-theorem) is needed here.
-/
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.FstarSamePrime
import Submission.Work.BMAX.DihOrCycSub
import Submission.Work.BMAX.Bender16DGroup
import Submission.Work.BMAX.Bender17DGroupMain
import Submission.Work.BMAX.Core18Bender17iiiCond

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-- The trivial subgroup is a p-group for every prime. -/
theorem isPGroup_bot_subgroup {G : Type} [Group G] (p : ℕ) : IsPGroup p (⊥ : Subgroup G) := by
  intro g
  exact ⟨1, by
    have hg : g = 1 := Subsingleton.elim g 1
    subst hg
    simp⟩

/-- **Bender 1981, Lemma 2.3** from the Sylow-2 heredity and Bender 1970, 1.1/1.6/1.7. -/
theorem lemma23_of_parts (hsub : DihOrCycSubgroupProp) (T : LocalToolkit) (K : BMAXToolkit) :
    Lemma23Prop := by
  intro G _ _ hFT hCtx B M hM hRel
  have hsimple : IsSimpleGroup G := hCtx.simple
  have hdihH : DihOrCycSylow B.Hhat := hsub G hCtx.sylow B.Hhat
  have hDH : IsDGroup B.Hhat := hCtx.ih B.Hhat B.card_Hhat_lt_card_G hdihH
  have hdihM : DihOrCycSylow M := hsub G hCtx.sylow M
  have hDM : IsDGroup M := hCtx.ih M (card_lt_card_of_ne_top hM) hdihM
  have h17 := K.b17 T G hsimple B.Hhat M hdihH hDH hdihM hDM B.Hhat_coatom hM hRel
  refine ⟨fun hnot => h17.1 hnot, h17.2.1, fun hCoatom hRel' => ?_⟩
  rcases eq_or_ne B.Hhat M with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    by_cases hside :
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn B.Hhat)) ∨
          (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn M))
    · obtain ⟨hAB, hBA⟩ := h17.2.2 hCoatom hRel' hside
      exact K.b16 T G hsimple B.Hhat M hdihH hDH hdihM hDM B.Hhat_coatom hCoatom h hAB hBA
    · push_neg at hside
      obtain ⟨⟨p, hp, hpG⟩, q, hq, hqG⟩ := hside
      by_cases hHbot : fstarIn B.Hhat = ⊥
      · exact ⟨q, hq, by rw [hHbot]; exact isPGroup_bot_subgroup q, hqG⟩
      by_cases hMbot : fstarIn M = ⊥
      · exact ⟨p, hp, hpG, by rw [hMbot]; exact isPGroup_bot_subgroup p⟩
      · have hpq : p = q :=
          K.sameP T G hsimple B.Hhat M hdihH hDH hdihM hDM B.Hhat_coatom hM hRel
            hCoatom hRel' h hHbot hMbot p q hp hq hpG hqG
        exact ⟨p, hp, hpG, hpq ▸ hqG⟩

/-- **THE DELIVERABLE.**  Bender 1981, Lemma 2.3 in the contract's `BenderCtx` setting,
from `LocalToolkit` alone.

All inputs are proved in this area:

* `DihOrCycSub` — the Sylow-2 heredity (`DS1`), which makes `Ĥ` and `M` D-groups;
* `thompsonLemma11` — Bender 1970, 1.1;
* `Bender16DGroup` — Bender 1970, 1.6;
* `Bender17DGroupMain` — Bender 1970, 1.7(i)+(ii), whose Thompson step is
  `CommutatorWitnessFinal`;
* `Core18Bender17iiiCond` — Bender 1970, 1.7(iii), with the mixed case closed by
  `layerIn_eq_bot_of_mixed` (GW design 18 §C), so **no** Dedekind input is needed;
* `FstarSamePrime` — the `π`-equality step of 1.6. -/
theorem lemma23 (T : LocalToolkit) : Lemma23Prop :=
  lemma23_of_parts BMAX.DihOrCycSub T
    (BMAXToolkit.of_parts thompsonLemma11 BMAX.Bender16DGroup BMAX.Bender17DGroupMain
      BMAX.Core18Bender17iiiCond (BMAX.FstarSamePrime T BMAX.Bender17DGroupMain))

end Work.GW2
