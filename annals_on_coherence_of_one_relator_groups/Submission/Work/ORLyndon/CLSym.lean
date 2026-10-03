import Mathlib
import Submission.Work.ORLyndon.CLInvDefs
import Submission.Work.ORLyndon.mmTopSym_mem_relatorLetters
import Submission.Work.ORLyndon.mmBotSym_mem_relatorLetters
import Submission.Work.ORLyndon.mmLo_ne_mmHi_or_exists_letter

/-!
# The extremal decorated symbols of the Magnus base

For a cyclically reduced root `u` which is not a proper power, of relator norm `≥ 2`, with a letter
`t` of exponent sum zero, the base of the exponent-sum-zero Magnus step is the decorated root
`rootW t u l hcyc he hl` in the occurring decorated alphabet `mmBeta t (u ^ l)`.  Its induction
hypothesis is consumed at an *extremal decorated symbol* of a letter `x ≠ t` of `u`: the top symbol
`mmTopSym t u l x hxt` or the bottom symbol `mmBotSym t u l x hxt`.

This file provides

* `Work.ORLyndon.mmTopSym_mem_relatorLetters`, `Work.ORLyndon.mmBotSym_mem_relatorLetters` -- the two
  extremal symbols are letters of the base root (so that the *letter-indexed* invariant
  `Work.ORLyndon.CLInvariant` can be consumed at them);
* `Work.ORLyndon.exists_extremal_sym_ne` -- for *any* prescribed symbol `s` of the base there is an
  extremal symbol of some letter `≠ t` of `u` different from `s`.  This is the combinatorial input
  that makes the single exempted letter of `CLInvariant` harmless: the exempted symbol of the base
  can always be avoided.

The combinatorial content of the last statement is
`Work.ORLyndon.mmLo_ne_mmHi_or_exists_letter`: either the two extremal symbols of `x` are distinct,
or a third letter `y ≠ t, x` of `u` exists (and then the top symbols of `x` and `y` differ because
their underlying letters do).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORLyndon

universe u

/-- **An extremal decorated symbol avoiding a prescribed one.**  Let `u` be cyclically reduced, not
a proper power, of relator norm `≥ 2`, and let `t` be a letter of exponent sum zero.  For every
letter `x ≠ t` of `u` and every symbol `s` of the decorated alphabet `mmBeta t (u ^ l)` there is a
symbol `q` of the base root `rootW t u l hcyc he hl`, different from `s`, which is the top or the
bottom decorated symbol of some letter `≠ t` of `u` (`x` itself, or a further letter `y`). -/
theorem exists_extremal_sym_ne {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hx : x ∈ Work.OROneRel.relatorLetters u) (hxt : x ≠ t)
    (s : Work.OROneRel.mmBeta t (u ^ l)) :
    ∃ q : Work.OROneRel.mmBeta t (u ^ l),
      q ∈ Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hcyc he hl) ∧ q ≠ s ∧
      (q = mmTopSym t u l x hxt ∨ q = mmBotSym t u l x hxt ∨
        ∃ (y : α) (hy : y ∈ Work.OROneRel.relatorLetters u) (hyt : y ≠ t),
          q = mmTopSym t u l y hyt ∨ q = mmBotSym t u l y hyt) := by
  classical
  have hval : ∀ (y : α) (hyt : y ≠ t),
      ((mmTopSym t u l y hyt : Work.OROneRel.mmBeta t (u ^ l)) : Work.OROneRel.MMAlpha t)
        = ((⟨y, hyt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmHi t u ⟨y, hyt⟩) := by
    intro y hyt
    rw [mmTopSym_val, Work.OROneRel.mmHi_pow t u hcyc he l hl]
  have hvalb : ∀ (y : α) (hyt : y ≠ t),
      ((mmBotSym t u l y hyt : Work.OROneRel.mmBeta t (u ^ l)) : Work.OROneRel.MMAlpha t)
        = ((⟨y, hyt⟩ : {a : α // a ≠ t}), Work.OROneRel.mmLo t u ⟨y, hyt⟩) := by
    intro y hyt
    rw [mmBotSym_val, Work.OROneRel.mmLo_pow t u hcyc he l hl]
  rcases mmLo_ne_mmHi_or_exists_letter t x u hpp hcyc hn he hx hxt with hne | ⟨y, hy, hyt, hyx⟩
  · -- the two extremal symbols of `x` differ, so one of them avoids `s`
    have hne' : mmTopSym t u l x hxt ≠ mmBotSym t u l x hxt := by
      intro h
      have h1 := congrArg (fun q : Work.OROneRel.mmBeta t (u ^ l) =>
        ((q : Work.OROneRel.MMAlpha t).2)) h
      rw [hval x hxt, hvalb x hxt] at h1
      exact hne h1.symm
    rcases eq_or_ne (mmTopSym t u l x hxt) s with htop | htop
    · refine ⟨mmBotSym t u l x hxt,
        mmBotSym_mem_relatorLetters t u l hcyc he hl x hxt hx, ?_, Or.inr (Or.inl rfl)⟩
      intro hc
      exact hne' (hc.trans htop.symm).symm
    · exact ⟨mmTopSym t u l x hxt, mmTopSym_mem_relatorLetters t u l hcyc he hl x hxt hx,
        htop, Or.inl rfl⟩
  · -- a further letter `y`; its symbols are disjoint from those of `x`
    by_cases h1 : mmTopSym t u l x hxt ≠ s
    · exact ⟨mmTopSym t u l x hxt, mmTopSym_mem_relatorLetters t u l hcyc he hl x hxt hx, h1,
        Or.inl rfl⟩
    · push_neg at h1
      by_cases h2 : mmTopSym t u l y hyt ≠ s
      · exact ⟨mmTopSym t u l y hyt, mmTopSym_mem_relatorLetters t u l hcyc he hl y hyt hy, h2,
          Or.inr (Or.inr ⟨y, hy, hyt, Or.inl rfl⟩)⟩
      · push_neg at h2
        by_cases h3 : mmBotSym t u l x hxt ≠ s
        · exact ⟨mmBotSym t u l x hxt, mmBotSym_mem_relatorLetters t u l hcyc he hl x hxt hx, h3,
            Or.inr (Or.inl rfl)⟩
        · push_neg at h3
          refine ⟨mmBotSym t u l y hyt,
            mmBotSym_mem_relatorLetters t u l hcyc he hl y hyt hy, ?_,
            Or.inr (Or.inr ⟨y, hy, hyt, Or.inr rfl⟩)⟩
          intro hc
          -- the two symbols have different underlying letters `y ≠ x`
          have hc' := congrArg (fun q : Work.OROneRel.mmBeta t (u ^ l) =>
            ((q : Work.OROneRel.MMAlpha t).1)) (hc.trans h1.symm)
          rw [hvalb y hyt, hval x hxt] at hc'
          exact hyx (Subtype.ext_iff.mp hc')

end Work.ORLyndon
