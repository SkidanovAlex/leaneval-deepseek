import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `cup3Swap` has no fixed points

`cup3Swap` (defined in `Submission/Work/Pi6/SQM/Cup3CobSetup.lean`) is the pairing involution
of the disjoint union `L3Idx ⊕ T3Idx ⊕ T4Idx ⊕ T1Idx ⊕ T2Idx` underlying the classical
"interval" proof of the mod-2 `∪₃` coboundary formula

`δ(u ∪₃ v) = u ∪₂ v + v ∪₂ u + (δu) ∪₃ v + u ∪₃ (δv)`.

This file records that it is fixed-point free, the index-level input (beside
`Work.Pi6.SQM.cup3SwapInvol`) to `Finset.sum_involution`.

## Proof

The proof is a case analysis over the five summands of `Idx3` and, inside each summand, over the
branch conditions of the `if`-chain of `swapL`/`swapC3`/`swapC4`/`swapT1`/`swapT2`.  In most
branches the value of the swap lands in a *different* summand than the argument, and the
equality is impossible on shape (`Sum.inl_ne_inr` / `Sum.inr_ne_inl` after stripping the
`Sum.inr` constructors).  In the remaining branches (`T3 → T3` and `T4 → T4`) the value has the
same shape as the argument, and the equality of the two indices unfolds, via
`Subtype.mk.injEq`/`Prod.mk.injEq`/`Fin.ext_iff`, into `ℕ`-equalities which contradict the
branch conditions (`omega`).

Note the two `def`s `cup3Swap` and `swapX` are *not* reducible at the default transparency, so
the branch conditions of the `if`-chains are not syntactically the reduced ones; the `set_option
backward.isDefEq.respectTransparency false` below (the same option used by `Cup3CobSetup.lean`)
is what makes the `rw [dif_pos …]` steps match.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.deprecated false
set_option maxHeartbeats 6400000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

/-- `cup3Swap` has no fixed points on the `L3`-summand: `swapL` always lands in the `T3`- or
`T4`-summand. -/
private theorem cup3Swap_ne_l3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : L3Idx n m) :
    cup3Swap n m hn hm (Sum.inl p) ≠ Sum.inl p := by
  intro h
  obtain ⟨⟨k, a, b, c⟩, hp⟩ := p
  simp only [cup3Swap, swapL, idxC3, idxC4, L3a, L3b, L3c, L3k] at h
  by_cases h1 : k.val ≤ a.val
  · rw [dif_pos h1] at h; exact Sum.inr_ne_inl h
  · rw [dif_neg h1] at h
    by_cases h2 : k.val ≤ a.val + b.val + 1
    · rw [dif_pos h2] at h; exact Sum.inr_ne_inl h
    · rw [dif_neg h2] at h
      by_cases h3 : k.val ≤ a.val + b.val + c.val + 2
      · rw [dif_pos h3] at h; exact Sum.inr_ne_inl h
      · rw [dif_neg h3] at h
        by_cases h4 : k.val ≤ a.val + c.val + m
        · rw [dif_pos h4] at h; exact Sum.inr_ne_inl h
        · rw [dif_neg h4] at h; exact Sum.inr_ne_inl h

/-- `cup3Swap` has no fixed points on the `T3`-summand.  The branches landing back in the
`T3`-summand (`j = a+1, c = 0` and `j = a+c+2, c = 0`) change the `b`-coordinate, so the
equality of indices is contradictory. -/
private theorem cup3Swap_ne_c3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T3Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inl p)) ≠ Sum.inr (Sum.inl p) := by
  intro h
  obtain ⟨⟨a, b, c, j⟩, hp⟩ := p
  simp only [cup3Swap, swapC3, C3a, C3b, C3c, C3j, idxL, idxC3, idxC4, idxT1, idxT2] at h
  by_cases h1 : j.val + 1 ≤ a.val
  · rw [dif_pos h1] at h; exact Sum.inl_ne_inr h
  · rw [dif_neg h1] at h
    by_cases h2 : j.val = a.val
    · rw [dif_pos h2] at h
      by_cases h2' : 1 ≤ a.val
      · rw [dif_pos h2'] at h; exact Sum.inr_ne_inl (Sum.inr.inj h)
      · rw [dif_neg h2'] at h
        exact Sum.inr_ne_inl (Sum.inr.inj h)
    · rw [dif_neg h2] at h
      by_cases h3 : j.val = a.val + 1
      · rw [dif_pos h3] at h
        by_cases h3' : 1 ≤ c.val
        · rw [dif_pos h3'] at h; exact Sum.inr_ne_inl (Sum.inr.inj h)
        · rw [dif_neg h3'] at h
          by_cases h3'' : b.val + 4 ≤ m
          · rw [dif_pos h3''] at h
            simp only [Sum.inr.injEq, Sum.inl.injEq, mkT3, Subtype.mk.injEq, Prod.mk.injEq,
              Fin.ext_iff] at h
            omega
          · rw [dif_neg h3''] at h
            by_cases h3''' : a.val + 3 ≤ n
            · rw [dif_pos h3'''] at h; exact Sum.inr_ne_inl (Sum.inr.inj h)
            · rw [dif_neg h3'''] at h
              exact Sum.inr_ne_inl (Sum.inr.inj h)
      · rw [dif_neg h3] at h
        by_cases h4 : j.val ≤ a.val + c.val + 1
        · rw [dif_pos h4] at h; exact Sum.inl_ne_inr h
        · rw [dif_neg h4] at h
          by_cases h5 : j.val = a.val + c.val + 2
          · rw [dif_pos h5] at h
            by_cases h5' : 1 ≤ c.val
            · rw [dif_pos h5'] at h; exact Sum.inr_ne_inl (Sum.inr.inj h)
            · rw [dif_neg h5'] at h
              by_cases h5'' : 1 ≤ b.val
              · rw [dif_pos h5''] at h
                simp only [Sum.inr.injEq, Sum.inl.injEq, mkT3, Subtype.mk.injEq, Prod.mk.injEq,
                  Fin.ext_iff] at h
                omega
              · rw [dif_neg h5''] at h
                by_cases h5''' : 1 ≤ a.val
                · rw [dif_pos h5'''] at h; exact Sum.inr_ne_inl (Sum.inr.inj h)
                · rw [dif_neg h5'''] at h
                  exact Sum.inr_ne_inl (Sum.inr.inj h)
          · rw [dif_neg h5] at h
            by_cases h6 : j.val = a.val + c.val + 3
            · rw [dif_pos h6] at h
              by_cases h6' : a.val + c.val + 3 ≤ n
              · rw [dif_pos h6'] at h; exact Sum.inr_ne_inl (Sum.inr.inj h)
              · rw [dif_neg h6'] at h
                exact Sum.inr_ne_inl (Sum.inr.inj h)
            · rw [dif_neg h6] at h
              exact Sum.inl_ne_inr h

/-- `cup3Swap` has no fixed points on the `T4`-summand.  The branches landing back in the
`T4`-summand all change (at least) one of the `a`-, `c`- or `j`-coordinates. -/
private theorem cup3Swap_ne_c4 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T4Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inl p))) ≠
      Sum.inr (Sum.inr (Sum.inl p)) := by
  intro h
  obtain ⟨⟨a, b, c, j⟩, hp⟩ := p
  simp only [cup3Swap, swapC4, C4a, C4b, C4c, C4j, idxL, idxC3, idxC4, idxT1, idxT2] at h
  by_cases h1 : j.val = 0
  · rw [dif_pos h1] at h
    by_cases h1' : 1 ≤ b.val
    · rw [dif_pos h1'] at h; exact Sum.inl_ne_inr (Sum.inr.inj h)
    · rw [dif_neg h1'] at h
      by_cases h1'' : 1 ≤ c.val
      · rw [dif_pos h1''] at h
        simp only [Sum.inr.injEq, Sum.inl.injEq, mkT4, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.ext_iff] at h
        omega
      · rw [dif_neg h1''] at h
        by_cases h1''' : m = 2
        · rw [dif_pos h1'''] at h
          by_cases h1'''' : a.val + 3 = n
          · rw [dif_pos h1''''] at h
            exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inr.inj h))
          · rw [dif_neg h1''''] at h
            simp only [Sum.inr.injEq, Sum.inl.injEq, mkT4, Subtype.mk.injEq, Prod.mk.injEq,
              Fin.ext_iff] at h
            omega
        · rw [dif_neg h1'''] at h
          exact Sum.inl_ne_inr (Sum.inr.inj h)
  · rw [dif_neg h1] at h
    by_cases h2 : j.val ≤ b.val
    · rw [dif_pos h2] at h; exact Sum.inl_ne_inr h
    · rw [dif_neg h2] at h
      by_cases h3 : j.val ≤ b.val + 1
      · rw [dif_pos h3] at h
        by_cases h3' : 1 ≤ b.val
        · rw [dif_pos h3'] at h; exact Sum.inl_ne_inr (Sum.inr.inj h)
        · rw [dif_neg h3'] at h
          by_cases h3'' : 1 ≤ a.val
          · rw [dif_pos h3''] at h
            simp only [Sum.inr.injEq, Sum.inl.injEq, mkT4, Subtype.mk.injEq, Prod.mk.injEq,
              Fin.ext_iff] at h
            omega
          · rw [dif_neg h3''] at h
            exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inr.inj h))
      · rw [dif_neg h3] at h
        by_cases h4 : j.val ≤ b.val + 2
        · rw [dif_pos h4] at h
          by_cases h4' : b.val + 3 ≤ m
          · rw [dif_pos h4'] at h; exact Sum.inl_ne_inr (Sum.inr.inj h)
          · rw [dif_neg h4'] at h
            by_cases h4'' : a.val + c.val + 4 ≤ n
            · rw [dif_pos h4''] at h
              simp only [Sum.inr.injEq, Sum.inl.injEq, mkT4, Subtype.mk.injEq, Prod.mk.injEq,
                Fin.ext_iff] at h
              omega
            · rw [dif_neg h4''] at h
              exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inr.inj h))
        · rw [dif_neg h4] at h
          by_cases h5 : j.val ≤ m
          · rw [dif_pos h5] at h; exact Sum.inl_ne_inr h
          · rw [dif_neg h5] at h
            by_cases h6 : b.val + 3 ≤ m
            · rw [dif_pos h6] at h; exact Sum.inl_ne_inr (Sum.inr.inj h)
            · rw [dif_neg h6] at h
              by_cases h6' : 1 ≤ c.val
              · rw [dif_pos h6'] at h
                simp only [Sum.inr.injEq, Sum.inl.injEq, mkT4, Subtype.mk.injEq, Prod.mk.injEq,
                  Fin.ext_iff] at h
                omega
              · rw [dif_neg h6'] at h
                by_cases h6'' : m = 2
                · rw [dif_pos h6''] at h
                  by_cases h6''' : a.val = 0
                  · rw [dif_pos h6'''] at h
                    exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inr.inj h))
                  · rw [dif_neg h6'''] at h
                    simp only [Sum.inr.injEq, Sum.inl.injEq, mkT4, Subtype.mk.injEq,
                      Prod.mk.injEq, Fin.ext_iff] at h
                    omega
                · rw [dif_neg h6''] at h
                  exact Sum.inl_ne_inr (Sum.inr.inj h)

/-- `cup3Swap` has no fixed points on the `T1`-summand: `swapT1` always lands in the `T3`-,
`T4`- or `T2`-summand. -/
private theorem cup3Swap_ne_t1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T1Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) ≠
      Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) := by
  intro h
  obtain ⟨a, b⟩ := p
  simp only [cup3Swap, swapT1, idxC3, idxC4, idxT2] at h
  by_cases h1 : b.val + 3 ≤ m
  · rw [dif_pos h1] at h; exact Sum.inl_ne_inr (Sum.inr.inj h)
  · rw [dif_neg h1] at h
    by_cases h2 : a.val + 3 ≤ n
    · rw [dif_pos h2] at h
      exact Sum.inl_ne_inr (Sum.inr.inj (Sum.inr.inj h))
    · rw [dif_neg h2] at h
      by_cases h3 : m = 2
      · rw [dif_pos h3] at h
        by_cases h3' : n = 2
        · rw [dif_pos h3'] at h
          exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))
        · rw [dif_neg h3'] at h
          exact Sum.inl_ne_inr (Sum.inr.inj (Sum.inr.inj h))
      · rw [dif_neg h3] at h
        exact Sum.inl_ne_inr (Sum.inr.inj h)

/-- `cup3Swap` has no fixed points on the `T2`-summand: `swapT2` always lands in the `T3`-,
`T4`- or `T1`-summand. -/
private theorem cup3Swap_ne_t2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T2Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) ≠
      Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) := by
  intro h
  obtain ⟨a, b⟩ := p
  simp only [cup3Swap, swapT2, idxC3, idxC4, idxT1] at h
  by_cases h1 : 1 ≤ a.val
  · rw [dif_pos h1] at h; exact Sum.inl_ne_inr (Sum.inr.inj h)
  · rw [dif_neg h1] at h
    by_cases h2 : 1 ≤ b.val
    · rw [dif_pos h2] at h
      exact Sum.inl_ne_inr (Sum.inr.inj (Sum.inr.inj h))
    · rw [dif_neg h2] at h
      by_cases h3 : m = 2
      · rw [dif_pos h3] at h
        by_cases h3' : n = 2
        · rw [dif_pos h3'] at h
          exact Sum.inl_ne_inr (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))
        · rw [dif_neg h3'] at h
          exact Sum.inl_ne_inr (Sum.inr.inj (Sum.inr.inj h))
      · rw [dif_neg h3] at h
        exact Sum.inl_ne_inr (Sum.inr.inj h)

/-- **The pairing involution `cup3Swap` has no fixed points.** -/
theorem cup3SwapNe (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (x : Work.Pi6.SQM.Idx3 n m) :
    Work.Pi6.SQM.cup3Swap n m hn hm x ≠ x := by
  intro h
  cases x with
  | inl p => exact cup3Swap_ne_l3 n m hn hm p h
  | inr y =>
      cases y with
      | inl p => exact cup3Swap_ne_c3 n m hn hm p h
      | inr y =>
          cases y with
          | inl p => exact cup3Swap_ne_c4 n m hn hm p h
          | inr y =>
              cases y with
              | inl p => exact cup3Swap_ne_t1 n m hn hm p h
              | inr p => exact cup3Swap_ne_t2 n m hn hm p h

end

end Work.Pi6.SQM
