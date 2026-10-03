import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.gaugeExtWindowDefs
import Submission.Work.OROneRel.gxHelpers
import Submission.Work.OROneRel.gxTrivFrom_mul
import Submission.Work.OROneRel.gxTrivFrom_replicate_true
import Submission.Work.OROneRel.gxTrivFrom_replicate_false
import Submission.Work.OROneRel.gxTrivFrom_of_window
import Submission.Work.OROneRel.gxUpBase_arith
import Submission.Work.OROneRel.gxDnBase_arith

/-!
# The global gauge extending a window gauge

This file proves `Work.OROneRel.exists_globalGauge_of_windowData`.

`Wt : ℤ → FreeGroup α` is a *gauge* of the `ℤ`-cover of a one-relator presentation (`Wt 0 = 1` and
`cohom c (Wt i) = ofAdd i`), given on a level window `[lo,hi]` in which its words only walk along
edges of trivial loop class (`htree`, with `winTree`).  The conclusion is that `Wt` extends to a
gauge `Wt'` on *all* of `ℤ` whose every word's walk uses only edges of trivial loop class, the
extended gauge agreeing with `Wt` on the window.

## The construction

The extension `gxGauge Wt c lo hi x₀` (`Submission/Work/OROneRel/gaugeExtWindowDefs.lean`) is made by
chains of `x₀`-edges, in the two directions away from the window.  Since `0 < c x₀ =: d` and
`d ≤ hi - lo` (the window is at least one `x₀`-step wide), the window contains one representative of
every residue class mod `d`, so every level outside the window is reached from a *window* level by
`d`-steps:

* a level `j > hi` is `gxUpBase (c x₀) hi j + gxUpExp (c x₀) hi j * c x₀`, the base lying in
  `(hi - d, hi]`;
* a level `j < lo` is `gxDnBase (c x₀) lo j - gxDnExp (c x₀) lo j * c x₀`, the base lying in
  `[lo, lo + d)`,

and the word attached to `j` is the base word times the corresponding power of `x₀`.  The chain
edges have their far endpoint outside the window, so the chain equations `Wt' (v + d) = Wt' v * x₀`
can be imposed without contradicting the data on the window: this is what makes every traversed edge
of the extension trivial.  The arithmetic of the two base maps is in
`gxUpBase_arith` / `gxDnBase_arith`; the walk computations are `gxGauge_up_step` / `gxGauge_dn_step`,
which feed the two list lemmas `gxTrivFrom_replicate_true` / `gxTrivFrom_replicate_false`, and the
product of two walks is handled by `gxTrivFrom_mul`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

set_option linter.unusedVariables false

/-! ## The two chains of the extended gauge -/

/-- **The value of the extended gauge on the chain above the window.** -/
theorem gxGauge_up_val (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (x₀ : α)
    (hdle : c x₀ ≤ hi - lo) (hcx : 0 < c x₀) {j : ℤ} (hj : hi < j) (m : ℕ) :
    gxGauge Wt c lo hi x₀ (gxUpBase (c x₀) hi j + (m : ℤ) * c x₀)
      = Wt (gxUpBase (c x₀) hi j) * (FreeGroup.of x₀) ^ m := by
  obtain ⟨h1, ⟨h2a, h2b⟩, h3, h4, h5⟩ := gxUpBase_arith (d := c x₀) (hi := hi) (j := j) hcx
  rcases Nat.eq_zero_or_pos m with hm | hpos
  · subst hm
    rw [Nat.cast_zero, zero_mul, add_zero, gxGauge_of_mem ⟨by linarith, h2b⟩, pow_zero, mul_one]
  · have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hpos
    have hmd : c x₀ ≤ (m : ℤ) * c x₀ := by
      simpa using mul_le_mul_of_nonneg_right hm1 (le_of_lt hcx)
    have hgt : hi < gxUpBase (c x₀) hi j + (m : ℤ) * c x₀ := by nlinarith [h2a, hmd]
    rw [gxGauge_of_gt hgt, h3 (m : ℤ) (by omega), h4 (m : ℤ) (by omega), zpow_natCast]

/-- **The chain step above the window.** -/
theorem gxGauge_up_step (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (x₀ : α)
    (hdle : c x₀ ≤ hi - lo) (hcx : 0 < c x₀) {j : ℤ} (hj : hi < j) (m : ℕ) :
    gxGauge Wt c lo hi x₀ (gxUpBase (c x₀) hi j + ((m : ℤ) + 1) * c x₀)
      = gxGauge Wt c lo hi x₀ (gxUpBase (c x₀) hi j + (m : ℤ) * c x₀) * FreeGroup.of x₀ := by
  have hcast : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  rw [← hcast, gxGauge_up_val Wt c lo hi x₀ hdle hcx hj (m + 1),
    gxGauge_up_val Wt c lo hi x₀ hdle hcx hj m, pow_succ, mul_assoc]

/-- **The value of the extended gauge on the chain below the window.** -/
theorem gxGauge_dn_val (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (x₀ : α)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hdle : c x₀ ≤ hi - lo) (hcx : 0 < c x₀) {j : ℤ}
    (hj : j < lo) (m : ℕ) :
    gxGauge Wt c lo hi x₀ (gxDnBase (c x₀) lo j - (m : ℤ) * c x₀)
      = Wt (gxDnBase (c x₀) lo j) * (FreeGroup.of x₀) ^ (-(m : ℤ)) := by
  obtain ⟨h1, ⟨h2a, h2b⟩, h3, h4, h5⟩ := gxDnBase_arith (d := c x₀) (lo := lo) (j := j) hcx
  have hule : gxDnBase (c x₀) lo j ≤ hi := by linarith
  rcases Nat.eq_zero_or_pos m with hm | hpos
  · subst hm
    rw [Nat.cast_zero, zero_mul, sub_zero, gxGauge_of_mem ⟨h2a, hule⟩]
    simp
  · have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hpos
    have hmd : c x₀ ≤ (m : ℤ) * c x₀ := by
      simpa using mul_le_mul_of_nonneg_right hm1 (le_of_lt hcx)
    have hlt : gxDnBase (c x₀) lo j - (m : ℤ) * c x₀ < lo := by nlinarith [h2b, hmd]
    rw [gxGauge_of_lt hlo hhi hlt, h3 (m : ℤ) (by omega), h4 (m : ℤ) (by omega)]

/-- **The chain step below the window.** -/
theorem gxGauge_dn_step (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (x₀ : α)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hdle : c x₀ ≤ hi - lo) (hcx : 0 < c x₀) {j : ℤ}
    (hj : j < lo) (m : ℕ) :
    gxGauge Wt c lo hi x₀ (gxDnBase (c x₀) lo j - (m : ℤ) * c x₀)
      = gxGauge Wt c lo hi x₀ (gxDnBase (c x₀) lo j - ((m : ℤ) + 1) * c x₀) * FreeGroup.of x₀ := by
  have hcast : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  rw [← hcast, gxGauge_dn_val Wt c lo hi x₀ hlo hhi hdle hcx hj m,
    gxGauge_dn_val Wt c lo hi x₀ hlo hhi hdle hcx hj (m + 1)]
  have hexp : -(((m + 1 : ℕ)) : ℤ) = -(m : ℤ) - 1 := by push_cast; ring
  rw [hexp]
  have hx : (FreeGroup.of x₀ : FreeGroup α) ^ (-(m : ℤ))
      = (FreeGroup.of x₀) ^ (-(m : ℤ) - 1) * FreeGroup.of x₀ := by
    have h := zpow_add_one (FreeGroup.of x₀ : FreeGroup α) (-(m : ℤ) - 1)
    rw [show (-(m : ℤ) - 1) + 1 = -(m : ℤ) by ring] at h
    exact h
  rw [hx, mul_assoc]

theorem exists_globalGauge_of_windowData {α : Type*} [DecidableEq α]
    (c : α → ℤ) (Wt : ℤ → FreeGroup α) (lo hi : ℤ) (x₀ : α)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hcx : 0 < c x₀) (hd : c x₀ ≤ hi - lo)
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi) :
    ∃ Wt' : ℤ → FreeGroup α,
      (∀ i : ℤ, lo ≤ i → i ≤ hi → Wt' i = Wt i) ∧
      (∀ i : ℤ, Work.OROneRel.cohom c (Wt' i) = Multiplicative.ofAdd i) ∧
      (∀ j : ℤ, ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt' j)),
        Work.OROneRel.coverClassAt Wt' c (Work.OROneRel.coverEdge e) = 1) := by
  refine ⟨gxGauge Wt c lo hi x₀, ?_, ?_, ?_⟩
  · -- agreement with `Wt` on the window
    intro i h1 h2
    exact gxGauge_of_mem ⟨h1, h2⟩
  · -- the extended gauge is a gauge
    intro i
    by_cases hgt : hi < i
    · rw [gxGauge_of_gt hgt, map_mul, hcoh (gxUpBase (c x₀) hi i), gx_cohom_of_zpow,
        ← ofAdd_add]
      rw [(gxUpBase_arith (d := c x₀) (hi := hi) (j := i) hcx).1]
    · by_cases hlt : i < lo
      · rw [gxGauge_of_lt hlo hhi hlt, map_mul, hcoh (gxDnBase (c x₀) lo i), gx_cohom_of_zpow,
          ← ofAdd_add]
        have h := (gxDnBase_arith (d := c x₀) (lo := lo) (j := i) hcx).1
        have h' : gxDnBase (c x₀) lo i + (-(gxDnExp (c x₀) lo i)) * c x₀ = i := by
          rw [neg_mul, ← sub_eq_add_neg]
          exact h
        rw [h']
      · have hwin : lo ≤ i ∧ i ≤ hi := ⟨le_of_not_gt hlt, le_of_not_gt hgt⟩
        rw [gxGauge_of_mem hwin]
        exact hcoh i
  · -- every walk of the extended gauge is trivial
    intro j e he
    by_cases hgt : hi < j
    · -- above the window: the walk is the base walk followed by the `x₀`-chain
      have hk1 : 1 ≤ gxUpExp (c x₀) hi j :=
        (gxUpBase_arith (d := c x₀) (hi := hi) (j := j) hcx).2.2.2.2 hgt
      have hcast : (((gxUpExp (c x₀) hi j).toNat : ℕ) : ℤ) = gxUpExp (c x₀) hi j :=
        Int.toNat_of_nonneg (by omega)
      have hpow : (FreeGroup.of x₀ : FreeGroup α) ^ (gxUpExp (c x₀) hi j)
          = (FreeGroup.of x₀) ^ (gxUpExp (c x₀) hi j).toNat := by
        conv_lhs => rw [← hcast, zpow_natCast]
      have hval : gxGauge Wt c lo hi x₀ j
          = Wt (gxUpBase (c x₀) hi j) * (FreeGroup.of x₀) ^ (gxUpExp (c x₀) hi j).toNat := by
        rw [gxGauge_of_gt hgt, hpow]
      rw [hval] at he
      have hmul := gxTrivFrom_mul c (gxGauge Wt c lo hi x₀) 0 (Wt (gxUpBase (c x₀) hi j))
        ((FreeGroup.of x₀) ^ (gxUpExp (c x₀) hi j).toNat) ?_ ?_
      · exact hmul e he
      · -- the base level lies in the window
        refine gxTrivFrom_of_window (fun k h1 h2 => gxGauge_of_mem ⟨h1, h2⟩) htree ?_ ?_
        · have h2a := (gxUpBase_arith (d := c x₀) (hi := hi) (j := j) hcx).2.1.1
          linarith
        · exact (gxUpBase_arith (d := c x₀) (hi := hi) (j := j) hcx).2.1.2
      · -- the chain
        rw [gx_lsig_wordOf_of_cohom c (hcoh _), zero_add, gx_wordOf_pow]
        refine gxTrivFrom_replicate_true c (gxGauge Wt c lo hi x₀) x₀ (gxUpBase (c x₀) hi j)
          (gxUpExp (c x₀) hi j).toNat ?_
        intro m _
        exact gxGauge_up_step Wt c lo hi x₀ hd hcx hgt m
    · by_cases hlt : j < lo
      · -- below the window
        have hn1 : 1 ≤ gxDnExp (c x₀) lo j :=
          (gxDnBase_arith (d := c x₀) (lo := lo) (j := j) hcx).2.2.2.2 hlt
        have hcast : (((gxDnExp (c x₀) lo j).toNat : ℕ) : ℤ) = gxDnExp (c x₀) lo j :=
          Int.toNat_of_nonneg (by omega)
        have hpow : (FreeGroup.of x₀ : FreeGroup α) ^ (-(gxDnExp (c x₀) lo j))
            = (FreeGroup.of x₀) ^ (-(((gxDnExp (c x₀) lo j).toNat : ℕ) : ℤ)) := by
          conv_lhs => rw [← hcast]
        have hval : gxGauge Wt c lo hi x₀ j
            = Wt (gxDnBase (c x₀) lo j)
              * (FreeGroup.of x₀) ^ (-(((gxDnExp (c x₀) lo j).toNat : ℕ) : ℤ)) := by
          rw [gxGauge_of_lt hlo hhi hlt, hpow]
        rw [hval] at he
        have hmul := gxTrivFrom_mul c (gxGauge Wt c lo hi x₀) 0 (Wt (gxDnBase (c x₀) lo j))
          ((FreeGroup.of x₀) ^ (-(((gxDnExp (c x₀) lo j).toNat : ℕ) : ℤ))) ?_ ?_
        · exact hmul e he
        · -- the base level lies in the window
          refine gxTrivFrom_of_window (fun k h1 h2 => gxGauge_of_mem ⟨h1, h2⟩) htree ?_ ?_
          · exact (gxDnBase_arith (d := c x₀) (lo := lo) (j := j) hcx).2.1.1
          · have h2b := (gxDnBase_arith (d := c x₀) (lo := lo) (j := j) hcx).2.1.2
            linarith
        · -- the chain
          rw [gx_lsig_wordOf_of_cohom c (hcoh _), zero_add, gx_wordOf_zpow_neg]
          refine gxTrivFrom_replicate_false c (gxGauge Wt c lo hi x₀) x₀ (gxDnBase (c x₀) lo j)
            (gxDnExp (c x₀) lo j).toNat ?_
          intro m _
          exact gxGauge_dn_step Wt c lo hi x₀ hlo hhi hd hcx hlt m
      · -- inside the window: the claim is `htree`
        have hwin : lo ≤ j ∧ j ≤ hi := ⟨le_of_not_gt hlt, le_of_not_gt hgt⟩
        rw [gxGauge_of_mem hwin] at he
        exact gxTrivFrom_of_window (fun k h1 h2 => gxGauge_of_mem ⟨h1, h2⟩) htree hwin.1 hwin.2 e he

end Work.OROneRel
