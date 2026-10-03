import Mathlib
import Submission.Work.Prop36SW.roundStmtW

/-!
# Definitions and constants for the round-by-round chain of §5

The §5 chain of `Work.Peluse.prop36SW_of_ladderA` runs `d - 1` rounds.  Every state of the chain
carries

* a *window invariant* `M₁ ≤ (H+1)^{d-1-m}` (at slot level `m`), which grows by one power of `H+1`
  at each round — exactly the paper's `δ'M^j → δ'M^{j+1}`;
* an *ambient invariant* `ambK D d c · (H+1)^d ≤ N`, which makes all the state's side conditions
  `M₁' M₂ ≤ N'`, `|p| M₁' M₂ ≤ N'` and the direction bounds automatic.

`sSup D d` is a crude bound for the slot counts `card (D.S j)`, `j ≤ d`; `ambK D d c` is the
data-independent ambient constant.  See `Submission/Work/Prop36SW/roundToNext.lean` for the
state-to-state step `Work.Prop36SW.roundToNextState` that consumes these invariants (its statement
is the frozen interface; `roundToNext.lean` also contains a partial proof, to be completed).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-- A crude bound for the slot counts: the sum of the cardinalities of `D.S j` for `j ≤ d`. -/
def sSup (D : IdxDatum) (d : ℕ) : ℕ := ∑ j ∈ Finset.range (d + 1), Fintype.card (D.S j)

theorem card_le_sSup (D : IdxDatum) {d j : ℕ} (hj : j ≤ d) : Fintype.card (D.S j) ≤ sSup D d := by
  refine Finset.single_le_sum (f := fun j => Fintype.card (D.S j)) (fun i _ => Nat.zero_le _) ?_
  exact Finset.mem_range.mpr (by omega)

/-- The ambient constant of the chain: every state's ambient `N` satisfies
`ambK · (H+1)^d ≤ N`. -/
def ambK (D : IdxDatum) (d : ℕ) (c : ℤ) : ℝ :=
  (2 : ℝ) ^ d * ((sSup D d : ℝ) + 1) ^ (d + 1) * ((Nat.factorial d : ℝ) + 1) ^ 2
    * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1)

theorem one_le_ambK (D : IdxDatum) (d : ℕ) (c : ℤ) : 1 ≤ ambK D d c := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ ((sSup D d : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) (sSup D d); linarith
  have h2' : (1 : ℝ) ≤ ((sSup D d : ℝ) + 1) ^ (d + 1) := one_le_pow₀ h2
  have h3 : (1 : ℝ) ≤ ((Nat.factorial d : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) (Nat.factorial d); linarith
  have h3' : (1 : ℝ) ≤ ((Nat.factorial d : ℝ) + 1) ^ 2 := one_le_pow₀ h3
  have h4 : (1 : ℝ) ≤ ((|(c : ℝ)|) + 1) := by
    have := abs_nonneg (c : ℝ); linarith
  have h5 : (1 : ℝ) ≤ ((d : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) d; linarith
  calc (1 : ℝ) = (1:ℝ) * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ (2 : ℝ) ^ d * ((sSup D d : ℝ) + 1) ^ (d + 1) * ((Nat.factorial d : ℝ) + 1) ^ 2
          * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2' (by norm_num) (by positivity))
          h3' (by positivity) (by positivity)) h4 (by positivity) (by positivity)) h5
          (by positivity) (by positivity)
    _ = ambK D d c := by rfl

end

end Work.Prop36SW
