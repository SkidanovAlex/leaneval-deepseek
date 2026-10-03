import Mathlib
import Submission.Work.BourgainPlan.Maximal.lewkoLewko

/-!
# The `2`-variation over a dyadic window is dominated by the dyadic block square functions

Combining the numerical Lewko–Lewko inequality (`lewkoLewko`, condition (2) of KMSZ
Definition 5.1 for the `2`-variation) with the translation invariance of `chainSq`
(`chainSq_shift`), we obtain the window form

`V²(a : lo ≤ k ≤ lo + 2^n) ≤ 2 · Σ_{l=0}^{n} (Σ_{m<2^{n−l}} ‖a(lo + (m+1)2^l) − a(lo + m 2^l)‖²)^{1/2}`,

i.e. the `2`-variation over the window `[lo, lo + 2^n]` is bounded by the sum of the
`n + 1 = log₂(length) + 1` **dyadic block square functions** of the sequence.

This is the form in which the estimate is consumed downstream: the window of Bourgain's restricted
maximal inequality has `≍ ε log₂ N₀` dyadic scales, so `n ≍ log₂ log₂ N₀` — the `log log N₀` of
Bourgain's (7.35) is exactly the number of terms of this sum.  (The same shape, obtained from the
*seminorm* Rademacher–Menshov inequality rather than from the variation, is
`Submission.Work.BourgainPlan.Maximal.restrictedAbsMax_le_rmLevels`.)
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **The `2`-variation over the window `[lo, lo + 2^n]` is dominated by the dyadic block square
functions of the sequence.** -/
theorem varTwo_le_rmLevels (n lo : ℕ) (a : ℕ → E) :
    varTwo lo (lo + 2 ^ n) a
      ≤ ENNReal.ofReal (2 * ∑ l ∈ Finset.range (n + 1),
          rmLevel n l (fun r => a (lo + r))) := by
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hrange => ?_
  have hlo : lo ≤ t 0 := (hrange 0 (Nat.zero_le J)).1
  have hmono : Monotone (fun j => t j - lo) := fun i j hij =>
    Nat.sub_le_sub_right (ht hij) lo
  have htop : ∀ j ≤ J, t j - lo ≤ 2 ^ n := by
    intro j hj
    exact Nat.sub_le_iff_le_add'.mpr (hrange j hj).2
  have hch := chainSq_shift J lo a t ht hlo
  have hll := lewkoLewko n J (fun r => a (lo + r)) (fun j => t j - lo) hmono htop
  rw [hch]
  exact ENNReal.ofReal_le_ofReal hll

end

end Work.BourgainPlan.Maximal
