import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers
import Submission.Work.LinnikBurgess.frame_count_prov_aux.masterSum_eq_masterSum2
import Submission.Work.LinnikBurgess.frame_step_defs

/-!
# Definitions for the Case I estimate of the frame count (`sumI_le`)

This file collects the auxiliary quantities used in the proof of

`Work.LinnikBurgess.sumI_le` :
`sumI H m d g ≤ 30000 * τ(m*d*g)^8 * (H^6/(d*g) + H^5/g)`.

The master sum `sumI` sums `wtAB m a b` over pairs `(a,b)` of triples in `[1,H]^3` satisfying
`condAB d g a b` and `CaseI a b` (at least one of `a 1`, `a 2` is not a `b`-entry).  In the proof
the two disjuncts of `CaseI` are handled symmetrically and the condition "is not a `b`-entry" is
dropped, which *increases* the sum; the conditions are reordered so that the pivot `x0 = a 0`, the
second triple `b` and the two remaining entries `x1 = a 1`, `x2 = a 2` of `a` appear as explicit
summation indices.

* `SIframe H m d g` — the relaxed case I frame sum: the pivot `x0` and `b` are summed outermost,
  the conditions being `b l ≠ x0`, `x1 ≠ x0`, `x2 ≠ x0`, `DLd d ![x0,x1,x2] b`, and the necessary
  consequence `g ∣ ∏_k |x0 - b_k|` of `g ∣ contAB` (which is *weaker*, hence gives an upper bound);
* `bSumBox H m g x0` — the `b`-sum with the pivot fixed, i.e. `∑_b [b_l ≠ x0] [g ∣ ∏_k |x0-b_k|]
  ∏_k √(gcd m |x0-b_k|)`;
* `TTsum H m d x0 b` — the inner sum over `(x1,x2)` with the double-critical condition;
* `frameG H m d x0` — the frame-step bound for that inner sum: for each `x ≠ x0` the number of
  admissible partners is at most `3^(ω d) (H / frameMod _ _ _ + 1)`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-- The relaxed Case-I frame sum.  The pivot `x0`, the second triple `b` and the two remaining
entries `x1, x2` of the first triple are explicit summation indices.  The "not a `b`-entry"
condition of `CaseI` is dropped (it only weakens the sum) and the condition `g ∣ contAB a b` is
replaced by its consequence `g ∣ ∏_k |x0 - b_k|`. -/
noncomputable def SIframe (H m d g : ℕ) : ℝ :=
  ∑ x0 ∈ Finset.Icc 1 H, ∑ b ∈ box3 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
    (if (∀ l : Fin 3, b l ≠ x0) ∧ x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0, x1, x2] b
        ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
      then wtAB m ![x0, x1, x2] b else 0)

/-- The `b`-sum of the Case-I frame sum with the pivot `x0` fixed. -/
noncomputable def bSumBox (H m g : ℕ) (x0 : ℕ) : ℝ :=
  ∑ b ∈ box3 H,
    (if (∀ l : Fin 3, b l ≠ x0) ∧ (g ∣ ∏ k : Fin 3, del x0 (b k))
      then ∏ k : Fin 3, wg m x0 (b k) else 0)

/-- The inner `(x1,x2)`-sum of the Case-I frame sum, with the pivot `x0` and the second triple `b`
fixed.  The condition "`x1` is not a `b`-entry" has been dropped. -/
noncomputable def TTsum (H m d : ℕ) (x0 : ℕ) (b : Fin 3 → ℕ) : ℝ :=
  ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
    (if x1 ≠ x0 ∧ x2 ≠ x0 ∧ DLd d ![x0, x1, x2] b then wg m x0 x1 * wg m x0 x2 else 0)

/-- The frame-step bound for the inner `(x1,x2)`-sum: for every `x ≠ x0` in `[1,H]` the number of
partners `x2 ∈ [1,H]` with `DLd d ![x0,x1,x2] b` is at most `3^(ω d) * (H / frameMod d x0 x + 1)`,
uniformly in `b`. -/
noncomputable def frameG (H m d : ℕ) (x0 : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 1 H).filter (fun x => x ≠ x0),
    ((Nat.gcd m (del x0 x) : ℕ) : ℝ)
      * ((3 : ℝ) ^ d.primeFactors.card * ((H : ℝ) / (frameMod d x0 x : ℝ) + 1))

end Work.LinnikBurgess
