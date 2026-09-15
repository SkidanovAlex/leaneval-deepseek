import Submission.Work.GYCorr9
import Submission.Work.GYCount
import Submission.Work.GYMajorant

/-!
# `GYCorr10`: the `g`-reduction of the correlation bound

Green–Tao's correlation condition is reduced (Proposition `mu-cor-con` of the paper) to the
following chain, which this file starts:

* `g(y) := (φ(W)/W)·Λ_R(W·y.val + 1)²/log R · 1_{εp ≤ y.val ≤ 2εp}` and `ν ≤ 1 + g`;
* hence `∏_i ν(x+h_i) ≤ ∑_{A} ∏_{i∈A} g(x+h_i)` (multinomial expansion);
* the `A`-terms are estimated by (`A = ∅`): `1`; (`|A| = 1`): `≤ ε(1+ε_box)` via `BoxAvgGood`;
  (`|A| ≥ 2`): via the window lift of `GYCorr9` and `boxAvgCorr_ub'`.

This file contains the definitions of `g`, the pointwise inequality `ν ≤ 1 + g` and the
multinomial reduction; the estimates of the individual `A`-terms are in the next files.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {m : ℕ}

/-- Green–Tao's `g`: the `Λ_R²`-part of the majorant, restricted to the window. -/
noncomputable def gGT (R W p : ℕ) (ε : ℝ) (y : ZMod p) : ℝ :=
  if ε * (p : ℝ) ≤ (y.val : ℝ) ∧ (y.val : ℝ) ≤ 2 * ε * (p : ℝ) then nuBulk R W p y else 0

lemma gGT_nonneg {R W p : ℕ} {ε : ℝ} (hR : 1 < R) (y : ZMod p) : 0 ≤ gGT R W p ε y := by
  rw [gGT]
  split_ifs with h
  · exact nuBulk_nonneg hR y
  · exact le_refl 0

lemma gGT_le_nuBulk {R W p : ℕ} {ε : ℝ} (hR : 1 < R) (y : ZMod p) :
    gGT R W p ε y ≤ nuBulk R W p y := by
  rw [gGT]
  split_ifs with h
  · exact le_refl _
  · exact nuBulk_nonneg hR y

/-- **`ν ≤ 1 + g`.** -/
lemma nuGT_le_one_add_gGT {R W p : ℕ} {ε : ℝ} (x : ZMod p) :
    nuGT R W p ε x ≤ 1 + gGT R W p ε x := by
  rw [nuGT, gGT]
  split_ifs <;> linarith

/-- **The multinomial reduction.** -/
theorem prod_nuGT_le_sum_gGT {R W p : ℕ} {ε : ℝ} (hR : 1 < R) (h : Fin m → ZMod p)
    (x : ZMod p) :
    ∏ i : Fin m, nuGT R W p ε (x + h i)
      ≤ ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ i ∈ A, gGT R W p ε (x + h i) := by
  refine le_trans (Finset.prod_le_prod (fun i _ => nuGT_nonneg hR _)
    (fun i _ => nuGT_le_one_add_gGT _)) ?_
  rw [Finset.prod_one_add]

end Corr
end GYMaj
