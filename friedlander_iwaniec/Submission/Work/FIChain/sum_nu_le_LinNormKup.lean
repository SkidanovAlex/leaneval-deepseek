/-
# `Work.FIChain.sum_nu_le_LinNormKup` — the measure form of the windowed norm

The windowed companion of `Work.FIChain.sum_nu_le` (`VfBFacts.lean`): under the one-sided
`Ω_κ` norm `LinNormKup ν C κ D` — the ratio bound `∏_{w ≤ p < z}(1-νp)⁻¹ ≤ C (log z/log w)^κ`
**restricted to windows with `z ≤ D`** — the ν-measure of the same window of primes satisfies

    `∑_{w ≤ p < z} ν p ≤ log C + κ log (log z / log w)`.

The proof is the same chain as for `sum_nu_le`: `ν p ≤ -log (1-ν p)`, the log of the product is
turned around by `prod_one_sub_ge_up`, and `log (C·(log z/log w)^κ)` is expanded.  The only
change is that the ratio hypothesis is only available through `LinNormKup`, which is why the level
constraint `z ≤ D` is carried along.
-/
import Mathlib
import Submission.Work.FIChain.VfBFacts

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Ratio bound, windowed form.**  The windowed `Ω_κ` norm `LinNormKup ν C κ D` gives, for any
window `2 ≤ w ≤ z ≤ D`, the lower bound `(C (log z/log w)^κ)⁻¹ ≤ ∏_{w ≤ p < z}(1-νp)`. -/
lemma prod_one_sub_ge_up {ν : ℕ → ℝ} {C κ D : ℝ} (h : LinNormKup ν C κ D)
    (hν1 : ∀ p, p.Prime → ν p ≤ 1/2) {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) (hzD : z ≤ D)
    (hC : 0 < C) :
    (C * (Real.log z / Real.log w)^κ)⁻¹
      ≤ ∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p) := by
  have hprod := h w z hw hwz hzD
  have hpos : 0 < ∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have := hν1 p hp'; linarith
  have hCpos : 0 < C * (Real.log z / Real.log w)^κ := by
    apply mul_pos hC
    exact Real.rpow_pos_of_pos (div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))) κ
  rw [Finset.prod_inv_distrib] at hprod
  rw [inv_le_comm₀ hpos hCpos] at hprod
  exact hprod

/-- **Measure bound, windowed form** (the target `sum_nu_le_LinNormKup`). -/
theorem sum_nu_le_LinNormKup {ν : ℕ → ℝ} {C κ D : ℝ} (h : Work.FIChain.LinNormKup ν C κ D)
    (hν0 : ∀ p : ℕ, p.Prime → 0 ≤ ν p) (hν1 : ∀ p : ℕ, p.Prime → ν p ≤ 1 / 2)
    {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) (hzD : z ≤ D) (hC : 0 < C) :
    ∑ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p : ℕ => w ≤ (p : ℝ)), ν p
      ≤ Real.log C + κ * Real.log (Real.log z / Real.log w) := by
  have hpos : 0 < ∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have := hν1 p hp'; linarith
  have hCpos : 0 < C * (Real.log z / Real.log w)^κ := by
    apply mul_pos hC
    exact Real.rpow_pos_of_pos (div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))) κ
  have hle : ∀ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)),
      ν p ≤ - Real.log (1 - ν p) := by
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have h0 := hν0 p hp'; have h1 := hν1 p hp'
    have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - ν p by linarith)
    linarith
  have hsumlog : ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)),
      -Real.log (1 - ν p)
      = - Real.log (∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p)) := by
    rw [Finset.sum_neg_distrib, Real.log_prod]
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have := hν1 p hp'; linarith
  have hkey := prod_one_sub_ge_up h hν1 hw hwz hzD hC
  have hlogc : Real.log ((C * (Real.log z / Real.log w)^κ)⁻¹)
      ≤ Real.log (∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p)) :=
    Real.log_le_log (inv_pos.mpr hCpos) hkey
  have hlog2 : Real.log (C * (Real.log z / Real.log w)^κ)
      = Real.log C + κ * Real.log (Real.log z / Real.log w) := by
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos
      (div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))) κ)), Real.log_rpow]
    exact div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
  calc ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), ν p
      ≤ ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), -Real.log (1 - ν p) :=
        Finset.sum_le_sum hle
    _ = - Real.log (∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p)) :=
        hsumlog
    _ ≤ - Real.log ((C * (Real.log z / Real.log w)^κ)⁻¹) := by linarith
    _ = Real.log (C * (Real.log z / Real.log w)^κ) := by rw [Real.log_inv, neg_neg]
    _ = Real.log C + κ * Real.log (Real.log z / Real.log w) := hlog2

end

end Work.FIChain
