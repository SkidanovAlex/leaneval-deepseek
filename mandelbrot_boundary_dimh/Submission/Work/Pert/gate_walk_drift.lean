import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.GateDriftRate.gate_walk_drift_rate_log
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou

/-!
# `Work.Pert.gate_walk_drift`: the drift of a legal walk in the lower gate

The proof has three layers.

1. **Reduction (this file).**  `hΨ` (`IsFatouCoordOn F Ψ (Qm Ξ α)`) and `hgate` give the Abel
   equation `Ψ (F^[n] z) = Ψ z + n` along the walk (`Work.Pert.abel_iter`).  Hence the first
   conjunct is *exactly* the near-translation drift bound `‖F^[n] z - (z + n)‖ ≤ RHS`, and the
   second follows from `|Im v| ≤ ‖v‖`.

2. **Room / geometry (this file).**  Along a walk the `b₂`-room `|Im w| - Re w - Ξ` *decreases* by
   at least `15/16` per step, so `n ≤ (32/15)(|Im z| + Re (1/α))`; the `b₁`-condition of the gate
   bounds `-Re z` above by `Re (1/α) + |Im z| + |Im (1/α)|`, and `InF1 α` gives
   `|Im (1/α)| ≤ Re (1/α)`.

3. **Drift (delegated pieces).**  `bounded_reduced_defect_coboundary` provides a bounded `η` with
   `η w - η (F w) = d(w) - endDefect u σ α`; hence the defect sum telescopes to `n · endDefect`
   plus a bounded remainder.  `endDefect_le_alpha_mul_Xi` bounds the coherent rate by
   `(1/2)‖α‖Ξ`.  As `Ξ‖α‖ ≤ 1/32` (from `hα`, `hM`) the coherent part is absorbed by the target's
   own `(1+|Im z|)/16` and `2^4‖α‖(n+1)` terms, while the bounded remainder is absorbed by
   `2^40(1+Ξ+1/Ξ+1/rr)(1+log(2+M)+log(2+‖z‖))`.
-/

namespace Work.Pert

open MandelDim Complex Set Metric
open scoped BigOperators

noncomputable section

/-! ## The room of a walk in the lower gate -/

/-- One step of a near-translation decreases the `b₂`-room `|Im w| - Re w - Ξ` by at least
`15/16`. -/
private lemma gw_room_step {Ξ : ℝ} {F : ℂ → ℂ} {w : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) :
    |(F w).im| - (F w).re - Ξ ≤ |w.im| - w.re - Ξ - 15 / 16 := by
  set ε : ℂ := F w - w - 1 with hε
  have hεn : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hε]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hre : (F w).re = w.re + 1 + ε.re := by
    rw [hε]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F w).im = w.im + ε.im := by
    rw [hε]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : -‖ε‖ ≤ ε.re := (abs_le.mp (Complex.abs_re_le_norm ε)).1
  have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
  have h2 : |(F w).im| ≤ |w.im| + ‖ε‖ := by
    have h4 := abs_add_le w.im ε.im
    rw [him]
    linarith
  linarith

/-- Along a legal walk the room to the upper boundary of the gate decreases by at least `15/16`
per step. -/
private lemma gw_walk_room_le {Ξ : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    |((Work.Pert.liftF u σ α)^[n] z).im| - ((Work.Pert.liftF u σ α)^[n] z).re - Ξ ≤
      |z.im| - z.re - Ξ - (15 / 16 : ℝ) * (n : ℝ) := by
  set F : ℂ → ℂ := Work.Pert.liftF u σ α with hF
  have key : ∀ j ≤ n, |(F^[j] z).im| - (F^[j] z).re - Ξ ≤
      |z.im| - z.re - Ξ - (15 / 16 : ℝ) * (j : ℝ) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
      have hik := ih hk'
      have hmem : F^[k] z ∈ Work.Pert.Qm Ξ α := hgate k hk'
      have hstep : ‖F (F^[k] z) - (F^[k] z + 1)‖ ≤ (1 / 32 : ℝ) := by
        rw [hF]; exact hNT _ hmem
      have hroom := gw_room_step (Ξ := Ξ) hstep
      rw [Function.iterate_succ_apply']
      push_cast
      linarith
  exact key n le_rfl

/-- `InF1 α` gives `|Im (1/α)| ≤ Re (1/α)`. -/
private lemma gw_im_inv_le_re_inv {α : ℂ} (h : MandelDim.InF1 α) :
    |(1 / α).im| ≤ (1 / α).re := by
  have hre : (0 : ℝ) < α.re := by
    have h' : |α.im| < α.re := h
    linarith [abs_nonneg α.im]
  have hns : (0 : ℝ) < α.normSq := Complex.normSq_pos.mpr (by
    intro h0; rw [h0] at hre; simp at hre)
  have h1 : (1 / α).im = -α.im / α.normSq := by rw [one_div, Complex.inv_im]
  have h2 : (1 / α).re = α.re / α.normSq := by rw [one_div, Complex.inv_re]
  rw [h1, h2, abs_div, abs_neg, abs_of_nonneg hns.le, div_le_div_iff_of_pos_right hns]
  exact le_of_lt h

/-- `Re (1/α) > 0` for `α` in the class `𝓕₁`. -/
private lemma gw_inv_re_pos {α : ℂ} (h : MandelDim.InF1 α) : 0 < (1 / α).re := by
  have hre : (0 : ℝ) < α.re := by
    have h' : |α.im| < α.re := h
    linarith [abs_nonneg α.im]
  have h2 : (1 / α).re = α.re / α.normSq := by rw [one_div, Complex.inv_re]
  have hns : (0 : ℝ) < α.normSq := Complex.normSq_pos.mpr (by
    intro h0; rw [h0] at hre; simp at hre)
  rw [h2]
  positivity

/-- **Room bound**: a legal walk of length `n` in the lower gate satisfies
`n ≤ (32/15)(|Im z| + Re (1/α))`. -/
private lemma gw_walk_len_le {Ξ : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    (n : ℝ) ≤ (32 / 15) * (|z.im| + (1 / α).re) := by
  set F : ℂ → ℂ := Work.Pert.liftF u σ α with hF
  have hroom := gw_walk_room_le (Ξ := Ξ) (α := α) (σ := σ) (u := u) (z := z) (n := n) hNT hgate
  -- the gate at time `n`: `Re w_n < |Im w_n| - Ξ`
  have hmem : F^[n] z ∈ Work.Pert.Qm Ξ α := hgate n le_rfl
  have hpos : 0 < |(F^[n] z).im| - (F^[n] z).re - Ξ := by
    have h := (Work.Pert.Qm_mem_iff (ξ := Ξ) (α := α) (z := F^[n] z)).mp hmem
    linarith [h.2]
  -- the gate at time `0`: `Ξ - Re (1/α) - |Im z + Im (1/α)| < Re z`
  have h0 : Ξ - (1 / α).re - |z.im + (1 / α).im| < z.re := by
    have h := (Work.Pert.Qm_mem_iff (ξ := Ξ) (α := α) (z := z)).mp (hgate 0 (Nat.zero_le n))
    simpa using h.1
  have htri : |z.im + (1 / α).im| ≤ |z.im| + |(1 / α).im| := abs_add_le _ _
  have him : |(1 / α).im| ≤ (1 / α).re := gw_im_inv_le_re_inv hInF1
  have hA : (0 : ℝ) ≤ (1 / α).re := le_of_lt (gw_inv_re_pos hInF1)
  have hroom0 : (15 / 16 : ℝ) * (n : ℝ) < |z.im| - z.re - Ξ := by linarith
  have hup : |z.im| - z.re - Ξ ≤ 2 * |z.im| + 2 * (1 / α).re := by linarith
  have h16 : (0 : ℝ) < 16 / 15 := by norm_num
  have hmult : (n : ℝ) < (16 / 15) * (2 * |z.im| + 2 * (1 / α).re) := by
    rw [show (16 / 15 : ℝ) * (2 * |z.im| + 2 * (1 / α).re)
        = (2 * |z.im| + 2 * (1 / α).re) / (15 / 16) by ring]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 15 / 16)]
    linarith
  have hfin : (16 / 15) * (2 * |z.im| + 2 * (1 / α).re)
      = (32 / 15) * (|z.im| + (1 / α).re) := by ring
  linarith [le_of_lt hmult, hfin.le, hfin.ge]

/-- `Ξ‖α‖ ≤ 1/32` under the hypotheses of the target. -/
private lemma gw_xi_mul_norm_alpha_le {Ξ M : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) :
    Ξ * ‖α‖ ≤ 1 / 32 := by
  have h1 : (0 : ℝ) < 32 * (M + 2 + Ξ) := by linarith
  have h2 : Ξ * ‖α‖ ≤ Ξ * (1 / (32 * (M + 2 + Ξ))) :=
    mul_le_mul_of_nonneg_left hα hΞ.le
  have h3 : Ξ * (1 / (32 * (M + 2 + Ξ))) ≤ 1 / 32 := by
    rw [mul_one_div, div_le_div_iff₀ h1 (by norm_num : (0 : ℝ) < 32)]
    linarith
  linarith

/-- `‖α‖ · Re (1/α) ≤ 1`. -/
private lemma gw_norm_alpha_mul_re_inv_le_one {α : ℂ} (h : MandelDim.InF1 α) :
    ‖α‖ * (1 / α).re ≤ 1 := by
  have hre : (0 : ℝ) < α.re := by
    have h' : |α.im| < α.re := h
    linarith [abs_nonneg α.im]
  have hpos : (0 : ℝ) < ‖α‖ := lt_of_lt_of_le hre (Complex.re_le_norm α)
  have h2 : (1 / α).re = α.re / α.normSq := by rw [one_div, Complex.inv_re]
  have h3 : (1 / α).re = α.re / ‖α‖ ^ 2 := by rw [h2, ← Complex.sq_norm α]
  rw [h3, mul_div_assoc', div_le_one (by positivity)]
  calc ‖α‖ * α.re ≤ ‖α‖ * ‖α‖ := mul_le_mul_of_nonneg_left (Complex.re_le_norm α) hpos.le
    _ = ‖α‖ ^ 2 := by ring

/-- The coherent part of the drift is absorbed by the target's own linear terms. -/
private lemma gw_coherent_le {Y A Ξ na : ℝ} (hY : 0 ≤ Y) (hΞ : 0 < Ξ) (hA : 0 ≤ A)
    (hXi : Ξ * na ≤ 1 / 32) (hnA : na * A ≤ 1) :
    (32 / 15) * (Y + A) * ((1 / 2) * na * Ξ) ≤ Y / 16 + 2 * Ξ := by
  have hkey : (32 / 15) * (Y + A) * ((1 / 2) * na * Ξ)
      = (16 / 15) * (na * Ξ) * Y + (16 / 15) * Ξ * (na * A) := by ring
  have h1 : (16 / 15) * (na * Ξ) ≤ 1 / 16 := by nlinarith [hXi]
  have h2 : (16 / 15) * Ξ * (na * A) ≤ 2 * Ξ := by nlinarith [hnA, hΞ]
  rw [hkey]
  linarith [mul_le_mul_of_nonneg_right h1 hY]

/-- The remaining constant of the drift plus `2Ξ` is dominated by the big constant of the
target. -/
private lemma gw_rem_plus_Xi_le_big {Ξ rr M : ℝ} {z : ℂ} (hΞ : 0 < Ξ) (hrr : 0 < rr)
    (hM : 2 ^ 10 ≤ M) :
    2 * Ξ + 2 ^ 31 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) ≤
      2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
  have hL : (1 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by
    have h1 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith [hM])
    have h2 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by
      have := norm_nonneg z; linarith)
    linarith
  have hfac : Ξ ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : 0 < 1 / Ξ := by positivity
    have h2 : 0 ≤ 1 / rr := by positivity
    linarith
  have h0 : (0 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := le_trans hΞ.le hfac
  have h40 : (2 : ℝ) ^ 32 ≤ 2 ^ 40 := by norm_num
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by linarith
  nlinarith [hL, hfac, h0, h40, hΞ, hL0]

theorem gate_walk_drift {Ξ rr M : ℝ} {α σ : ℂ} {u Ψ : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hΨ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Ψ (Work.Pert.Qm Ξ α))
    (hgate : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ‖(Ψ ((Work.Pert.liftF u σ α)^[n] z) - (Work.Pert.liftF u σ α)^[n] z) - (Ψ z - z)‖ ≤
        2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) +
          (1 + |z.im|) / 16 + 2 ^ 4 * ‖α‖ * ((n : ℝ) + 1) ∧
      |((Work.Pert.liftF u σ α)^[n] z).im - z.im| ≤
        2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) +
          (1 + |z.im|) / 16 + 2 ^ 4 * ‖α‖ * ((n : ℝ) + 1) := by
  set F : ℂ → ℂ := Work.Pert.liftF u σ α with hF
  -- the Abel equation along the walk
  have habel : Ψ (F^[n] z) = Ψ z + (n : ℂ) :=
    Work.Pert.abel_iter (F := F) (Φ := Ψ) (Q := Work.Pert.Qm Ξ α) (n := n) (ζ := z)
      hgate hΨ.2.2
  -- the drift bound: the average defect per step is at most `(1/2)‖α‖Ξ`, plus a bounded term
  have hdrift : ‖F^[n] z - (z + (n : ℂ))‖ ≤
      (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ) +
        2 ^ 31 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
    Work.Pert.GateDriftRate.gate_walk_drift_rate_log
      (Ξ := Ξ) (rr := rr) (M := M) (α := α) (σ := σ) (u := u) (z := z) (n := n)
      hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT (hgate 0 (Nat.zero_le n)) hgate
  -- room bound, and the geometry of `InF1`
  have hroom := gw_walk_len_le (Ξ := Ξ) (α := α) (σ := σ) (u := u) (z := z) (n := n)
    hΞ hInF1 hNT hgate
  have hXi : Ξ * ‖α‖ ≤ 1 / 32 := gw_xi_mul_norm_alpha_le hΞ hM hα
  have hnA : ‖α‖ * (1 / α).re ≤ 1 := gw_norm_alpha_mul_re_inv_le_one hInF1
  have hA : (0 : ℝ) ≤ (1 / α).re := le_of_lt (gw_inv_re_pos hInF1)
  have hY : (0 : ℝ) ≤ |z.im| := abs_nonneg _
  have hna : (0 : ℝ) ≤ ‖α‖ := norm_nonneg _
  -- the linear part is absorbed by the target's own `(1+|Im z|)/16` and `2^4‖α‖(n+1)`
  have hcoef : (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ) ≤ |z.im| / 16 + 2 * Ξ := by
    have hb : (0 : ℝ) ≤ (32 / 15) * (|z.im| + (1 / α).re) := by nlinarith
    have hc : (0 : ℝ) ≤ (1 / 2) * ‖α‖ * Ξ := by nlinarith
    have h1 : (n : ℝ) * ((1 / 2) * ‖α‖ * Ξ)
        ≤ (32 / 15) * (|z.im| + (1 / α).re) * ((1 / 2) * ‖α‖ * Ξ) :=
      mul_le_mul_of_nonneg_right hroom hc
    exact le_trans h1 (gw_coherent_le hY hΞ hA hXi hnA)
  have hrem := gw_rem_plus_Xi_le_big (Ξ := Ξ) (rr := rr) (M := M) (z := z) hΞ hrr hM
  have hmain : ‖F^[n] z - (z + (n : ℂ))‖ ≤
      2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) +
        (1 + |z.im|) / 16 + 2 ^ 4 * ‖α‖ * ((n : ℝ) + 1) := by
    have h16 : |z.im| / 16 ≤ (1 + |z.im|) / 16 := by linarith
    have h20 : (0 : ℝ) ≤ 2 ^ 4 * ‖α‖ * ((n : ℝ) + 1) := by positivity
    linarith [hdrift, hcoef, hrem, h16, h20]
  constructor
  · have heq : (Ψ (F^[n] z) - F^[n] z) - (Ψ z - z) = -(F^[n] z - (z + (n : ℂ))) := by
      rw [habel]; ring
    rw [heq, norm_neg]
    exact hmain
  · have him : ((F^[n] z).im - z.im) = ((F^[n] z - (z + (n : ℂ))).im) := by
      simp [Complex.sub_im]
    rw [him]
    exact le_trans (Complex.abs_im_le_norm _) hmain

end

end Work.Pert
