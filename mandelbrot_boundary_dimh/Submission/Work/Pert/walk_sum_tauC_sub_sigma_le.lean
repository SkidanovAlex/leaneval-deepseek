import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.sum_inv_dist_gate_walk
import Submission.Work.Pert.count_gate_walk_close
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge
import Submission.Work.Pert.tauC_sub_sigma_norm_le
import Submission.Work.Pert.tauC_norm_le_gate_five
import Submission.Work.Pert.lattice_dist_ge_of_tauC_le
import Submission.Work.Pert.sum_two_add_inv_lattice_le

/-!
# PERT · `Work.Pert.walk_sum_tauC_sub_sigma_le`

The "value comparison" sum of Shishikura §4.2: along a legal walk `w_j = F^[j] z` in the lower
gate `Qm Ξ α` of a perturbed map with normal-form data `(σ, u, α)`,

  `∑_{j<n} ‖τ_f (w_j) - σ‖ ≤ 2^12 (1 + n‖α‖)(1 + log (2+n))`.

The three ingredients (all separate lemmas in this directory):

* **pointwise** (`Work.Pert.tauC_sub_sigma_norm_le`, no hypotheses): since
  `τ_f w - σ = σ/(e^{2πi α w} - 1)`, the lattice separation `dist (αw, ℤ)` controls the value:
  `‖τ_f w - σ‖ ≤ ‖σ‖ (2 + (9/25)/dist (αw, ℤ))`.
* **the walk stays off the lattice** (`Work.Pert.tauC_norm_le_gate_five` +
  `Work.Pert.lattice_dist_ge_of_tauC_le`): the near-translation hypothesis forces `‖τ_f‖ ≤ 5` on
  the whole gate, hence `dist (αw, ℤ) ≥ ‖α‖/20` for every gate point off the lattice.
* **harmonic summation** (`Work.Pert.sum_two_add_inv_lattice_le`): the two proven walk estimates
  `Work.Pert.sum_inv_dist_gate_walk` and `Work.Pert.count_walk_level` (behind
  `Work.Pert.count_gate_walk_close`) give
  `∑_{j<n} 1/dist (αw_j, ℤ) ≲ (1+n‖α‖)(1+log(2+n))/‖α‖ + (1+n‖α‖)/(c₀‖α‖)`.
-/

namespace Work.Pert

open scoped Classical

noncomputable section

/-- Final arithmetic: with `‖σ‖ ≤ 32‖α‖` the summed bound of
`Work.Pert.sum_two_add_inv_lattice_le` (at `c₀ = 1/20`) is at most `2^12 (1+n‖α‖)(1+log(2+n))`. -/
private lemma final_arith {h s : ℝ} {n : ℕ} (hh : 0 < h) (hs : 0 ≤ s) (hs32 : s ≤ 32 * h) :
    s * (2 * (n : ℝ)
          + 11 * (1 + (n : ℝ) * h) * (1 + Real.log (2 + (n : ℝ))) / h
          + 5 * (1 + (n : ℝ) * h) / ((1 / 20 : ℝ) * h))
      ≤ 2 ^ 12 * (1 + (n : ℝ) * h) * (1 + Real.log (2 + (n : ℝ))) := by
  set A : ℝ := (n : ℝ) * h with hA
  set L : ℝ := Real.log (2 + (n : ℝ)) with hL
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  have hkey1 : s * (2 * (n : ℝ)) ≤ 64 * A := by
    have h1 : s * (2 * (n : ℝ)) ≤ (32 * h) * (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hs32 (by positivity)
    have h2 : (32 * h) * (2 * (n : ℝ)) = 64 * A := by rw [hA]; ring
    linarith [h1, h2]
  have hkey2 : s * (11 * (1 + A) * (1 + L) / h) ≤ 352 * (1 + A) * (1 + L) := by
    have h1 : s * (11 * (1 + A) * (1 + L) / h) ≤ (32 * h) * (11 * (1 + A) * (1 + L) / h) :=
      mul_le_mul_of_nonneg_right hs32 (by positivity)
    have h2 : (32 * h) * (11 * (1 + A) * (1 + L) / h) = 352 * (1 + A) * (1 + L) := by
      field_simp
      ring
    linarith [h1, h2]
  have hkey3 : s * (5 * (1 + A) / ((1 / 20 : ℝ) * h)) ≤ 3200 * (1 + A) := by
    have h1 : s * (5 * (1 + A) / ((1 / 20 : ℝ) * h))
        ≤ (32 * h) * (5 * (1 + A) / ((1 / 20 : ℝ) * h)) :=
      mul_le_mul_of_nonneg_right hs32 (by positivity)
    have h2 : (32 * h) * (5 * (1 + A) / ((1 / 20 : ℝ) * h)) = 3200 * (1 + A) := by
      field_simp
      ring
    linarith [h1, h2]
  have hsplit : s * (2 * (n : ℝ) + 11 * (1 + A) * (1 + L) / h
        + 5 * (1 + A) / ((1 / 20 : ℝ) * h))
      = s * (2 * (n : ℝ)) + s * (11 * (1 + A) * (1 + L) / h)
        + s * (5 * (1 + A) / ((1 / 20 : ℝ) * h)) := by ring
  rw [hsplit]
  have hfin : 64 * A + 352 * (1 + A) * (1 + L) + 3200 * (1 + A)
      ≤ 4096 * (1 + A) * (1 + L) := by
    have h1 : 64 * A ≤ 64 * (1 + A) * (1 + L) := by nlinarith [hA0, hL0]
    have h2 : 3200 * (1 + A) ≤ 3200 * (1 + A) * (1 + L) := by nlinarith [hA0, hL0]
    linarith [h1, h2]
  have h4096 : (4096 : ℝ) * (1 + A) * (1 + L) = 2 ^ 12 * (1 + A) * (1 + L) := by norm_num
  linarith [hkey1, hkey2, hkey3, hfin, h4096]

theorem walk_sum_tauC_sub_sigma_le {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j : ℕ, j ≤ n → (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ∑ j ∈ Finset.range n,
        ‖Work.Pert.tauC σ α ((Work.Pert.liftF u σ α)^[j] z) - σ‖
      ≤ 2 ^ 12 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) := by
  -- `InF1 α` gives `α ≠ 0`, hence `0 < ‖α‖`
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  -- `‖α‖ ≤ 1/64` from `hα`, `hM`, `hΞ`
  have hM1024 : (1024 : ℝ) ≤ M := by
    have := hM
    norm_num at this ⊢
    exact this
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h32 : (64 : ℝ) ≤ 32 * (M + 2 + Ξ) := by nlinarith [hM1024, hΞ]
    exact le_trans hα (one_div_le_one_div_of_le (by norm_num) h32)
  have hσb : ‖σ‖ ≤ 32 * ‖α‖ :=
    Work.Pert.sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  -- the walk
  set w : ℕ → ℂ := fun j => (Work.Pert.liftF u σ α)^[j] z with hw
  have hwmem : ∀ j : ℕ, j ≤ n → w j ∈ Work.Pert.Qm Ξ α := fun j hj => hwalk j hj
  have hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32 := by
    intro j hj
    have h1 : w (j + 1) = Work.Pert.liftF u σ α (w j) := by
      rw [show w = fun k => (Work.Pert.liftF u σ α)^[k] z from hw]
      exact Function.iterate_succ_apply' _ _ _
    rw [h1]
    exact hNT (w j) (hwmem j (le_of_lt hj))
  -- the gate keeps the walk off the lattice: `dist (α w_j, ℤ) ≥ ‖α‖/20` when nonzero
  have hlat : ∀ j, j < n → 0 < (⨅ k : ℤ, dist (α * w j) (k : ℂ)) →
      (1 / 20) * ‖α‖ ≤ (⨅ k : ℤ, dist (α * w j) (k : ℂ)) := by
    intro j hj hdj
    have hmem : w j ∈ Work.Pert.Qm Ξ α := hwmem j (le_of_lt hj)
    exact Work.Pert.lattice_dist_ge_of_tauC_le hα64 hσ hnorm hu2 (hτQ (w j) hmem)
      (Work.Pert.tauC_norm_le_gate_five hΞ hα64 hσ hnorm hu2 hτQ hNT (w j) hmem) hdj
  -- the two summations
  have hpt : ∀ j, ‖Work.Pert.tauC σ α (w j) - σ‖
      ≤ ‖σ‖ * (2 + (9 / 25) / (⨅ k : ℤ, dist (α * w j) (k : ℂ))) :=
    fun j => Work.Pert.tauC_sub_sigma_norm_le
  have hsum := Work.Pert.sum_two_add_inv_lattice_le (w := w) (α := α) (Ξ := Ξ) (n := n)
    (c₀ := (1 / 20 : ℝ)) hΞ hInF1 (by norm_num) hstep hwmem hlat
  calc ∑ j ∈ Finset.range n, ‖Work.Pert.tauC σ α (w j) - σ‖
      ≤ ∑ j ∈ Finset.range n,
          ‖σ‖ * (2 + (9 / 25) / (⨅ k : ℤ, dist (α * w j) (k : ℂ))) :=
        Finset.sum_le_sum (fun j _ => hpt j)
    _ = ‖σ‖ * ∑ j ∈ Finset.range n,
          (2 + (9 / 25) / (⨅ k : ℤ, dist (α * w j) (k : ℂ))) := by
        rw [Finset.mul_sum]
    _ ≤ ‖σ‖ * (2 * (n : ℝ)
          + 11 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖
          + 5 * (1 + (n : ℝ) * ‖α‖) / ((1 / 20 : ℝ) * ‖α‖)) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg σ)
    _ ≤ 2 ^ 12 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) :=
        final_arith hαpos (norm_nonneg σ) hσb

end

end Work.Pert
