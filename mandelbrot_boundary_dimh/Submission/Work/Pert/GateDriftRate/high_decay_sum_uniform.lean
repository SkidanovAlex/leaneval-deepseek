import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.gate_geom_facts
import Submission.Work.Pert.walk_gate_mono
import Submission.Work.Pert.layer_cake_sum
import Submission.Work.Pert.geom_exp_sum_le
import Submission.Work.Pert.GateDriftRate.gate_high_im_pos
import Submission.Work.Pert.GateDriftRate.gate_high_t_lb
import Submission.Work.Pert.GateDriftRate.walk_gate_H_im_drift

/-!
# PERT · `Work.Pert.GateDriftRate.high_decay_sum_uniform`

The high-regime decay sum of Shishikura §4.2 in the *uniform in `Ξ`* form needed by the drift
estimate for the perturbed coordinate `Work.Pert.liftF u σ α`.

For a `1/32`-near-translation walk `w` (`‖w_{j+1} - (w_j + 1)‖ ≤ 1/32`) in the lower gate
`Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` one has, **independently of the gate width `Ξ` and of the length
`n` of the walk**, the bound

  `‖α‖ * ∑_{j<n, 1 ≤ Im (α w_j)} exp (-2π Im (α w_j)) ≤ 2 ^ 6`      (for `‖α‖ ≤ 1/64`).

## Structure

* `high_decay_sum_core` is the analytic core, **sharp in the `Ξ`-dependence**: writing
  `a = Re α > |Im α|`, the gate geometry (`Work.Pert.gate_geom_facts`) plus the walk
  monotonicity (`Work.Pert.walk_gate_mono`) give, on the contributing set
  `J = {j < n : 1 ≤ Im (α w_j)}`,

    * `J` lies in the upper half plane: `Work.Pert.GateDriftRate.gate_high_im_pos`,
    * `t_j := Im (α w_j) ≥ ((a - b)/2) H_j + (a Ξ - 1)` with `H_j = |Im w_j| - Re w_j - Ξ`,
      `b = Im α`: `Work.Pert.GateDriftRate.gate_high_t_lb`,
    * `H_{j+1} ≤ H_j - 15/16` and `|Im w_{j+1} - Im w_j| ≤ 1/32`: telescoped for arbitrary
      `i ≤ j` by `Work.Pert.GateDriftRate.walk_gate_H_im_drift`.

  Then two regimes are treated separately: if `b > a/2` the level `t_j` grows at rate
  `(29b - a)/32 ≥ 27a/64 ≥ 0` and `Work.Pert.geom_exp_sum_le` bounds the geometric tail; if
  `b ≤ a/2` the discrete layer cake `Work.Pert.layer_cake_sum` (with `c = (a-b)/2 ≥ a/4`, using
  the `15/16`-separation of the ladder `H_j`) bounds the sum.  Both give

  `∑_{j ∈ J} exp (-2π t_j) ≤ exp (-2π max 1 (aΞ - 1)) * (4 + 20/a)`.

* `high_decay_sum_uniform` then multiplies by `‖α‖ ≤ 2a` (`a ≥ |b|` gives `‖α‖ ≤ √2 a`), so the
  weighted sum is at most `exp (-2π max 1 (aΞ-1)) * (8a + 40) ≤ 8a + 40 ≤ 8/64 + 40 ≤ 2^6`:
  the `1/a` in the core is exactly what the factor `a` in `‖α‖ ≤ 2 a` pays for.
-/

namespace Work.Pert.GateDriftRate

open Complex
open scoped BigOperators

set_option maxHeartbeats 8000000

/-- **The analytic core of the high-regime decay sum**, sharp in `Ξ`: the whole sum is bounded by
`exp (-(2π max 1 (Re α · Ξ - 1))) * (4 + 20 / Re α)` — note the absence of any additive `Ξ`-term.
The hypotheses are exactly those of `Work.Pert.high_decay_sum_le`, whose proof this is (stopped at
the sharp intermediate bound instead of multiplying by `‖α‖`). -/
theorem high_decay_sum_core {Ξ : ℝ} {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hstep : ∀ j < n, ‖w (j+1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * w j).im then Real.exp (-(2 * Real.pi * (α * w j).im)) else 0))
      ≤ Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) * (4 + 20 / α.re) := by
  classical
  -- ==================== 0.  Basic facts about `α` ====================
  have ha_pos : 0 < α.re := by
    have h := hInF1
    rw [MandelDim.InF1] at h
    have h2 := abs_nonneg α.im
    linarith
  have hb_abs : |α.im| < α.re := hInF1

  -- ==================== 1.  delegated gate / walk facts ====================
  have hGateH : ∀ j ≤ n, 0 < |(w j).im| - (w j).re - Ξ :=
    fun j hj => (gate_geom_facts hInF1 (hgate j hj)).2.2.2.2.1
  have hwalk := walk_gate_mono (Ξ := Ξ) (w := w) (n := n) hstep
  have hHstep : ∀ j < n,
      |(w (j + 1)).im| - (w (j + 1)).re - Ξ ≤ |(w j).im| - (w j).re - Ξ - 15 / 16 := hwalk.2.2.1

  -- ==================== 2.  the index set of high-regime points ====================
  set J : Finset ℕ := (Finset.range n).filter (fun j => 1 ≤ (α * w j).im) with hJdef
  have hJmem : ∀ j, j ∈ J ↔ (j < n ∧ 1 ≤ (α * w j).im) := by
    intro j; rw [hJdef]; simp [Finset.mem_filter, Finset.mem_range]
  have hsum_eq : (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * w j).im then Real.exp (-(2 * Real.pi * (α * w j).im)) else 0))
      = ∑ j ∈ J, Real.exp (-(2 * Real.pi * (α * w j).im)) := by
    rw [hJdef, Finset.sum_filter]
  have hHpos : ∀ j ≤ n, 0 ≤ |(w j).im| - (w j).re - Ξ := fun j hj => le_of_lt (hGateH j hj)

  -- ==================== 3.  contributing points have positive imaginary part ==========
  have hy_pos : ∀ j ∈ J, 0 < (w j).im := by
    intro j hj
    obtain ⟨hjlt, htj⟩ := (hJmem j).mp hj
    exact gate_high_im_pos hΞ hInF1 (hgate j (le_of_lt hjlt)) htj

  -- ==================== 4.  the key lower bound for `t j` ====================
  have ht_lb : ∀ j ∈ J,
      (α.re - α.im) / 2 * (|(w j).im| - (w j).re - Ξ) + (α.re * Ξ - 1) ≤ (α * w j).im := by
    intro j hj
    obtain ⟨hjlt, _htj⟩ := (hJmem j).mp hj
    exact gate_high_t_lb hInF1 (hgate j (le_of_lt hjlt)) (hy_pos j hj)

  -- ==================== 5.  the sum bound ====================
  have hsum_bound : ∑ j ∈ J, Real.exp (-(2 * Real.pi * (α * w j).im))
      ≤ Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) * (4 + 20 / α.re) := by
    by_cases hb2 : α.re / 2 < α.im
    · -- #### geometric regime
      have hr : 0 < (29 * α.im - α.re) / 32 := by linarith
      rcases Finset.eq_empty_or_nonempty J with hJemp | hJne
      · rw [hJemp]; simp only [Finset.sum_empty]; positivity
      · set j0 := J.min' hJne with hj0def
        have hj0mem : j0 ∈ J := Finset.min'_mem J hJne
        have hj0le : ∀ j ∈ J, j0 ≤ j := fun j hj => Finset.min'_le J j hj
        have hj0n : j0 < n := ((hJmem j0).mp hj0mem).1
        have ht0 : max 1 (α.re * Ξ - 1) ≤ (α * w j0).im := by
          have h1 := ((hJmem j0).mp hj0mem).2
          have h2 := ht_lb j0 hj0mem
          have h3 : 0 ≤ |(w j0).im| - (w j0).re - Ξ := hHpos j0 (le_of_lt hj0n)
          have h4 : α.re * Ξ - 1 ≤ (α * w j0).im := by
            nlinarith [h2, h3, hb_abs, le_abs_self α.im]
          exact max_le h1 h4
        have hdriftAll := walk_gate_H_im_drift (Ξ := Ξ) (w := w) (n := n) hstep
        have him_drift := hdriftAll.1
        have hH_drift := hdriftAll.2
        have hdrift : ∀ j ∈ J, (α * w j0).im + (29 * α.im - α.re) / 32 * ((j : ℝ) - j0)
            ≤ (α * w j).im := by
          intro j hj
          have hy := hy_pos j hj
          have hy0 := hy_pos j0 hj0mem
          have hj0lej : j0 ≤ j := hj0le j hj
          have hjn : j ≤ n := le_of_lt ((hJmem j).mp hj).1
          have himj : (α * w j).im
              = (α.re + α.im) * (w j).im - α.im * (Ξ + (|(w j).im| - (w j).re - Ξ)) := by
            rw [Complex.mul_im, abs_of_pos hy]; ring
          have him0 : (α * w j0).im
              = (α.re + α.im) * (w j0).im - α.im * (Ξ + (|(w j0).im| - (w j0).re - Ξ)) := by
            rw [Complex.mul_im, abs_of_pos hy0]; ring
          have hy1 : (w j).im - (w j0).im ≥ -(((j - j0 : ℕ) : ℝ) / 32) := by
            have h := him_drift j0 j hj0lej hjn
            linarith [neg_abs_le ((w j).im - (w j0).im)]
          have hH1 : |(w j).im| - (w j).re - Ξ
              ≤ (|(w j0).im| - (w j0).re - Ξ) - 15 * ((j - j0 : ℕ) : ℝ) / 16 :=
            hH_drift j0 j hj0lej hjn
          have hcast : ((j : ℝ) - j0) = ((j - j0 : ℕ) : ℝ) := (Nat.cast_sub hj0lej).symm
          rw [himj, him0, hcast]
          nlinarith [hy1, hH1]
        have hstep1 : ∑ j ∈ J, Real.exp (-(2 * Real.pi * (α * w j).im))
            ≤ Real.exp (-(2 * Real.pi * (α * w j0).im)) *
              ∑ j ∈ J, (Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) ^ (j - j0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j hj
          have hd := hdrift j hj
          have hcast : ((j - j0 : ℕ) : ℝ) = (j : ℝ) - j0 := Nat.cast_sub (hj0le j hj)
          have hexp : Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32))) ^ (j - j0)
              = Real.exp (((j : ℝ) - j0) * (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            rw [hcast]
          rw [hexp, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have heq : -(2 * Real.pi * (α * w j0).im)
              + ((j : ℝ) - j0) * (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))
              = -(2 * Real.pi * ((α * w j0).im + (29 * α.im - α.re) / 32 * ((j : ℝ) - j0))) := by
            ring
          rw [heq]
          nlinarith [hd, Real.pi_pos]
        have hinj : ∀ x ∈ J, ∀ y ∈ J, x - j0 = y - j0 → x = y := by
          intro x hx y hy h
          have hx' : j0 ≤ x := hj0le x hx
          have hy' : j0 ≤ y := hj0le y hy
          omega
        have hreindex : ∑ j ∈ J, (Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) ^ (j - j0)
            ≤ ∑ k ∈ Finset.range n,
                (Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) ^ k := by
          rw [← Finset.sum_image hinj]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hk
            rw [Finset.mem_range]
            exact lt_of_le_of_lt (Nat.sub_le j j0) ((hJmem j).mp hjJ).1
          · intro k hk hks
            positivity
        have hgeom0 := geom_exp_sum_le (r := (29 * α.im - α.re) / 32) (η := 0) hr n
        have hgeom0' : ∑ k ∈ Finset.range n,
              Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32 * (k : ℝ))))
            ≤ 1 + 1 / (2 * Real.pi * ((29 * α.im - α.re) / 32)) := by
          simpa using hgeom0
        have hgeom : ∑ k ∈ Finset.range n,
              (Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) ^ k
            ≤ 1 + 1 / (2 * Real.pi * ((29 * α.im - α.re) / 32)) := by
          refine le_trans ?_ hgeom0'
          apply Finset.sum_le_sum
          intro k hk
          rw [← Real.exp_nat_mul]
          exact le_of_eq (by congr 1; ring)
        have hfin1 : (1 : ℝ) + 1 / (2 * Real.pi * ((29 * α.im - α.re) / 32)) ≤ 1 + 20 / α.re := by
          have h1 : (29 * α.im - α.re) / 32 ≥ 27 * α.re / 64 := by linarith
          have hpi := Real.pi_pos
          have h2 : 2 * Real.pi * ((29 * α.im - α.re) / 32) ≥ 2 * Real.pi * (27 * α.re / 64) := by
            nlinarith
          have h3 : 1 / (2 * Real.pi * ((29 * α.im - α.re) / 32))
              ≤ 1 / (2 * Real.pi * (27 * α.re / 64)) := by
            apply one_div_le_one_div_of_le
            · nlinarith
            · exact h2
          have h4 : 1 / (2 * Real.pi * (27 * α.re / 64)) ≤ 20 / α.re := by
            rw [div_le_div_iff₀ (by nlinarith) ha_pos]
            have := Real.pi_gt_three
            nlinarith
          linarith
        calc ∑ j ∈ J, Real.exp (-(2 * Real.pi * (α * w j).im))
            ≤ Real.exp (-(2 * Real.pi * (α * w j0).im)) *
                ∑ j ∈ J, (Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) ^ (j - j0) :=
              hstep1
          _ ≤ Real.exp (-(2 * Real.pi * (α * w j0).im)) *
                (∑ k ∈ Finset.range n,
                  (Real.exp (-(2 * Real.pi * ((29 * α.im - α.re) / 32)))) ^ k) :=
              mul_le_mul_of_nonneg_left hreindex (Real.exp_pos _).le
          _ ≤ Real.exp (-(2 * Real.pi * (α * w j0).im)) *
                (1 + 1 / (2 * Real.pi * ((29 * α.im - α.re) / 32))) :=
              mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
          _ ≤ Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) * (4 + 20 / α.re) := by
              have h1 : Real.exp (-(2 * Real.pi * (α * w j0).im))
                  ≤ Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) := by
                apply Real.exp_le_exp.mpr
                nlinarith [ht0, Real.pi_pos]
              have h2 : (1 : ℝ) + 1 / (2 * Real.pi * ((29 * α.im - α.re) / 32))
                  ≤ 4 + 20 / α.re := by
                have := hfin1
                linarith
              exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    · -- #### layer-cake regime
      push_neg at hb2
      have hc : 0 < (α.re - α.im) / 2 := by linarith
      have hβ : -1 ≤ α.re * Ξ - 1 := by nlinarith [ha_pos, hΞ]
      set t' : ℕ → ℝ := fun j =>
        if j ∈ J then (α * w j).im
        else max 1 ((α.re - α.im) / 2 * (|(w j).im| - (w j).re - Ξ) + (α.re * Ξ - 1)) with ht'def
      have ht1' : ∀ j ≤ n, 1 ≤ t' j := by
        intro j hj
        by_cases h : j ∈ J
        · rw [show t' j = (α * w j).im from if_pos h]
          exact ((hJmem j).mp h).2
        · rw [show t' j = max 1 ((α.re - α.im) / 2 * (|(w j).im| - (w j).re - Ξ)
              + (α.re * Ξ - 1)) from if_neg h]
          exact le_max_left _ _
      have ht2' : ∀ j ≤ n,
          (α.re - α.im) / 2 * (|(w j).im| - (w j).re - Ξ) + (α.re * Ξ - 1) ≤ t' j := by
        intro j hj
        by_cases h : j ∈ J
        · rw [show t' j = (α * w j).im from if_pos h]
          exact ht_lb j h
        · rw [show t' j = max 1 ((α.re - α.im) / 2 * (|(w j).im| - (w j).re - Ξ)
              + (α.re * Ξ - 1)) from if_neg h]
          exact le_max_right _ _
      have hlc := layer_cake_sum (c := (α.re - α.im) / 2) (β := α.re * Ξ - 1) hc hβ
        hHpos hHstep ht1' ht2' J (fun j hj => le_of_lt ((hJmem j).mp hj).1)
      have hcongr : ∑ j ∈ J, Real.exp (-(2 * Real.pi * t' j))
          = ∑ j ∈ J, Real.exp (-(2 * Real.pi * (α * w j).im)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show t' j = (α * w j).im from if_pos hj]
      rw [hcongr] at hlc
      refine le_trans hlc ?_
      have h5 : 5 / ((α.re - α.im) / 2) ≤ 20 / α.re := by
        rw [div_le_div_iff₀ hc ha_pos]
        linarith
      have h4 : (4 : ℝ) + 5 / ((α.re - α.im) / 2) ≤ 4 + 20 / α.re := by linarith
      exact mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le

  rw [hsum_eq]
  exact hsum_bound

/-- **Uniform high-regime decay sum.**  For a `1/32`-near-translation walk in the gate `Qm Ξ α`
with `‖α‖ ≤ 1/64`, the weighted high-regime decay sum is bounded by the absolute constant `2 ^ 6`,
uniformly in the gate width `Ξ` and in the length `n` of the walk. -/
theorem high_decay_sum_uniform {Ξ : ℝ} {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    ‖α‖ * (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * w j).im then Real.exp (-(2 * Real.pi * (α * w j).im)) else 0))
      ≤ 2 ^ 6 := by
  have hcore := high_decay_sum_core (Ξ := Ξ) (α := α) (w := w) (n := n) hΞ hInF1 hstep hgate
  -- ### elementary facts about `α` (`InF1 α` is `|Im α| < Re α`)
  have hb_abs : |α.im| < α.re := hInF1
  have ha_pos : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hb_abs
  have hnorm_sq : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hnorm_le : ‖α‖ ≤ 2 * α.re := by
    have h2 : ‖α‖ ^ 2 ≤ (2 * α.re) ^ 2 := by
      rw [hnorm_sq]
      nlinarith [hb_abs, le_abs_self α.im, neg_abs_le α.im, abs_nonneg α.im, ha_pos, sq_abs α.im]
    have h3 : ‖α‖ ^ 2 = ‖α‖ * ‖α‖ := by ring
    nlinarith [norm_nonneg α, ha_pos, h2]
  -- ### the exponential weight is at most `1`, because `max 1 (aΞ - 1) ≥ 1`
  have hexp : Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : (1 : ℝ) ≤ max 1 (α.re * Ξ - 1) := le_max_left _ _
    nlinarith [Real.pi_pos]
  -- ### `‖α‖ * (4 + 20/a) ≤ 8a + 40`, because `‖α‖ ≤ 2a`
  have hpos4 : 0 < 4 + 20 / α.re := by positivity
  have hfac : ‖α‖ * (4 + 20 / α.re) ≤ 8 * α.re + 40 := by
    have h3 : ‖α‖ * (4 + 20 / α.re) ≤ 2 * α.re * (4 + 20 / α.re) :=
      mul_le_mul_of_nonneg_right hnorm_le (le_of_lt hpos4)
    have h4 : 2 * α.re * (4 + 20 / α.re) = 8 * α.re + 40 := by
      field_simp
      ring
    linarith [h3, h4]
  have hfacnn : 0 ≤ ‖α‖ * (4 + 20 / α.re) := by positivity
  -- ### the resulting constant is below `2 ^ 6` (`a ≤ ‖α‖ ≤ 1/64`)
  have hconst : 8 * α.re + 40 ≤ 2 ^ 6 := by
    have h2 : α.re ≤ 1 / 64 := le_trans (Complex.re_le_norm α) hα64
    have h3 : 8 * α.re ≤ 1 / 8 := by linarith
    norm_num
    linarith
  calc ‖α‖ * (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * w j).im then Real.exp (-(2 * Real.pi * (α * w j).im)) else 0))
      ≤ ‖α‖ * (Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) * (4 + 20 / α.re)) :=
        mul_le_mul_of_nonneg_left hcore (norm_nonneg α)
    _ = Real.exp (-(2 * Real.pi * max 1 (α.re * Ξ - 1))) * (‖α‖ * (4 + 20 / α.re)) := by ring
    _ ≤ 1 * (8 * α.re + 40) := mul_le_mul hexp hfac hfacnn (by norm_num)
    _ = 8 * α.re + 40 := one_mul _
    _ ≤ 2 ^ 6 := hconst

end Work.Pert.GateDriftRate
