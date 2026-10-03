import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.norm_endDefect_le
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.liftF_defect_le_tau_explicit
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.lattice_sum_le
import Submission.Work.Pert.gate_walk_legal
import Submission.Work.Pert.norm_div_one_sub_exp_neg_le
import Submission.Work.Pert.defect_sub_endDefect_le
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.gate_walk_sum_y_le
import Submission.Work.Pert.sigma_le_half_rr
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

/-!
# Reduction layer for `gate_walk_drift_explicit`

The exact algebra of the defect `d w = liftF u σ α w - (w + 1)`.

Write `τ := tauC σ α w = σ/(1-E)`, `E := exp (-2πi α w)`, `y := τ - σ`, `A := 1 + σ·u σ`.  Then

* `d w = (1/(2πiα)) (log (1 - sfun) - 2πiα)`;
* `1 - sfun = (1 + u τ · y)/(1 + τ u τ)`;
* `y = τ · E`  (so `‖y‖ ≤ rr ‖E‖` by `hτQ`);
* `A (1 - sfun) - 1 = (σ (u σ - u τ) + σ u σ u τ y)/(1 + τ u τ)`;
* `d w - endDefect u σ α = (1/(2πiα)) log (A (1 - sfun))`.

These are the identities on which the estimate `‖Σ_{j<n}(d w_j - D(σ))‖ ≤ C (1+1/rr) Σ‖y_j‖`
rests; see `NOTES_gate_walk_drift_SESSION15b.md` for the full mechanism.
-/

/-- The defect in terms of `sfun`: `d w = (1/(2πiα))·(log (1 - sfun) - 2πiα)`. -/
theorem liftF_sub_one_eq {u : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0) :
    liftF u σ α w - (w + 1)
      = (1 / (2 * Real.pi * Complex.I * α)) *
        (Complex.log (1 - sfun u σ α w) - 2 * Real.pi * Complex.I * α) := by
  have h2 : (2 * Real.pi * Complex.I * α) ≠ 0 := by
    simp [hα, Real.pi_ne_zero, Complex.I_ne_zero]
  unfold liftF
  field_simp
  ring

/-- `1 - sfun` as a rational function of `τ = tauC σ α w`. -/
theorem one_sub_sfun_eq {u : ℂ → ℂ} {σ α w : ℂ}
    (h : 1 + tauC σ α w * u (tauC σ α w) ≠ 0) :
    1 - sfun u σ α w
      = (1 + u (tauC σ α w) * (tauC σ α w - σ)) / (1 + tauC σ α w * u (tauC σ α w)) := by
  have h' : 1 + u (tauC σ α w) * tauC σ α w ≠ 0 := by simpa [mul_comm] using h
  unfold sfun
  rw [eq_div_iff h]
  field_simp
  ring

/-- `τ - σ = τ · E`, the Möbius form of the level `E = exp (-2πi α w)`. -/
theorem tauC_sub_sigma_eq {σ α w : ℂ} (hσ : σ ≠ 0)
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1) :
    tauC σ α w - σ = tauC σ α w * Complex.exp (-(2 * Real.pi * Complex.I * α * w)) := by
  have hExp := exp_eq_tauC σ α w hσ hE
  have hτ : tauC σ α w ≠ 0 := by
    rw [tauC, div_ne_zero_iff]
    refine ⟨hσ, ?_⟩
    intro h1
    exact hE (by rw [sub_eq_zero] at h1; exact h1.symm)
  rw [hExp]
  field_simp

/-- **(key normalisation)** `1 - endDefect` equals the logarithm of `A (1 - sfun)`, where
`A = 1 + σ u σ`:  hence the *deviation of the defect from its lower-end value* is
`(1/(2πiα)) log (A (1 - sfun))`, a quantity which vanishes at `τ = σ`. -/
theorem A_mul_one_sub_sfun_sub_one {u : ℂ → ℂ} {σ α w : ℂ}
    (h : 1 + tauC σ α w * u (tauC σ α w) ≠ 0) :
    (1 + σ * u σ) * (1 - sfun u σ α w) - 1
      = (σ * (u σ - u (tauC σ α w))
          + σ * u σ * u (tauC σ α w) * (tauC σ α w - σ))
        / (1 + tauC σ α w * u (tauC σ α w)) := by
  have h' : 1 + u (tauC σ α w) * tauC σ α w ≠ 0 := by simpa [mul_comm] using h
  rw [one_sub_sfun_eq h]
  field_simp
  ring

/-- The defect minus its lower-end value, in terms of the logarithm of `A (1 - sfun)`. -/
theorem defect_sub_endDefect_eq {u : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0) :
    liftF u σ α w - (w + 1) - endDefect u σ α
      = (1 / (2 * Real.pi * Complex.I * α))
        * (Complex.log (1 - sfun u σ α w)
            - Complex.log (1 / (1 + σ * u σ))) := by
  have h2 : (2 * Real.pi * Complex.I * α) ≠ 0 := by
    simp [hα, Real.pi_ne_zero, Complex.I_ne_zero]
  rw [liftF_sub_one_eq hα, endDefect]
  field_simp
  ring

/-! ## The telescoping identity -/

/-- `F^[n] z - (z+n) = ∑_{j<n} (F (F^[j] z) - (F^[j] z + 1))`: the drift is the sum of the
successive defects of the near-translation. -/
theorem iterate_drift_eq_sum {u : ℂ → ℂ} {σ α : ℂ} {z : ℂ} (n : ℕ) :
    (liftF u σ α)^[n] z - (z + (n : ℂ))
      = ∑ j ∈ Finset.range n,
          ((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, Function.iterate_succ_apply']
    push_cast
    ring

/-! ## The per-step bound `‖d - D(σ)‖ ≤ 2^11 (1+1/rr) ‖τ - σ‖` -/

/-- **The per-step bound.**  The defect `d w = F_f w - (w+1)` differs from its lower-end value
`D(σ) = endDefect u σ α` by at most `2^11 (1+1/rr) ‖τ_f w - σ‖`.  For `‖τ_f w - σ‖ ≤ 1/4` this
is `Work.Pert.defect_sub_endDefect_le`; otherwise the crude bound `‖d w‖ ≤ 1/32` together with
`‖D(σ)‖ ≤ 100(1+1/rr)‖α‖ ≤ 100(1+1/rr)/64` wins because `2^11(1+1/rr)` is so large. -/
theorem defect_sub_endDefect_le_full {rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {w : ℂ}
    (hrr : 0 < rr) (hα64 : ‖α‖ ≤ 1 / 64) (hα0 : α ≠ 0)
    (hσhalf : ‖σ‖ ≤ rr / 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hA : 0 < (1 + σ * u σ).re)
    (hτ : tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hd : ‖liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    ‖liftF u σ α w - (w + 1) - endDefect u σ α‖
      ≤ 2 ^ 11 * (1 + 1 / rr) * ‖tauC σ α w - σ‖ := by
  have hD : ‖endDefect u σ α‖ ≤ 100 * (1 + 1 / rr) * ‖α‖ := by
    have h := norm_endDefect_le hrr hα64 hα0 hu hu2 hσhalf hnorm
    linarith [h]
  have h1rr : (1 : ℝ) ≤ 1 + 1 / rr := by
    have : 0 < 1 / rr := by positivity
    linarith
  have hcoef0 : (0 : ℝ) ≤ 2 ^ 11 * (1 + 1 / rr) := by positivity
  by_cases hy : ‖tauC σ α w - σ‖ ≤ 1 / 4
  · -- the analytic case: `defect_sub_endDefect_le`
    exact defect_sub_endDefect_le hrr hα64 hα0 hu hu2 hσhalf hτ hd hy hA
  · -- the crude case: `‖d - D‖ ≤ 1/32 + ‖D‖` and `‖τ - σ‖` is not small
    push_neg at hy
    have h1 : ‖liftF u σ α w - (w + 1) - endDefect u σ α‖
        ≤ ‖liftF u σ α w - (w + 1)‖ + ‖endDefect u σ α‖ :=
      norm_sub_le _ _
    have hD' : ‖endDefect u σ α‖ ≤ 100 * (1 + 1 / rr) / 64 := by
      have h : 100 * (1 + 1 / rr) * ‖α‖ ≤ 100 * (1 + 1 / rr) * (1 / 64) :=
        mul_le_mul_of_nonneg_left hα64 (by positivity)
      linarith [hD, h]
    have hbig : 2 ^ 11 * (1 + 1 / rr) * (1 / 4) ≤ 2 ^ 11 * (1 + 1 / rr) * ‖tauC σ α w - σ‖ :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) hcoef0
    have hkey : (1 : ℝ) / 32 + 100 * (1 + 1 / rr) / 64 ≤ 2 ^ 11 * (1 + 1 / rr) * (1 / 4) := by
      nlinarith [h1rr]
    linarith [h1, hd, hD', hbig, hkey, le_of_lt hy]

theorem gate_walk_drift_explicit {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j : ℕ, j ≤ n → (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ‖(Work.Pert.liftF u σ α)^[n] z - (z + (n : ℂ))‖
      ≤ 2 ^ 30 * (1 + 1 / rr) * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) := by
  -- ## 0.  the basic constants
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h1 : (64 : ℝ) ≤ 32 * (M + 2 + Ξ) := by
      have h2 : (1024 : ℝ) ≤ M := by
        have h3 : (2 : ℝ) ^ 10 ≤ M := hM
        norm_num at h3 ⊢
        exact h3
      nlinarith [h2, hΞ]
    exact le_trans hα (one_div_le_one_div_of_le (by norm_num) h1)
  have hσ32 : ‖σ‖ ≤ 32 * ‖α‖ :=
    sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  have hσhalf : ‖σ‖ ≤ rr / 2 := sigma_le_half_rr hΞ hrr hM hInF1 hα hτQ
  -- `(1 + σ u σ).re > 0`
  have hA0 : 0 < (1 + σ * u σ).re := by
    have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
      rw [Metric.mem_ball, dist_zero_right]; linarith [hσhalf, hrr]
    have huσ2 : ‖u σ‖ ≤ 2 := (hu2 σ hσmem).2
    have h1 : ‖σ * u σ‖ < 1 := by
      rw [norm_mul]
      have h2 : ‖σ‖ * ‖u σ‖ ≤ (32 * ‖α‖) * 2 :=
        mul_le_mul hσ32 huσ2 (norm_nonneg _) (by positivity)
      have h3 : (32 * ‖α‖) * 2 < 1 := by
        have h4 : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)) := hα
        have h5 : (1024 : ℝ) ≤ M := by
          have h6 : (2 : ℝ) ^ 10 ≤ M := hM
          norm_num at h6 ⊢
          exact h6
        have h6 : 64 * ‖α‖ ≤ 64 * (1 / (32 * (M + 2 + Ξ))) :=
          mul_le_mul_of_nonneg_left h4 (by norm_num)
        have h7 : 64 * (1 / (32 * (M + 2 + Ξ))) < 1 := by
          rw [mul_one_div, div_lt_one (by nlinarith [h5, hΞ])]
          nlinarith [h5, hΞ]
        linarith
      linarith
    have h2 : (1 + σ * u σ).re = 1 + (σ * u σ).re := by simp
    have h3 : |(σ * u σ).re| ≤ ‖σ * u σ‖ := Complex.abs_re_le_norm _
    rw [h2]; linarith [(abs_le.mp h3).1, h1]
  -- ## 1.  telescoping
  rw [iterate_drift_eq_sum (u := u) (σ := σ) (α := α) (z := z) n]
  have hsplit : (∑ j ∈ Finset.range n,
        ((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1)))
      = ∑ j ∈ Finset.range n,
          (endDefect u σ α
            + (((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1))
                - endDefect u σ α)) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit]
  -- ## 2.  the two estimates
  have hDnorm : ‖endDefect u σ α‖ ≤ 100 * (1 + 1 / rr) * ‖α‖ := by
    have h := norm_endDefect_le hrr hα64 hαne hu hu2 hσhalf hnorm
    linarith [h]
  have hstep : ∀ j ∈ Finset.range n,
      ‖((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1))
          - endDefect u σ α‖
        ≤ 2 ^ 11 * (1 + 1 / rr) * ‖tauC σ α ((liftF u σ α)^[j] z) - σ‖ := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact defect_sub_endDefect_le_full hrr hα64 hαne hσhalf hnorm hu hu2 hA0
      (hτQ _ (hwalk j (le_of_lt hj))) (hNT _ (hwalk j (le_of_lt hj)))
  have hsum' : (∑ j ∈ Finset.range n, ‖tauC σ α ((liftF u σ α)^[j] z) - σ‖) ≤ 2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) :=
    gate_walk_sum_y_le hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT hz hwalk
  -- ## 3.  assembly
  have hΛ0 : 0 ≤ Real.log (2 + (n : ℝ) + ‖z‖) :=
    Real.log_nonneg (by have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
                        have h2 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
                        linarith)
  have hApos : 0 ≤ (n : ℝ) * ‖α‖ := by positivity
  have hr1 : (0 : ℝ) < 1 + 1 / rr := by
    have : 0 < 1 / rr := by positivity
    linarith
  calc ‖∑ j ∈ Finset.range n,
        (endDefect u σ α
          + (((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1))
              - endDefect u σ α))‖
      ≤ ∑ j ∈ Finset.range n,
          ‖endDefect u σ α
            + (((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1))
                - endDefect u σ α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n,
          (‖endDefect u σ α‖
            + ‖((liftF u σ α) ((liftF u σ α)^[j] z) - ((liftF u σ α)^[j] z + 1))
                - endDefect u σ α‖) :=
        Finset.sum_le_sum (fun j _ => norm_add_le _ _)
    _ ≤ ∑ j ∈ Finset.range n,
          (100 * (1 + 1 / rr) * ‖α‖
            + 2 ^ 11 * (1 + 1 / rr) * ‖tauC σ α ((liftF u σ α)^[j] z) - σ‖) :=
        Finset.sum_le_sum (fun j hj => add_le_add hDnorm (hstep j hj))
    _ = (n : ℝ) * (100 * (1 + 1 / rr) * ‖α‖)
          + 2 ^ 11 * (1 + 1 / rr)
              * ∑ j ∈ Finset.range n, ‖tauC σ α ((liftF u σ α)^[j] z) - σ‖ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        · rw [← Finset.mul_sum]
    _ ≤ (n : ℝ) * (100 * (1 + 1 / rr) * ‖α‖)
          + 2 ^ 11 * (1 + 1 / rr)
              * (2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖)) := by
        gcongr
    _ ≤ 2 ^ 30 * (1 + 1 / rr)
          * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) := by
        have h1 : (n : ℝ) * (100 * (1 + 1 / rr) * ‖α‖)
            = 100 * (1 + 1 / rr) * ((n : ℝ) * ‖α‖) := by ring
        rw [h1]
        have h2 : 2 ^ 11 * (1 + 1 / rr)
              * (2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖))
            = 2 ^ 29 * (1 + 1 / rr)
              * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) := by
          ring
        rw [h2]
        have h3 : (0 : ℝ) ≤ (1 + 1 / rr)
            * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) :=
          mul_nonneg (le_of_lt hr1) (by linarith)
        have h4 : 100 * ((n : ℝ) * ‖α‖)
            ≤ 100 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) := by
          nlinarith [hΛ0]
        nlinarith [h3, h4]


end Work.Pert
