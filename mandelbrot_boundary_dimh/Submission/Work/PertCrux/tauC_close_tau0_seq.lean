import Mathlib
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.Qreg_norm_lower
import Submission.Work.Pert.one_sub_exp_ge_ratio
import Submission.Work.PertCrux.norm_tauC_sub_tau0_le

namespace Work.PertCrux

open Filter
open scoped Topology

/-!
# `Work.PertCrux.tauC_close_tau0_seq`

Uniform (in `w ∈ K`) convergence of the perturbed chart `τ_f = Work.Pert.tauC (σ n) (α n)` to the
unperturbed chart `τ₀ = MandelDim.tau0`, together with a uniform norm bound, along a sequence of
parameters satisfying the normal-form relation `1 - σ n · u n 0 = exp (2πi α n)` with
`α n → 0`, `u n 0 → 1`.

The two inputs are purely local at a point `w ≠ 0` with `‖w‖` bounded below and `2π‖α‖‖w‖` small:

* `norm_tauC_sub_tau0_le`: `‖τ_f w - τ₀ w‖ ≤ 4π‖α‖ + (8π²‖α‖ + 4π‖u₀-1‖)/(π m)` for
  `m ≤ ‖w‖` (Laurent expansion of `1/(1 - e^{-z})` at `z = 0` + the perturbation bound
  `‖σ/α + 2πi‖ ≤ 8π²‖α‖ + 4π‖u₀-1‖`);
* `tauC_norm_le_of_small` below: `‖τ_f w‖ ≤ 8/‖w‖`, from `‖σ‖ ≤ 8π‖α‖` (normal form) and the
  universal bound `‖1 - e^{-2πiαw}‖ ≥ (25/36)·2π‖α‖‖w‖` (`Work.Pert.one_sub_exp_ge_ratio`).

The hypothesis `K ⊆ Qreg (some Ξ') none` gives `Ξ'/2 < ‖w‖` on `K` (`Work.Pert.Qreg_norm_lower`)
and compactness gives `‖w‖ ≤ R'`: only the lower bound is needed for the convergence statement,
only the upper bound for the smallness of `2π‖α‖‖w‖`.
-/

/-- On the disc `2π‖α‖‖w‖ ≤ 1/2` the perturbed chart is bounded by `8/‖w‖`, uniformly in the
direction of `w`: from the normal form `‖σ‖ ≤ 8π‖α‖` and `‖1 - e^{-2πiαw}‖ ≥ (25/36)·2π‖α‖‖w‖`. -/
theorem tauC_norm_le_of_small {σ α u0 w : ℂ} (hα : α ≠ 0) (hw : w ≠ 0)
    (hnorm : 1 - σ * u0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu0 : ‖u0 - 1‖ ≤ 1 / 2) (hαs : 2 * Real.pi * ‖α‖ ≤ 1 / 2)
    (hwu : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2) :
    ‖Work.Pert.tauC σ α w‖ ≤ 8 / ‖w‖ := by
  -- the normal form controls `σ`
  have hαs' : ‖α‖ ≤ 1 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hαs]
  have hσ := (Work.Pert.sigma_alpha_close (u := fun _ : ℂ => u0) hα hαs' hu0 hnorm).2
  have hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
    have h1 : 8 * Real.pi ^ 2 * ‖α‖ ≤ 2 * Real.pi := by nlinarith [hαs, Real.pi_pos]
    have h2 : 4 * Real.pi * ‖u0 - 1‖ ≤ 2 * Real.pi := by nlinarith [hu0, Real.pi_pos]
    have hsum : 8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖ + 2 * Real.pi ≤ 6 * Real.pi := by
      linarith
    calc ‖σ‖ ≤ ‖α‖ * (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖ + 2 * Real.pi) := hσ
      _ ≤ ‖α‖ * (6 * Real.pi) := mul_le_mul_of_nonneg_left hsum (norm_nonneg α)
      _ ≤ 8 * Real.pi * ‖α‖ := by nlinarith [norm_nonneg α, Real.pi_pos]
  -- the universal lower bound for the denominator
  set u : ℂ := -(2 * Real.pi * Complex.I * α * w) with hu
  have hun : ‖u‖ = 2 * Real.pi * ‖α‖ * ‖w‖ := by
    simp only [hu, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  have hden : (25 / 36 : ℝ) * (2 * Real.pi * ‖α‖ * ‖w‖) ≤ ‖1 - Complex.exp u‖ := by
    have h := Work.Pert.one_sub_exp_ge_ratio (z := u) (by rw [hun]; exact hwu)
    rwa [hun] at h
  have hpos : 0 < (25 / 36 : ℝ) * (2 * Real.pi * ‖α‖ * ‖w‖) := by
    have h1 : 0 < ‖α‖ := norm_pos_iff.mpr hα
    have h2 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  have hτ : Work.Pert.tauC σ α w = σ / (1 - Complex.exp u) := by
    rw [Work.Pert.tauC, hu]
  rw [hτ, norm_div]
  calc ‖σ‖ / ‖1 - Complex.exp u‖
      ≤ ‖σ‖ / ((25 / 36 : ℝ) * (2 * Real.pi * ‖α‖ * ‖w‖)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hpos hden
    _ ≤ (8 * Real.pi * ‖α‖) / ((25 / 36 : ℝ) * (2 * Real.pi * ‖α‖ * ‖w‖)) :=
        div_le_div_of_nonneg_right hσ8 (le_of_lt hpos)
    _ = (144 / 25) / ‖w‖ := by
        have hα0 : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα
        have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
        rw [div_eq_div_iff (by positivity) hw0]
        ring
    _ ≤ 8 / ‖w‖ := div_le_div_of_nonneg_right (by norm_num) (norm_nonneg w)

/-- Arithmetic: the right-hand side of `norm_tauC_sub_tau0_le`, evaluated with `m = Ξ'/2`,
is at most `ε` as soon as `‖α‖ ≤ δ`, `‖u₀-1‖ ≤ δ` and `δ ≤ ε/(8π+2)`, for `Ξ' ≥ 64`. -/
private theorem eps_bound {Ξ' ε δ a b : ℝ} (hΞ' : 64 ≤ Ξ') (hε : 0 < ε)
    (hδ : δ ≤ ε / (8 * Real.pi + 2)) (ha0 : 0 ≤ a) (ha : a ≤ δ) (hb : b ≤ δ) :
    4 * Real.pi * a + (8 * Real.pi ^ 2 * a + 4 * Real.pi * b) / (Real.pi * (Ξ' / 2)) ≤ ε := by
  have hδ0 : 0 ≤ δ := le_trans ha0 ha
  have hden : 0 < Real.pi * (Ξ' / 2) := by positivity
  have hnumle : 8 * Real.pi ^ 2 * a + 4 * Real.pi * b
      ≤ 8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ := by
    nlinarith [Real.pi_pos, ha, hb]
  have step1 : (8 * Real.pi ^ 2 * a + 4 * Real.pi * b) / (Real.pi * (Ξ' / 2))
      ≤ (8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ) / (Real.pi * (Ξ' / 2)) :=
    div_le_div_of_nonneg_right hnumle hden.le
  have h32 : 32 * Real.pi ≤ Real.pi * (Ξ' / 2) := by
    have h : (32 : ℝ) ≤ Ξ' / 2 := by linarith
    calc 32 * Real.pi = Real.pi * 32 := by ring
      _ ≤ Real.pi * (Ξ' / 2) := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  have step2 : (8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ) / (Real.pi * (Ξ' / 2))
      ≤ (8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ) / (32 * Real.pi) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h32
  have hpi32 : 8 * Real.pi + 4 ≤ 32 := by nlinarith [Real.pi_lt_d2]
  have step3 : (8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ) / (32 * Real.pi) ≤ δ := by
    have h : (8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ) / (32 * Real.pi)
        = δ * ((8 * Real.pi + 4) / 32) := by
      rw [show (8 * Real.pi ^ 2 * δ + 4 * Real.pi * δ)
            = δ * (8 * Real.pi ^ 2 + 4 * Real.pi) by ring]
      rw [mul_div_assoc]
      congr 1
      rw [div_eq_div_iff (by positivity : (32 * Real.pi : ℝ) ≠ 0) (by norm_num : (32 : ℝ) ≠ 0)]
      ring
    rw [h]
    have hle : (8 * Real.pi + 4) / 32 ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ) < 32)]
      exact hpi32
    nlinarith [mul_le_mul_of_nonneg_left hle hδ0]
  have h4 : 4 * Real.pi * a ≤ 4 * Real.pi * δ := by nlinarith [Real.pi_pos, ha]
  have hfin : 4 * Real.pi * δ + δ ≤ ε := by
    have h1 : (4 * Real.pi + 1) * δ ≤ (4 * Real.pi + 1) * (ε / (8 * Real.pi + 2)) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h2 : (4 * Real.pi + 1) * (ε / (8 * Real.pi + 2)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi + 2)]
      nlinarith [hε, Real.pi_pos]
    nlinarith [h1, h2]
  linarith [step1, step2, step3, h4, hfin]

theorem tauC_close_tau0_seq {Ξ' : ℝ} (hΞ' : 64 ≤ Ξ') {K : Set ℂ} (hKc : IsCompact K)
    (hKcone : K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none)
    {σ α : ℕ → ℂ} {u : ℕ → ℂ → ℂ}
    (hInF1 : ∀ n, MandelDim.InF1 (α n))
    (hnorm : ∀ n, 1 - σ n * u n 0 = Complex.exp (2 * Real.pi * Complex.I * (α n)))
    (hα0 : Filter.Tendsto (fun n => ‖α n‖) Filter.atTop (nhds 0))
    (hu0 : Filter.Tendsto (fun n => ‖u n 0 - 1‖) Filter.atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    (∀ᶠ n in Filter.atTop, ∀ w ∈ K,
        ‖Work.Pert.tauC (σ n) (α n) w - MandelDim.tau0 w‖ ≤ ε) ∧
      (∀ᶠ n in Filter.atTop, ∀ w ∈ K,
        ‖Work.Pert.tauC (σ n) (α n) w‖ ≤ 8 * Real.pi / Ξ') := by
  have hΞ'pos : 0 < Ξ' := by linarith
  -- `K` is bounded
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ w ∈ K, ‖w‖ ≤ R := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hKc.isBounded
    exact ⟨r, fun w hw => by
      have h := hr hw
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h⟩
  set R' : ℝ := max R 1 with hR'def
  have hR'pos : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hKle : ∀ w ∈ K, ‖w‖ ≤ R' := fun w hw => le_trans (hR w hw) (le_max_left R 1)
  -- the smallness threshold
  set δ : ℝ := min (ε / (8 * Real.pi + 2)) (1 / (4 * Real.pi * R' + 1)) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ_eps : δ ≤ ε / (8 * Real.pi + 2) := min_le_left _ _
  have hδ_inv : δ ≤ 1 / (4 * Real.pi * R' + 1) := min_le_right _ _
  have hδR : δ * (4 * Real.pi * R' + 1) ≤ 1 := by
    have hpos : 0 < 4 * Real.pi * R' + 1 := by positivity
    calc δ * (4 * Real.pi * R' + 1)
        ≤ (1 / (4 * Real.pi * R' + 1)) * (4 * Real.pi * R' + 1) :=
          mul_le_mul_of_nonneg_right hδ_inv hpos.le
      _ = 1 := by field_simp
  have hδhalf : 2 * Real.pi * δ * R' ≤ 1 / 2 := by nlinarith [hδR, Real.pi_pos]
  have hδαs : 2 * Real.pi * δ ≤ 1 / 2 := by
    have hR1 : 1 ≤ R' := le_max_right R 1
    have h2 : 2 * Real.pi * δ ≤ 2 * Real.pi * δ * R' := by
      calc 2 * Real.pi * δ = 2 * Real.pi * δ * 1 := by ring
        _ ≤ 2 * Real.pi * δ * R' := mul_le_mul_of_nonneg_left hR1 (by positivity)
    linarith [hδhalf, h2]
  have hδ_le_half : δ ≤ 1 / 2 := by
    have h1 : 1 / (4 * Real.pi * R' + 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      have hR1 : 1 ≤ R' := le_max_right R 1
      have h : 4 * Real.pi * 1 ≤ 4 * Real.pi * R' :=
        mul_le_mul_of_nonneg_left hR1 (by positivity)
      nlinarith [Real.pi_gt_three, h]
    linarith [hδ_inv]
  have hδ_le_2pi : δ ≤ 1 / (2 * Real.pi) := by
    have h1 : 1 / (4 * Real.pi * R' + 1) ≤ 1 / (2 * Real.pi) :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * Real.pi)
        (by
          have hR1 : 1 ≤ R' := le_max_right R 1
          have h : 4 * Real.pi * 1 ≤ 4 * Real.pi * R' :=
            mul_le_mul_of_nonneg_left hR1 (by positivity)
          nlinarith [Real.pi_pos])
    linarith [hδ_inv]
  -- eventually both sequences are below the threshold
  have hαsmall : ∀ᶠ n in Filter.atTop, ‖α n‖ ≤ δ :=
    (hα0.eventually (isOpen_Iio.mem_nhds hδpos)).mono fun n h => le_of_lt h
  have husmall : ∀ᶠ n in Filter.atTop, ‖u n 0 - 1‖ ≤ δ :=
    (hu0.eventually (isOpen_Iio.mem_nhds hδpos)).mono fun n h => le_of_lt h
  have hEv : ∀ᶠ n in Filter.atTop, ‖α n‖ ≤ δ ∧ ‖u n 0 - 1‖ ≤ δ := hαsmall.and husmall
  -- `α n ≠ 0` from `InF1`
  have hαne : ∀ n, α n ≠ 0 := by
    intro n h
    have h1 : |(α n).im| < (α n).re := hInF1 n
    have hre : (α n).re = (0 : ℝ) := by rw [h]; rfl
    have him : (α n).im = (0 : ℝ) := by rw [h]; rfl
    rw [hre, him] at h1
    simp only [abs_zero] at h1
    exact absurd h1 (by norm_num)
  refine ⟨?_, ?_⟩
  · refine hEv.mono ?_
    intro n hn w hw
    obtain ⟨hαδ, huδ⟩ := hn
    have hαn : α n ≠ 0 := hαne n
    have hwQ : w ∈ MandelDim.Qreg (some (Ξ' : ℂ)) none := hKcone hw
    have hwge : Ξ' / 2 < ‖w‖ := (Work.Pert.Qreg_norm_lower hΞ'pos).1 w hwQ
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwge; linarith
    have hm : 0 < Ξ' / 2 := by linarith
    have hwu : 2 * Real.pi * ‖α n‖ * ‖w‖ ≤ 1 / 2 := by
      have h1 : 2 * Real.pi * ‖α n‖ ≤ 2 * Real.pi * δ :=
        mul_le_mul_of_nonneg_left hαδ (by positivity)
      have h2 : ‖w‖ ≤ R' := hKle w hw
      calc 2 * Real.pi * ‖α n‖ * ‖w‖ ≤ (2 * Real.pi * δ) * R' :=
            mul_le_mul h1 h2 (norm_nonneg w) (by positivity)
        _ = 2 * Real.pi * δ * R' := by ring
        _ ≤ 1 / 2 := hδhalf
    have h := norm_tauC_sub_tau0_le (σ := σ n) (α := α n) (u0 := u n 0) (w := w) (m := Ξ' / 2)
      hαn hw0 hm (le_of_lt hwge) (le_trans huδ hδ_le_half) (hnorm n)
      (le_trans hαδ hδ_le_2pi) hwu
    have hb := eps_bound (Ξ' := Ξ') (ε := ε) (δ := δ) (a := ‖α n‖) (b := ‖u n 0 - 1‖)
      hΞ' hε hδ_eps (norm_nonneg _) hαδ huδ
    linarith
  · refine hEv.mono ?_
    intro n hn w hw
    obtain ⟨hαδ, huδ⟩ := hn
    have hαn : α n ≠ 0 := hαne n
    have hwQ : w ∈ MandelDim.Qreg (some (Ξ' : ℂ)) none := hKcone hw
    have hwge : Ξ' / 2 < ‖w‖ := (Work.Pert.Qreg_norm_lower hΞ'pos).1 w hwQ
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwge; linarith
    have hαs2 : 2 * Real.pi * ‖α n‖ ≤ 1 / 2 := by
      have h1 : 2 * Real.pi * ‖α n‖ ≤ 2 * Real.pi * δ :=
        mul_le_mul_of_nonneg_left hαδ (by positivity)
      linarith [hδαs]
    have hwu : 2 * Real.pi * ‖α n‖ * ‖w‖ ≤ 1 / 2 := by
      have h1 : 2 * Real.pi * ‖α n‖ ≤ 2 * Real.pi * δ :=
        mul_le_mul_of_nonneg_left hαδ (by positivity)
      have h2 : ‖w‖ ≤ R' := hKle w hw
      calc 2 * Real.pi * ‖α n‖ * ‖w‖ ≤ (2 * Real.pi * δ) * R' :=
            mul_le_mul h1 h2 (norm_nonneg w) (by positivity)
        _ = 2 * Real.pi * δ * R' := by ring
        _ ≤ 1 / 2 := hδhalf
    have h8 := tauC_norm_le_of_small (σ := σ n) (α := α n) (u0 := u n 0) (w := w)
      hαn hw0 (hnorm n) (le_trans huδ hδ_le_half) hαs2 hwu
    calc ‖Work.Pert.tauC (σ n) (α n) w‖ ≤ 8 / ‖w‖ := h8
      _ ≤ 8 / (Ξ' / 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hwge.le
      _ = 16 / Ξ' := by
          rw [div_eq_div_iff (by linarith : Ξ' / 2 ≠ 0) (by linarith : (Ξ' : ℝ) ≠ 0)]
          ring
      _ ≤ 8 * Real.pi / Ξ' :=
          div_le_div_of_nonneg_right (by nlinarith [Real.pi_gt_three]) hΞ'pos.le

end Work.PertCrux
