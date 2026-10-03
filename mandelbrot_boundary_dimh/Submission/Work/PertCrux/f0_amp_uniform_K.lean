import Mathlib
import Submission.Work.Pert.Ksub2.f0_iterate_lipschitz_uniform_D
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.exists_ball_local_inverse
import Submission.Work.Pert.Ksub2.exists_ball_subset_of_forall_mem
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.tools
import Submission.Work.Parab.Setup
import Submission.Work.PertCrux.Xc_deep_ball_data

/-!
# `Work.PertCrux.f0_amp_uniform_K`

Uniform-in-the-level amplification of `f₀`-orbits near the deep strip, as used by
`Ksub_phi_close_v2` (the "fixed amplification `A = sup |(f₀^[n])'|`" of the assembly notes).

**Statement.** For §4.1 data `d : ParabData f₀ D₀` and a compact `K' ⊆ d.Dφ` there are constants
`Ce₀, cc₀, M₀, Kk > 0` (and `T₀` bounding `K'`) such that for every `M ≥ M₀`, every `w ∈ K'`,
every `u` of the deep strip `Dstrip M (T₀ + 1)` with `u + n = w`, every `k ≤ n` and every `z` with
`‖z - d.φ u‖ < cc₀ / (Kk M²)`,

  `‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ (2 Ce₀ M² / cc₀) ‖z - d.φ u‖`.

**Proof.** Two ingredients.

* `Work.Pert.Ksub2.deriv_phi_bounds_walk` supplies the walk bounds: on the `ρe`-balls around the
  walk points `u, u+1, …, u+n = w` the coordinate `φ₀` is holomorphic and `‖φ₀'‖ ≤ Ce₀`.
* The crux is to *invert* `φ₀` near `d.φ u` with an explicitly controlled radius.  The curve
  `Xc d = τ₀ ∘ φ₀` is a quasi-identity with a `log`-sized displacement; on the ball of radius
  `ρ := C₀ (1 + log 2M)` around a deep point `u` it satisfies `‖(Xc d)' - 1‖ ≤ 1/2`
  (`Work.PertCrux.Xc_deep_ball_data`), so the Rouché covering estimate
  `Work.Pert.image_cover_centered` gives a preimage `W` of `τ₀ z` under `Xc d` in that ball, i.e.
  `φ₀ W = z`, and the mean value estimate `Work.Pert.image_cover_mvt` turns the same derivative
  bound into the coercivity `‖W - u‖ ≤ 2 ‖Xc d W - Xc d u‖`.  Since
  `Xc d W - Xc d u = τ₀ z - τ₀ (φ₀ u) = (z - φ₀ u)/(z · φ₀ u)` and
  `‖z‖ ≳ 1/M`, `‖φ₀ u‖ ≳ 1/M`, one gets `‖W - u‖ ≤ 36 M² ‖z - φ₀ u‖`.
  The Abel equation along the walks `W, …, W+k` and `u, …, u+k` identifies
  `f₀^[k] z = φ₀ (W + k)`, `f₀^[k] (d.φ u) = φ₀ (u + k)`, so the mean value theorem at the far
  end (with the bound `Ce₀`) gives the constant `36 Ce₀ M² ≤ 2 Ce₀ M² / cc₀` as soon as
  `cc₀ ≤ 1/18`.

The only non-elementary input is `Work.PertCrux.Xc_deep_ball_data` (delegated; the deep-strip
geometry of the curve at `log`-scale), the rest is mean value bookkeeping.
-/

namespace Work.PertCrux

open MandelDim Complex Set Metric Work.Pert

noncomputable section

/-- `‖τ₀ w‖ = 1/‖w‖` for `τ₀ w = -1/w`. -/
private lemma norm_tau0' (w : ℂ) : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
  simp [MandelDim.tau0, norm_neg, norm_one]

/-- `τ₀ z - τ₀ a = (z - a)/(z a)` away from `0` (`τ₀ w = -1/w`). -/
private lemma tau0_sub (z a : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) :
    MandelDim.tau0 z - MandelDim.tau0 a = (z - a) / (z * a) := by
  simp only [MandelDim.tau0]
  field_simp
  ring

/-- **Core amplification bound.**  All the analytic inputs are hypotheses; the conclusion is the
inner `∀ M ≥ M₁` statement of `f0_amp_uniform_K` (with the deep-ball data
`Work.PertCrux.Xc_deep_ball_data` in place of `c₁`). -/
theorem amp_core {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ}
    {T₀ ρe Ce₀ cc₀ C₀ M₁ Kk : ℝ}
    (hρe : 0 < ρe) (hCe₀ : 0 < Ce₀) (hcc₀ : 0 < cc₀) (hC₀ : 0 < C₀) (hKk : 0 < Kk)
    (hcc₀18 : cc₀ ≤ 1 / 18)
    (hKk_ρe : 36 * cc₀ < Kk * ρe)
    (hKk_C₀ : 72 * cc₀ < Kk * C₀)
    (hM₁1 : 1 ≤ M₁)
    (hKk_M : 6 * cc₀ ≤ Kk * M₁)
    (hwalk : ∀ M : ℝ, M₁ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1), ∀ n : ℕ,
      u + (n : ℂ) = w → ∀ i : ℕ, i ≤ n →
        Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ ∧
        ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce₀)
    (hstrip : ∀ M : ℝ, M₁ ≤ M → ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1),
      ‖Work.Pert.Xc d u‖ ≤ 3 * M ∧ d.φ u ≠ 0)
    (hdeep : ∀ M : ℝ, M₁ ≤ M → ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1),
      (∀ z : ℂ, ‖z - u‖ ≤ C₀ * (1 + Real.log (2 * M)) → z ∈ MandelDim.QLeft d.ξ₀) ∧
      (∀ z : ℂ, ‖z - u‖ ≤ C₀ * (1 + Real.log (2 * M)) →
        DifferentiableAt ℂ (Work.Pert.Xc d) z) ∧
      (∀ z : ℂ, ‖z - u‖ ≤ C₀ * (1 + Real.log (2 * M)) →
        ‖deriv (Work.Pert.Xc d) z - 1‖ ≤ 1 / 2)) :
    ∀ M : ℝ, M₁ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1), ∀ n : ℕ,
      u + (n : ℂ) = w → ∀ k : ℕ, k ≤ n → ∀ z : ℂ, ‖z - d.φ u‖ < cc₀ / (Kk * M * M) →
        ‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ (2 * Ce₀ * M * M / cc₀) * ‖z - d.φ u‖ := by
  intro M hM w hw u hu n hn k hk z hz
  have hMpos : 0 < M := lt_of_lt_of_le (by linarith) hM
  have hMMpos : 0 < M * M := mul_pos hMpos hMpos
  -- ## the deep-ball data at `u`, and the sector membership of `u`
  obtain ⟨hdmem, hddiff, hdder⟩ := hdeep M hM u hu
  have hlog2M : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have hρpos : 0 < C₀ * (1 + Real.log (2 * M)) := mul_pos hC₀ (by linarith)
  have huQ : u ∈ MandelDim.QLeft d.ξ₀ := hdmem u (by rw [sub_self, norm_zero]; exact hρpos.le)
  -- ## the strip bound at `u`: `‖φ₀ u‖ ≥ 1/(3M)`
  obtain ⟨hXcu, hφune⟩ := hstrip M hM u hu
  have hnormXcu : ‖Work.Pert.Xc d u‖ = 1 / ‖d.φ u‖ := by
    rw [Work.Pert.Xc]; exact norm_tau0' (d.φ u)
  have ha_pos : 0 < ‖d.φ u‖ := norm_pos_iff.mpr hφune
  have ha_low : 1 / (3 * M) ≤ ‖d.φ u‖ := by
    have h3M : 0 < 3 * M := by linarith
    have h1 : 1 / ‖d.φ u‖ ≤ 3 * M := hnormXcu ▸ hXcu
    have hmul : 1 ≤ (3 * M) * ‖d.φ u‖ := (div_le_iff₀ ha_pos).mp h1
    rw [div_le_iff₀ h3M]
    rw [mul_comm (3 * M)] at hmul
    exact hmul
  have ha0 : d.φ u ≠ 0 := hφune
  -- ## lower bound for `‖z‖`
  have hKkM : 6 * cc₀ ≤ Kk * M :=
    le_trans hKk_M (mul_le_mul_of_nonneg_left hM hKk.le)
  have hz_small : cc₀ / (Kk * M * M) ≤ 1 / (6 * M) := by
    have hKkMM : 0 < Kk * M * M := by positivity
    have heq : 1 / (6 * M) * (Kk * M * M) = Kk * M / 6 := by
      field_simp
      try ring
    rw [div_le_iff₀ hKkMM, heq, le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    linarith [hKkM]
  have hz_norm : 1 / (6 * M) < ‖z‖ := by
    have h1 : ‖d.φ u‖ ≤ ‖z‖ + ‖z - d.φ u‖ := by
      have h := norm_add_le z (d.φ u - z)
      rw [add_sub_cancel] at h
      rwa [norm_sub_rev (d.φ u) z] at h
    have h2 : 1 / (3 * M) - 1 / (6 * M) = 1 / (6 * M) := by
      field_simp
      try ring
    linarith [ha_low, hz, hz_small, h1, h2]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz_norm
    linarith [show (0 : ℝ) < 1 / (6 * M) by positivity]
  -- ## the Rouché covering of `τ₀ '' ball` by `Xc d`
  have hdiffball : ∀ ζ ∈ Metric.closedBall u (C₀ * (1 + Real.log (2 * M))),
      DifferentiableAt ℂ (Work.Pert.Xc d) ζ := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    exact hddiff ζ hζ
  have hderball : ∀ ζ ∈ Metric.closedBall u (C₀ * (1 + Real.log (2 * M))),
      ‖deriv (Work.Pert.Xc d) ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    exact hdder ζ hζ
  have hcov := image_cover_centered (Φ := Work.Pert.Xc d) (z₀ := u)
    (r := C₀ * (1 + Real.log (2 * M))) hρpos hdiffball hderball
  -- ## the size of `1/(‖z‖ ‖φ₀ u‖)`
  have hτsub : MandelDim.tau0 z - MandelDim.tau0 (d.φ u) = (z - d.φ u) / (z * d.φ u) :=
    tau0_sub z (d.φ u) hz0 ha0
  have hpm : 1 / (6 * M) * (1 / (3 * M)) < ‖z‖ * ‖d.φ u‖ :=
    mul_lt_mul hz_norm ha_low (by positivity) (norm_nonneg z)
  have hdenpos : 0 < 1 / (6 * M) * (1 / (3 * M)) := by positivity
  have hinv18 : 1 / (‖z‖ * ‖d.φ u‖) ≤ 18 * M * M := by
    have h1 : 1 / (‖z‖ * ‖d.φ u‖) ≤ 1 / (1 / (6 * M) * (1 / (3 * M))) :=
      one_div_le_one_div_of_le hdenpos hpm.le
    have h2 : 1 / (1 / (6 * M) * (1 / (3 * M))) = 18 * M * M := by
      field_simp
      try ring
    linarith [h1, h2.ge]
  have hdist : ‖z - d.φ u‖ / (‖z‖ * ‖d.φ u‖) ≤ 18 * M * M * ‖z - d.φ u‖ := by
    rw [div_eq_mul_one_div]
    calc ‖z - d.φ u‖ * (1 / (‖z‖ * ‖d.φ u‖)) ≤ ‖z - d.φ u‖ * (18 * M * M) :=
          mul_le_mul_of_nonneg_left hinv18 (norm_nonneg _)
      _ = 18 * M * M * ‖z - d.φ u‖ := by ring
  -- ## `τ₀ z` lies in the covered ball
  have h4 : 18 * cc₀ / Kk < C₀ * (1 + Real.log (2 * M)) / 4 := by
    have hC₀le : C₀ ≤ C₀ * (1 + Real.log (2 * M)) := by nlinarith
    have h5 : 18 * cc₀ / Kk < C₀ / 4 := by
      rw [div_lt_iff₀ hKk, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hKk_C₀]
    linarith
  have hy : MandelDim.tau0 z ∈
      Metric.ball (Work.Pert.Xc d u) (C₀ * (1 + Real.log (2 * M)) / 4) := by
    rw [Metric.mem_ball, dist_eq_norm,
      show Work.Pert.Xc d u = MandelDim.tau0 (d.φ u) from rfl, hτsub, norm_div, norm_mul]
    have h2 : 18 * M * M * ‖z - d.φ u‖ ≤ 18 * M * M * (cc₀ / (Kk * M * M)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hz) (by positivity)
    have h3 : 18 * M * M * (cc₀ / (Kk * M * M)) = 18 * cc₀ / Kk := by
      field_simp
      try ring
    linarith [hdist, h2, h3.ge, h4]
  -- ## the preimage `W` of `τ₀ z`
  obtain ⟨W, hWball, hXcW⟩ := hcov hy
  have hmvt := image_cover_mvt hρpos hdiffball hderball
  -- ## coercivity: `‖W - u‖ ≤ 2 ‖Xc W - Xc u‖`
  have hWnorm : ‖W - u‖ ≤ 2 * ‖Work.Pert.Xc d W - Work.Pert.Xc d u‖ := by
    have h1 := hmvt W hWball
    have h2 : ‖W - u‖ ≤ ‖(Work.Pert.Xc d W - W) - (Work.Pert.Xc d u - u)‖ +
        ‖Work.Pert.Xc d W - Work.Pert.Xc d u‖ := by
      have h3 := norm_add_le (-((Work.Pert.Xc d W - W) - (Work.Pert.Xc d u - u)))
        (Work.Pert.Xc d W - Work.Pert.Xc d u)
      rw [norm_neg] at h3
      have h4 : -((Work.Pert.Xc d W - W) - (Work.Pert.Xc d u - u)) +
          (Work.Pert.Xc d W - Work.Pert.Xc d u) = W - u := by ring
      calc ‖W - u‖ = ‖-((Work.Pert.Xc d W - W) - (Work.Pert.Xc d u - u)) +
            (Work.Pert.Xc d W - Work.Pert.Xc d u)‖ := by rw [h4]
        _ ≤ ‖(Work.Pert.Xc d W - W) - (Work.Pert.Xc d u - u)‖ +
            ‖Work.Pert.Xc d W - Work.Pert.Xc d u‖ := h3
    linarith
  -- ## `φ₀ W = z`
  have hφW : d.φ W = z := by
    have h1 : MandelDim.tau0 (d.φ W) = MandelDim.tau0 z := by
      simpa only [Work.Pert.Xc] using hXcW
    calc d.φ W = MandelDim.tau0 (MandelDim.tau0 (d.φ W)) := (Work.Pert.tau0_tau0 (d.φ W)).symm
      _ = MandelDim.tau0 (MandelDim.tau0 z) := by rw [h1]
      _ = z := Work.Pert.tau0_tau0 z
  -- ## the relative bound `‖W - u‖ ≤ 36 M² ‖z - φ₀ u‖`
  have hrel : ‖W - u‖ ≤ 36 * M * M * ‖z - d.φ u‖ := by
    have h1 : ‖Work.Pert.Xc d W - Work.Pert.Xc d u‖ = ‖z - d.φ u‖ / (‖z‖ * ‖d.φ u‖) := by
      rw [hXcW, show Work.Pert.Xc d u = MandelDim.tau0 (d.φ u) from rfl, hτsub, norm_div, norm_mul]
    calc ‖W - u‖ ≤ 2 * ‖Work.Pert.Xc d W - Work.Pert.Xc d u‖ := hWnorm
      _ = 2 * (‖z - d.φ u‖ / (‖z‖ * ‖d.φ u‖)) := by rw [h1]
      _ ≤ 2 * (18 * M * M * ‖z - d.φ u‖) := by linarith [hdist]
      _ = 36 * M * M * ‖z - d.φ u‖ := by ring
  -- ## `‖W - u‖ < ρe`
  have hwρ : ‖W - u‖ < ρe := by
    have h1 : 36 * M * M * ‖z - d.φ u‖ ≤ 36 * M * M * (cc₀ / (Kk * M * M)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hz) (by positivity)
    have h2 : 36 * M * M * (cc₀ / (Kk * M * M)) = 36 * cc₀ / Kk := by
      field_simp
      try ring
    have h3 : 36 * cc₀ / Kk < ρe := by
      rw [div_lt_iff₀ hKk]
      nlinarith [hKk_ρe]
    linarith [hrel, h1, h2.ge, h3]
  -- ## the walks and the Abel equation
  have hwalk_u : ∀ i : ℕ, i ≤ k → u + (i : ℂ) ∈ d.Dφ := by
    intro i hi
    exact (hwalk M hM w hw u hu n hn i (le_trans hi hk)).1 (Metric.mem_ball_self hρe)
  have hwalk_W : ∀ i : ℕ, i ≤ k → W + (i : ℂ) ∈ d.Dφ := by
    intro i hi
    apply (hwalk M hM w hw u hu n hn i (le_trans hi hk)).1
    rw [Metric.mem_ball, dist_eq_norm]
    have h : W + (i : ℂ) - (u + (i : ℂ)) = W - u := by ring
    rw [h]
    exact hwρ
  have hiter_W : f₀^[k] (d.φ W) = d.φ (W + (k : ℂ)) :=
    Work.Pert.Ksub2.iterate_phi_of_mem d hwalk_W
  have hiter_u : f₀^[k] (d.φ u) = d.φ (u + (k : ℂ)) :=
    Work.Pert.Ksub2.iterate_phi_of_mem d hwalk_u
  -- ## the mean value bound at the far end of the walk
  have hMVT : ‖d.φ (W + (k : ℂ)) - d.φ (u + (k : ℂ))‖ ≤ Ce₀ * ‖W - u‖ := by
    obtain ⟨hbk, hCek⟩ := hwalk M hM w hw u hu n hn k hk
    have hmv := (convex_ball (u + (k : ℂ)) ρe).norm_image_sub_le_of_norm_deriv_le
      (f := d.φ) (C := Ce₀) (x := u + (k : ℂ)) (y := W + (k : ℂ))
      (fun x hx => d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (hbk hx)))
      (fun x hx => hCek x (hbk hx)
        (le_of_lt (by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx)))
      (by rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hρe)
      (by
        rw [Metric.mem_ball, dist_eq_norm]
        have h : W + (k : ℂ) - (u + (k : ℂ)) = W - u := by ring
        rw [h]
        exact hwρ)
    simpa using hmv
  -- ## the constant comparison
  have hkey : Ce₀ * (36 * M * M) ≤ 2 * Ce₀ * M * M / cc₀ := by
    rw [le_div_iff₀ hcc₀]
    have h36 : 36 * cc₀ ≤ 2 := by linarith [hcc₀18]
    have h1 : Ce₀ * (M * M) * (36 * cc₀) ≤ Ce₀ * (M * M) * 2 :=
      mul_le_mul_of_nonneg_left h36 (by positivity)
    have h2 : Ce₀ * (36 * M * M) * cc₀ = Ce₀ * (M * M) * (36 * cc₀) := by ring
    have h3 : 2 * Ce₀ * M * M = Ce₀ * (M * M) * 2 := by ring
    linarith [h1, h2.ge, h3.le]
  calc ‖f₀^[k] z - f₀^[k] (d.φ u)‖
      = ‖d.φ (W + (k : ℂ)) - d.φ (u + (k : ℂ))‖ := by rw [← hφW, hiter_W, hiter_u]
    _ ≤ Ce₀ * ‖W - u‖ := hMVT
    _ ≤ Ce₀ * (36 * M * M * ‖z - d.φ u‖) := mul_le_mul_of_nonneg_left hrel hCe₀.le
    _ = (Ce₀ * (36 * M * M)) * ‖z - d.φ u‖ := by ring
    _ ≤ (2 * Ce₀ * M * M / cc₀) * ‖z - d.φ u‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)

/-- **Target lemma.**  Uniform-in-the-level amplification of `f₀`-orbits on the deep strip. -/
theorem f0_amp_uniform_K {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ (∀ w ∈ K', ‖w‖ ≤ T₀) ∧ ∃ Ce₀ cc₀ M₀ Kk : ℝ,
      0 < Ce₀ ∧ 0 < cc₀ ∧ 0 < M₀ ∧ 0 < Kk ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1), ∀ n : ℕ, u + (n : ℂ) = w →
        ∀ k : ℕ, k ≤ n → ∀ z : ℂ, ‖z - d.φ u‖ < cc₀ / (Kk * M * M) →
          ‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ (2 * Ce₀ * M * M / cc₀) * ‖z - d.φ u‖ := by
  obtain ⟨T₀, hT₀pos, hT₀bd, ρe, hρepos, _hballw, M₁, hM₁pos, Ce₀, cc₀', hCe₀pos, hcc₀'pos,
    Hwalk⟩ := Work.Pert.Ksub2.deriv_phi_bounds_walk d hK'c hK'
  obtain ⟨M₂, hM₂pos, Hstrip⟩ := Work.Pert.Ksub2.Xc_strip_nhd_bounds d (T₀ + 1)
  obtain ⟨c₁, hc₁pos, M₃, hM₃pos, Hdeep⟩ :=
    Work.PertCrux.Xc_deep_ball_data d (T₀ + 1) (by linarith)
  -- ## the constants
  set cc₀ : ℝ := min cc₀' (1 / 18) with hcc₀def
  have hcc₀pos : 0 < cc₀ := lt_min hcc₀'pos (by norm_num)
  have hcc₀18 : cc₀ ≤ 1 / 18 := min_le_right _ _
  set Kk : ℝ := max 1 (max (36 * cc₀ / ρe + 1) (72 * cc₀ / c₁ + 1)) with hKkdef
  have hKkpos : 0 < Kk := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKk1 : 36 * cc₀ / ρe + 1 ≤ Kk := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKk2 : 72 * cc₀ / c₁ + 1 ≤ Kk := le_trans (le_max_right _ _) (le_max_right _ _)
  have hKk_ρe : 36 * cc₀ < Kk * ρe := by
    have h1 : (36 * cc₀ / ρe + 1) * ρe ≤ Kk * ρe := mul_le_mul_of_nonneg_right hKk1 hρepos.le
    have h2 : (36 * cc₀ / ρe + 1) * ρe = 36 * cc₀ + ρe := by
      field_simp
      try ring
    linarith [h1, h2.ge]
  have hKk_c₁ : 72 * cc₀ < Kk * c₁ := by
    have h1 : (72 * cc₀ / c₁ + 1) * c₁ ≤ Kk * c₁ := mul_le_mul_of_nonneg_right hKk2 hc₁pos.le
    have h2 : (72 * cc₀ / c₁ + 1) * c₁ = 72 * cc₀ + c₁ := by
      field_simp
      try ring
    linarith [h1, h2.ge]
  set M₀ : ℝ := max (max (max M₁ M₂) (max M₃ (d.ξ₀ + 2))) (max (1 + 6 * cc₀ / Kk) 1) with hM₀def
  have hM₁M₀ : M₁ ≤ M₀ :=
    le_trans (le_max_left M₁ M₂) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hM₂M₀ : M₂ ≤ M₀ :=
    le_trans (le_max_right M₁ M₂) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hM₃M₀ : M₃ ≤ M₀ :=
    le_trans (le_max_left M₃ (d.ξ₀ + 2)) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hξM₀ : d.ξ₀ + 1 ≤ M₀ := by
    have h : d.ξ₀ + 2 ≤ M₀ :=
      le_trans (le_max_right M₃ (d.ξ₀ + 2)) (le_trans (le_max_right _ _) (le_max_left _ _))
    linarith
  have hM₀_cc : 1 + 6 * cc₀ / Kk ≤ M₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₀1 : 1 ≤ M₀ := by
    have h : (0 : ℝ) ≤ 6 * cc₀ / Kk := by positivity
    linarith [hM₀_cc, h]
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one hM₀1
  have hKk_M : 6 * cc₀ ≤ Kk * M₀ := by
    have h1 : Kk * (1 + 6 * cc₀ / Kk) ≤ Kk * M₀ := mul_le_mul_of_nonneg_left hM₀_cc hKkpos.le
    have h2 : Kk * (1 + 6 * cc₀ / Kk) = Kk + 6 * cc₀ := by
      field_simp
      try ring
    linarith [h1, h2.ge]
  refine ⟨T₀, hT₀pos, hT₀bd, Ce₀, cc₀, M₀, Kk, hCe₀pos, hcc₀pos, hM₀pos, hKkpos, ?_⟩
  intro M hM
  refine amp_core (T₀ := T₀) (ρe := ρe) (Ce₀ := Ce₀) (cc₀ := cc₀) (C₀ := c₁) (M₁ := M₀)
    (Kk := Kk) d hρepos hCe₀pos hcc₀pos hc₁pos hKkpos hcc₀18 hKk_ρe hKk_c₁ hM₀1 hKk_M
    ?_ ?_ ?_ M hM
  · -- ## the walk bounds
    intro M' hM' w hw u hu n hn i hi
    exact (Hwalk M' (le_trans hM₁M₀ hM') w hw u hu n hn).1 i hi
  · -- ## the strip bounds
    intro M' hM' u hu
    have huQ : u ∈ MandelDim.QLeft d.ξ₀ :=
      Work.Pert.Dstrip_sub_QLeft (M := M') (T := T₀ + 1) (ξ := d.ξ₀) (le_trans hξM₀ hM') hu
    have huDφ : u ∈ d.Dφ := d.Q_sub huQ
    have h := Hstrip M' (le_trans hM₂M₀ hM') u hu u huDφ (by simp)
    exact ⟨h.2.1, h.2.2⟩
  · -- ## the deep-ball data
    intro M' hM' u hu
    obtain ⟨h1, h2, h3, -⟩ := Hdeep M' (le_trans hM₃M₀ hM') u hu
    exact ⟨h1, h2, h3⟩

end

end Work.PertCrux
