import Mathlib
import Submission.Work.Pert.Pin3.Prelim
import Submission.Work.Pert.LiftExp.liftF_sub_translation_le_explicit
import Submission.Work.Pert.LiftExp.lipschitz_u_on_ball
import Submission.Work.Pert.LiftExp.norm_sigma_add_one_le_two
import Submission.Work.Pert.PinFromCoord.gate_aux

/-!
# PERT · `Work.Pert.Pin3.pin_data`

The quantitative datum attached to a §4.2 perturbation `f z = z + z (z - σ) u z` of the parabolic
germ, at scale `M`: the normal-form parameters `(σ, α)` are small and `1/α` sits far out in the
cone `|Im| ≤ Re`, and on the annulus `30000/rr + 15000 ≤ ‖z‖ ≤ 2M`

* the covering map `τ_f = tauC σ α` decays like `9/‖z‖` (this is the `‖τ_f‖ ≤ min (rr/4) …`
  threshold used by `Work.Pert.LiftExp.liftF_sub_translation_le_explicit`), and
* the lift `F_f = liftF u σ α` is a near-translation with defect `144 (8/rr + 4)/‖z‖` — the
  constant `Kd = 144 (CL + 4)`, `CL = 8/rr` of `NOTES_high_pin_log.md` §3.1.

All four non-geometric conjuncts are elementary consequences of the hypotheses:

* `α ≠ 0`, `16 (M+2) ≤ (1/α).re`, `|(1/α).im| ≤ (1/α).re`: `InF1 α` is `|α.im| < α.re`, so
  `‖α‖ ≤ √2 α.re` and `(1/α).re = α.re/‖α‖² ≥ 1/(√2 ‖α‖) ≥ 16√2 (M+2)`; the imaginary part bound
  is `Work.Pert.PinFromCoord.im_inv_le_re`.
* `‖σ‖ ≤ 14 ‖α‖`: `Work.Pert.Pin3.norm_sigma_le14`.
* The `τ` decay: `Work.Pert.Pin3.tauC_le_inv`, applicable because
  `‖2πiαz‖ = 2π‖α‖‖z‖ ≤ 2π · 2M/(32(M+2)) ≤ π/8 < 2/5` on the range `‖z‖ ≤ 2M`.
* The `liftF` defect: `liftF_sub_translation_le_explicit` with `r = rr/2` and `C = 8/rr` (the
  Lipschitz constant of `u` on the half-ball, `lipschitz_u_on_ball`), the threshold being cleared
  by the `τ` decay and `‖σ‖ + 1 ≤ 2` (`norm_sigma_add_one_le_two`).
-/

namespace Work.Pert.Pin3

open Complex

noncomputable section

/-! ## Uniform datum attached to the perturbation (`α`, `σ`, `τ_f` decay, near-translation) -/

/-- `α ≠ 0`, `(1/α).re ≥ 16 (M+2)` and `|(1/α).im| ≤ (1/α).re` for a small `α` in the cone
`InF1 α` (`|Im α| < Re α`). -/
lemma pin_inv_alpha_bounds {α : ℂ} {M : ℝ} (hM : 2 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2))) :
    α ≠ 0 ∧ 16 * (M + 2) ≤ (1 / α).re ∧ |(1 / α).im| ≤ (1 / α).re := by
  have hαim : |α.im| < α.re := hInF1
  have hαre_pos : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hαim
  have hαne : α ≠ 0 := by
    intro h; rw [h] at hαre_pos; simp at hαre_pos
  have hsq : ‖α‖ ^ 2 = Complex.normSq α := Complex.sq_norm α
  have hns_lt : Complex.normSq α < 2 * α.re ^ 2 := by
    rw [Complex.normSq_apply]
    have h3 : |α.im| < |α.re| := by
      rw [abs_of_pos hαre_pos]; exact hαim
    have h2 : α.im ^ 2 < α.re ^ 2 := sq_lt_sq.mpr h3
    linarith
  have hnorm_lt : ‖α‖ < Real.sqrt 2 * α.re := by
    have h2 : ‖α‖ ^ 2 < (Real.sqrt 2 * α.re) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hsq]
      exact hns_lt
    have h3 := sq_lt_sq.mp h2
    rwa [abs_of_nonneg (norm_nonneg α),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt 2 * α.re)] at h3
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hre_ge : 1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := by
    have hrepr : (1 / α).re = α.re / ‖α‖ ^ 2 := by
      rw [one_div, Complex.inv_re, Complex.sq_norm]
    rw [hrepr]
    have h : ‖α‖ / Real.sqrt 2 ≤ α.re := by
      rw [div_le_iff₀ hsqrt]
      linarith [hnorm_lt]
    calc 1 / (Real.sqrt 2 * ‖α‖) = (‖α‖ / Real.sqrt 2) / ‖α‖ ^ 2 := by field_simp
      _ ≤ α.re / ‖α‖ ^ 2 := div_le_div_of_nonneg_right h (by positivity)
  have hbig : 16 * (M + 2) ≤ 1 / (Real.sqrt 2 * (1 / (32 * (M + 2)))) := by
    have h1 : 1 / (Real.sqrt 2 * (1 / (32 * (M + 2)))) = 16 * Real.sqrt 2 * (M + 2) := by
      have h2 : Real.sqrt 2 * (1 / (32 * (M + 2))) ≠ 0 := by
        apply mul_ne_zero (ne_of_gt hsqrt)
        apply one_div_ne_zero
        linarith
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [h1]
    have h2 : (1:ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [h2, hM]
  have hle : 1 / (Real.sqrt 2 * (1 / (32 * (M + 2)))) ≤ 1 / (Real.sqrt 2 * ‖α‖) := by
    apply one_div_le_one_div_of_le (mul_pos hsqrt hαpos)
    apply mul_le_mul_of_nonneg_left hα hsqrt.le
  refine ⟨hαne, ?_, ?_⟩
  · linarith [hbig, hle, hre_ge]
  · exact Work.Pert.PinFromCoord.im_inv_le_re hInF1

/-- The covering-map decay `‖τ_f z‖ ≤ 9/‖z‖` on the annulus
`30000/rr + 15000 ≤ ‖z‖ ≤ 2M`, from `tauC_le_inv` and `‖2πiαz‖ ≤ 2π‖α‖·2M ≤ π/8 < 2/5`. -/
lemma tauC_bound_pin {σ α : ℂ} {rr M : ℝ} (hrr : 0 < rr) (hM : 2 ≤ M)
    (hαne : α ≠ 0) (hσ : ‖σ‖ ≤ 14 * ‖α‖) (hα : ‖α‖ ≤ 1 / (32 * (M + 2))) :
    ∀ z : ℂ, 30000 / rr + 15000 ≤ ‖z‖ → ‖z‖ ≤ 2 * M →
      ‖Work.Pert.tauC σ α z‖ ≤ 9 / ‖z‖ := by
  intro z hz1 hz2
  have hzpos : 0 < ‖z‖ := by
    have h1 : 0 < 30000 / rr + 15000 := by positivity
    linarith
  refine tauC_le_inv hαne hσ ?_ hzpos
  have hwn : ‖2 * (Real.pi : ℂ) * Complex.I * α * z‖ = 2 * Real.pi * ‖α‖ * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_I]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
        show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
    ring
  rw [hwn]
  have hM2p : 0 < M + 2 := by linarith
  have h1 : 2 * Real.pi * ‖α‖ * ‖z‖ ≤ 2 * Real.pi * (1 / (32 * (M + 2))) * (2 * M) := by
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left hα (by positivity)
    · exact hz2
    · positivity
    · positivity
  have h2 : 2 * Real.pi * (1 / (32 * (M + 2))) * (2 * M) ≤ 2 / 5 := by
    have he : 2 * Real.pi * (1 / (32 * (M + 2))) * (2 * M) = Real.pi * M / (8 * (M + 2)) := by
      field_simp
      ring
    rw [he]
    have h3 : Real.pi * M / (8 * (M + 2)) ≤ Real.pi / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos, hM]
    have h4 : Real.pi / 8 ≤ 2 / 5 := by
      nlinarith [Real.pi_lt_d2]
    linarith
  linarith

/-- The near-translation defect of the lift on the annulus: with the `τ` decay
`‖τ_f z‖ ≤ 9/‖z‖` in hand, `liftF_sub_translation_le_explicit` (radius `rr/2`, Lipschitz
constant `8/rr` for `u`) gives `‖F_f z - (z+1)‖ ≤ 16 (8/rr + 4)·9/‖z‖ = 144 (8/rr+4)/‖z‖`,
because on the annulus `9/‖z‖` is below the threshold `min (rr/4) (min (1/8) (1/(16(‖σ‖+1)(8/rr+4))))`
(`‖σ‖ + 1 ≤ 2`). -/
lemma pin_liftF_bound {u : ℂ → ℂ} {σ α : ℂ} {rr M : ℝ} (hrr : 0 < rr)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hα64 : ‖α‖ ≤ 1 / 64) (hαne : α ≠ 0)
    (hτ : ∀ z : ℂ, 30000 / rr + 15000 ≤ ‖z‖ → ‖z‖ ≤ 2 * M →
      ‖Work.Pert.tauC σ α z‖ ≤ 9 / ‖z‖) :
    ∀ z : ℂ, 30000 / rr + 15000 ≤ ‖z‖ → ‖z‖ ≤ 2 * M →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 144 * (8 / rr + 4) / ‖z‖ := by
  have hu2' : ∀ z ∈ Metric.ball (0 : ℂ) (rr / 2), 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2 :=
    fun z hz => hu2 z (Metric.ball_subset_ball (by linarith) hz)
  have huL := Work.Pert.LiftExp.lipschitz_u_on_ball hrr hu (fun z hz => (hu2 z hz).2)
  have hC8 : (0 : ℝ) ≤ 8 / rr := by positivity
  have htr := Work.Pert.LiftExp.liftF_sub_translation_le_explicit (u := u) (σ := σ) (α := α)
    (r := rr / 2) (C := 8 / rr) (by linarith) hC8 hu2' huL hnorm hαne hα64
  have hσ2 : ‖σ‖ + 1 ≤ 2 :=
    Work.Pert.LiftExp.norm_sigma_add_one_le_two hα64 hnorm (hu2 0 (Metric.mem_ball_self hrr)).1
  intro z hz1 hz2
  have hzpos : 0 < ‖z‖ := by
    have h1 : 0 < 30000 / rr + 15000 := by positivity
    linarith
  have hτz : ‖Work.Pert.tauC σ α z‖ ≤ 9 / ‖z‖ := hτ z hz1 hz2
  have hDpos : 0 < 16 * (‖σ‖ + 1) * (8 / rr + 4) := by positivity
  have h8pos : 0 < 8 / rr + 4 := by positivity
  -- the three threshold comparisons, all from `‖z‖ ≥ 30000/rr + 15000`
  have hrmul : rr * (30000 / rr + 15000) = 30000 + 15000 * rr := by field_simp
  have hzbig : 30000 + 15000 * rr ≤ rr * ‖z‖ := by
    rw [← hrmul]
    exact mul_le_mul_of_nonneg_left hz1 hrr.le
  have hthr : ‖Work.Pert.tauC σ α z‖ ≤
      min (rr / 2 / 2) (min (1 / 8) (1 / (16 * (‖σ‖ + 1) * (8 / rr + 4)))) := by
    refine le_trans hτz (le_min ?_ (le_min ?_ ?_))
    · rw [show (rr / 2 / 2 : ℝ) = rr / 4 by ring, div_le_iff₀ hzpos]
      nlinarith [hzbig]
    · rw [div_le_iff₀ hzpos]
      nlinarith [hz1, show (0:ℝ) < 30000 / rr + 15000 by positivity]
    · have hb : 16 * (‖σ‖ + 1) * (8 / rr + 4) ≤ 32 * (8 / rr + 4) := by
        have h16 : 16 * (‖σ‖ + 1) ≤ 16 * 2 := by linarith
        nlinarith [h16, h8pos]
      have h9 : 9 * (32 * (8 / rr + 4)) ≤ ‖z‖ := by
        have h9' : 9 * (32 * (8 / rr + 4)) = 2304 / rr + 1152 := by
          field_simp
          ring
        rw [h9']
        have hmul : rr * (2304 / rr + 1152) ≤ rr * ‖z‖ := by
          have h4 : rr * (2304 / rr + 1152) = 2304 + 1152 * rr := by field_simp
          nlinarith [hzbig, h4]
        exact (mul_le_mul_iff_of_pos_left hrr).mp hmul
      rw [div_le_div_iff₀ hzpos hDpos]
      nlinarith [h9, hb]
  calc ‖Work.Pert.liftF u σ α z - (z + 1)‖
      ≤ 16 * (8 / rr + 4) * ‖Work.Pert.tauC σ α z‖ := htr z hthr
    _ ≤ 16 * (8 / rr + 4) * (9 / ‖z‖) := mul_le_mul_of_nonneg_left hτz (by positivity)
    _ = 144 * (8 / rr + 4) / ‖z‖ := by ring

/-- **The uniform datum of a §4.2 perturbation at scale `M`.**  For a small perturbation
`f z = z + z (z - σ) u z` of the parabolic germ with multiplier `α = rotOf f` in the cone
`InF1` and `‖α‖ ≤ 1/(32(M+2))`, the data `(σ, α)` are small and `1/α` lies far out in the cone,
and on the annulus `30000/rr + 15000 ≤ ‖z‖ ≤ 2M` the covering map `τ_f` decays like `9/‖z‖` while
the lift `F_f` is a near-translation with defect `144 (8/rr + 4)/‖z‖`. -/
theorem pin_data {u : ℂ → ℂ} {σ α : ℂ} {rr M : ℝ} (hrr : 0 < rr) (hM : 2 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2)))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    α ≠ 0 ∧ ‖σ‖ ≤ 14 * ‖α‖ ∧ 16 * (M + 2) ≤ (1 / α).re ∧ |(1 / α).im| ≤ (1 / α).re ∧
    (∀ z : ℂ, 30000 / rr + 15000 ≤ ‖z‖ → ‖z‖ ≤ 2 * M →
      ‖Work.Pert.tauC σ α z‖ ≤ 9 / ‖z‖) ∧
    (∀ z : ℂ, 30000 / rr + 15000 ≤ ‖z‖ → ‖z‖ ≤ 2 * M →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 144 * (8 / rr + 4) / ‖z‖) := by
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h1 : 1 / (32 * (M + 2)) ≤ 1 / 128 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    linarith
  have hu0 : 1 / 2 ≤ ‖u 0‖ := (hu2 0 (Metric.mem_ball_self hrr)).1
  have hσ : ‖σ‖ ≤ 14 * ‖α‖ := norm_sigma_le14 hrr hu0 hnorm hα64
  obtain ⟨hαne, hre, him⟩ := pin_inv_alpha_bounds hM hInF1 hα
  have hτ := tauC_bound_pin (σ := σ) (α := α) hrr hM hαne hσ hα
  exact ⟨hαne, hσ, hre, him, hτ,
    pin_liftF_bound (u := u) hrr hu hu2 hnorm hα64 hαne hτ⟩

end

end Work.Pert.Pin3
