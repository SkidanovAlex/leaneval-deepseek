import Mathlib
import Submission.Work.Pert.PinLogDev.PinAux2
import Submission.Work.Pert.PinLogDev.Helpers
import Submission.Work.Pert.PinLogDev.liftF_sub_model_le_on_gate
import Submission.Work.Pert.PinLogDev.liftF_sub_model_le_pointwise_wide
import Submission.Work.Pert.PinLogDev.tauC_sub_tau0_alpha
import Submission.Work.Pert.PinLogDev.u_sub_hF_le
import Submission.Work.Pert.PinLogDev.u_sub_hF_le_inner
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.exists_model_data_full
import Submission.Work.Pert.PinLogDev.deep_step_le
import Submission.Work.Pert.PinLogDev.sum_shallow_indicator_le

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-! ## The margins are `2`-Lipschitz -/

lemma abs_margA_sub_le (Ξ : ℝ) (α z u : ℂ) :
    |Work.Pert.margA Ξ α z - Work.Pert.margA Ξ α u| ≤ 2 * ‖z - u‖ := by
  have h1 : Work.Pert.margA Ξ α z - Work.Pert.margA Ξ α u
      = (z - u).re + (|z.im + (1 / α).im| - |u.im + (1 / α).im|) := by
    simp only [Work.Pert.margA]
    rw [Complex.sub_re]
    ring
  rw [h1]
  have h2 : |(z - u).re| ≤ ‖z - u‖ := Complex.abs_re_le_norm _
  have h3 : |(|z.im + (1 / α).im| - |u.im + (1 / α).im|)| ≤ ‖z - u‖ := by
    have h := abs_abs_sub_abs_le_abs_sub (z.im + (1 / α).im) (u.im + (1 / α).im)
    have h4 : z.im + (1 / α).im - (u.im + (1 / α).im) = (z - u).im := by
      rw [Complex.sub_im]
      ring
    rw [h4] at h
    exact le_trans h (Complex.abs_im_le_norm _)
  calc |(z - u).re + (|z.im + (1 / α).im| - |u.im + (1 / α).im|)|
      ≤ |(z - u).re| + |(|z.im + (1 / α).im| - |u.im + (1 / α).im|)| := abs_add_le _ _
    _ ≤ 2 * ‖z - u‖ := by linarith

lemma abs_margB_sub_le (Ξ : ℝ) (α z u : ℂ) :
    |Work.Pert.margB Ξ α z - Work.Pert.margB Ξ α u| ≤ 2 * ‖z - u‖ := by
  have h1 : Work.Pert.margB Ξ α z - Work.Pert.margB Ξ α u
      = (|z.im| - |u.im|) - (z - u).re := by
    simp only [Work.Pert.margB]
    rw [Complex.sub_re]
    ring
  rw [h1]
  have h2 : |(z - u).re| ≤ ‖z - u‖ := Complex.abs_re_le_norm _
  have h3 : |(|z.im| - |u.im|)| ≤ ‖z - u‖ := by
    have h := abs_abs_sub_abs_le_abs_sub z.im u.im
    have h4 : z.im - u.im = (z - u).im := by
      rw [Complex.sub_im]
    rw [h4] at h
    exact le_trans h (Complex.abs_im_le_norm _)
  calc |(|z.im| - |u.im|) - (z - u).re| ≤ |(|z.im| - |u.im|)| + |(z - u).re| := by
        have h := abs_add_le (|z.im| - |u.im|) (-((z - u).re))
        rw [abs_neg] at h
        have h2 : |z.im| - |u.im| + -((z - u).re) = (|z.im| - |u.im|) - (z - u).re := by
          ring
        rwa [h2] at h
    _ ≤ 2 * ‖z - u‖ := by linarith

lemma mem_Qm_of_marg (Ξ : ℝ) (α z : ℂ) (hA : 0 < Work.Pert.margA Ξ α z)
    (hB : 0 < Work.Pert.margB Ξ α z) : z ∈ Work.Pert.Qm Ξ α :=
  (Work.Pert.mem_Qm_iff_marg Ξ α z).mpr ⟨hA, hB⟩

/-! ## `F` maps walk points into the gate -/

/-- If `w` is a walk point (margins at least `Rd`) then `liftF u σ α w` is again in the gate,
because `F` is a near-translation on the gate and the margins are `2`-Lipschitz. -/
lemma liftF_mem_Qm_of_marg {Ξ Rd : ℝ} {α : ℂ} {u : ℂ → ℂ} {σ w : ℂ}
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hw : w ∈ Work.Pert.Qm Ξ α)
    (hA : Rd ≤ Work.Pert.margA Ξ α w) (hB : Rd ≤ Work.Pert.margB Ξ α w)
    (hRd : 2 * (1 + 1 / 32) < Rd) :
    Work.Pert.liftF u σ α w ∈ Work.Pert.Qm Ξ α := by
  have hdef : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32 := (hNT.1.2 w hw).1
  have hstep : ‖Work.Pert.liftF u σ α w - w‖ ≤ 1 + 1 / 32 := by
    have h : Work.Pert.liftF u σ α w - w = (Work.Pert.liftF u σ α w - (w + 1)) + 1 := by ring
    rw [h]
    have := norm_add_le (Work.Pert.liftF u σ α w - (w + 1)) (1 : ℂ)
    rw [norm_one] at this
    linarith
  have h2 : 2 * ‖Work.Pert.liftF u σ α w - w‖ < Rd := by linarith
  have hA' : 0 < Work.Pert.margA Ξ α (Work.Pert.liftF u σ α w) := by
    have h := abs_margA_sub_le Ξ α (Work.Pert.liftF u σ α w) w
    rw [abs_sub_le_iff] at h
    linarith [h.1]
  have hB' : 0 < Work.Pert.margB Ξ α (Work.Pert.liftF u σ α w) := by
    have h := abs_margB_sub_le Ξ α (Work.Pert.liftF u σ α w) w
    rw [abs_sub_le_iff] at h
    linarith [h.1]
  exact mem_Qm_of_marg Ξ α _ hA' hB'

/-! ## `Φ` is Lipschitz with an explicit constant where the margins are `≥ Rd` -/

lemma Phi_sub_le_of_marg {Ξ Rde C₂ Rd : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {w a b : ℂ}
    (hRde : 0 < Rde)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hA : Rd ≤ Work.Pert.margA Ξ α w) (hB : Rd ≤ Work.Pert.margB Ξ α w)
    (hRd : Real.sqrt 2 * (2 + 2 * Rde) + 2 ≤ Rd) (hC₂ : 0 ≤ C₂)
    (ha : ‖a - w‖ < 2) (hb : ‖b - w‖ < 2) :
    ‖Φ a - Φ b‖ ≤ (1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31) * ‖a - b‖ := by
  have h4 : (4 : ℝ) < Rd := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [hRd, hRde, h2, hsq]
  have hkey : Real.sqrt 2 * Rde ≤ Rd - 4 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 2 * Rde ≤ Real.sqrt 2 * (2 + 2 * Rde) + 2 - 4 := by
      nlinarith [mul_pos h2 hRde, hsq, h2]
    linarith
  have hbound : ∀ z ∈ Metric.ball w 2,
      ‖deriv Φ z‖ ≤ 1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31 := by
    intro z hz
    have hzw : ‖z - w‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hmA0 : Rd - 4 ≤ Work.Pert.margA Ξ α z := by
      have h := abs_margA_sub_le Ξ α z w
      rw [abs_sub_le_iff] at h
      linarith [h.1]
    have hmB0 : Rd - 4 ≤ Work.Pert.margB Ξ α z := by
      have h := abs_margB_sub_le Ξ α z w
      rw [abs_sub_le_iff] at h
      linarith [h.1]
    have hmA : Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α z := by linarith
    have hmB : Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α z := by linarith
    have hcle : Real.sqrt 2 * Rde ≤ min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) :=
      le_min hmA hmB
    have hmm0 : 0 < min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) := by
      have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith [hcle, hRde]
    have hzQ : z ∈ Work.Pert.Qm Ξ α :=
      mem_Qm_of_marg Ξ α z (lt_of_lt_of_le hmm0 (min_le_left _ _))
        (lt_of_lt_of_le hmm0 (min_le_right _ _))
    have hmain := deriv_le_of_clear hRde hDE hNT hΦ hcle
    have hdef : ‖F z - (z + 1)‖ ≤ 1 / 32 := (hNT.1.2 z hzQ).1
    have hmin_le : Real.sqrt 2 * C₂ / min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z)
        ≤ Real.sqrt 2 * C₂ / (Rd - 4) := by
      have h1 : Rd - 4 ≤ min (Work.Pert.margA Ξ α z) (Work.Pert.margB Ξ α z) :=
        le_min hmA0 hmB0
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) h1
    have h31 : (32 / 31 : ℝ) * ‖F z - (z + 1)‖ ≤ 1 / 31 := by
      have h : (32 / 31 : ℝ) * ‖F z - (z + 1)‖ ≤ (32 / 31) * (1 / 32) :=
        mul_le_mul_of_nonneg_left hdef (by norm_num)
      linarith [h]
    have := hmain
    have h1 : ‖deriv Φ z‖ ≤ ‖deriv Φ z - 1‖ + 1 := by
      have h := norm_add_le (deriv Φ z - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_one] at h
      linarith [h]
    linarith [h1, this, hmin_le, h31]
  have ha' : a ∈ Metric.ball w 2 := by simpa [Metric.mem_ball, dist_eq_norm] using ha
  have hb' : b ∈ Metric.ball w 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hb
  have hballsub : Metric.ball w 2 ⊆ Work.Pert.Qm Ξ α := by
    intro z hz
    have hzw : ‖z - w‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h1 : 0 < Work.Pert.margA Ξ α z := by
      have h := abs_margA_sub_le Ξ α z w
      rw [abs_sub_le_iff] at h
      linarith [h.1]
    have h2 : 0 < Work.Pert.margB Ξ α z := by
      have h := abs_margB_sub_le Ξ α z w
      rw [abs_sub_le_iff] at h
      linarith [h.1]
    exact mem_Qm_of_marg Ξ α z h1 h2
  have hdiff : ∀ z ∈ Metric.ball w 2, DifferentiableAt ℂ Φ z := fun z hz =>
    hΦ.1.differentiableAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) hballsub)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_ball w 2) hb' ha'

end

/-! ## The structural part of the proof

`drift_aux` isolates everything in `drift_le` except the two analytic/numerical inputs, which are
passed as hypotheses:

* `hdeep` — the sharp *deep-regime* per-step comparison: for a walk point `w` with `MsE ≤ ‖w‖`,
  `‖F_f w - F₀ w‖ ≤ Cstep / (M + 1)` (this is `Work.Pert.PinLogDev.deep_step_le`);
* `hcount` — the number of *shallow* walk points (`‖w‖ < MsE`) is controlled by the walk data
  (this is `Work.Pert.PinLogDev.sum_shallow_indicator_le`).

The deviation identity used is the telescoping identity of the pin,
`Φ (W n) - W n = -(W n + (M - n)) + Σ_{j<n} (Φ (W (j+1)) - Φ (F (W j)))`,
whose first term is bounded by the hypothesis on `ε` (`hWn`, i.e. `Bn`) and whose sum is bounded
by the Lipschitz bound for `Φ` on the walk (margin `Rd`, radius `2`) together with the split
`deep/shallow` of the per-step comparisons. -/
theorem drift_aux {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ Rde C₂ rr : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ) (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂)
    (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    {X₁ Rd Bn : ℝ} (hX₁ : 0 < X₁) (hBn : 0 ≤ Bn)
    (hRd : Real.sqrt 2 * (2 + 2 * Rde) + 2 ≤ Rd)
    (Cstep MsE : ℝ) (hCstep : 0 ≤ Cstep) (hMsE : 0 < MsE)
    (hdeep : ∀ (M δ : ℝ) (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (w : ℂ),
      MsE ≤ M → 0 < δ → δ ≤ 1 / (1000 * (M + 1)) →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) δ →
      f 0 = 0 → MandelDim.InF1 α → α = MandelDim.rotOf f →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
      ‖α‖ * M ≤ 1 / 2 →
      w ∈ Work.Pert.Qm Ξ α → 64 ≤ ‖w‖ → ‖α‖ * ‖w‖ ≤ 2 / 3 → MsE ≤ ‖w‖ →
      ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ Cstep / (M + 1))
    (hcount : ∀ (n : ℕ) (ζ : ℕ → ℂ) (T Bn' X₁' M' : ℝ), 0 ≤ T → 0 < X₁' →
      (∀ j : ℕ, j < n → ‖ζ (j + 1) - (ζ j + 1)‖ ≤ 1 / 32) →
      ‖ζ n + (((M' - (n : ℝ)) : ℝ) : ℂ)‖ ≤ Bn' →
      X₁' ≤ M' - (n : ℝ) → M' - (n : ℝ) ≤ X₁' + 1 →
      ∑ j ∈ Finset.range n, (if ‖ζ j‖ < T then (1 : ℝ) else 0) ≤
        (32 / 31) * (T + X₁' + 1 + Bn') + 1) :
    ∃ (K Ms : ℝ), 0 ≤ K ∧ 0 < Ms ∧
    ∀ (M : ℝ) (δ : ℝ) (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φ : ℂ → ℂ)
      (n : ℕ) (W : ℕ → ℂ),
      Ms ≤ M → 0 < δ → δ ≤ 1 / (1000 * (M + 1)) →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) δ →
      f 0 = 0 → MandelDim.InF1 α → α = MandelDim.rotOf f →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      ‖α‖ * M ≤ 1 / 2 →
      MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
      MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α) →
      W 0 = Work.Pert.Xc d (-(M : ℂ)) →
      Φ (Work.Pert.Xc d (-(M : ℂ))) = -(M : ℂ) →
      X₁ ≤ M - n →
      M - n ≤ X₁ + 1 →
      ‖W n + (((M - (n : ℝ)) : ℝ) : ℂ)‖ ≤ Bn →
      (∀ j ≤ n, W j ∈ Work.Pert.Qm Ξ α) →
      (∀ j < n, Work.Pert.F0f f₀ (W j) = W (j + 1)) →
      (∀ j < n, ‖Work.Pert.F0f f₀ (W j) - (W j + 1)‖ ≤ 1 / 32) →
      (∀ j ≤ n, ‖α‖ * ‖W j‖ ≤ 2 / 3) →
      (∀ j ≤ n, 64 ≤ ‖W j‖) →
      (∀ j ≤ n, Rd ≤ Work.Pert.margA Ξ α (W j)) →
      (∀ j ≤ n, Rd ≤ Work.Pert.margB Ξ α (W j)) →
      ‖Φ (W n) - W n‖ ≤ K := by
  refine ⟨Bn + (1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31) *
      (Cstep + (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1) + 1), max MsE 1, ?_, ?_, ?_⟩
  · -- `0 ≤ K`
    have hRd4 : (0 : ℝ) < Rd - 4 := by
      have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [hRd, hRde, h2, hsq, mul_pos h2 hRde]
    have hΛ0 : 0 ≤ 1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31 := by positivity
    have hb0 : 0 ≤ Cstep + (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1) + 1 := by positivity
    nlinarith [hBn, mul_nonneg hΛ0 hb0]
  · exact lt_max_of_lt_right (by norm_num)
  · intro M δ f Df u σ α Φ n W hM hδ hδle hnear hf0 hInF1 hαrot hdu hu2 hform hnorm hτQ hQAdm
      hαM hNT hΦ hW0 hpin hXn hnX hWn hWQ hstep hstepdef hαW hW64 hmargA hmargB
    have hMsM : MsE ≤ M := le_trans (le_max_left _ _) hM
    have hRdlt : 2 * (1 + 1 / 32) < Rd := by
      have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [hRd, hRde, h2, hsq, mul_pos h2 hRde]
    have hnlt : (n : ℝ) < M := by linarith
    -- ## 1. the images of the walk points under `F` stay in the gate
    have hFmem : ∀ j : ℕ, j < n → Work.Pert.liftF u σ α (W j) ∈ Work.Pert.Qm Ξ α := by
      intro j hj
      exact liftF_mem_Qm_of_marg hNT (hWQ j (le_of_lt hj)) (hmargA j (le_of_lt hj))
        (hmargB j (le_of_lt hj)) hRdlt
    -- ## 2. the telescoping identity
    have htel : Φ (W n) = -(M : ℂ) + (n : ℂ) +
        ∑ j ∈ Finset.range n,
          (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j))) := by
      have hrec : ∀ m : ℕ, m ≤ n →
          Φ (W m) = Φ (W 0) + ∑ j ∈ Finset.range m, (Φ (W (j + 1)) - Φ (W j)) := by
        intro m hm
        induction m with
        | zero => simp
        | succ k ih =>
          have hk : k ≤ n := by omega
          rw [Finset.sum_range_succ, ih hk]
          ring
      have h0 : Φ (W 0) = -(M : ℂ) := by rw [hW0, hpin]
      have hsplit : ∑ j ∈ Finset.range n, (Φ (W (j + 1)) - Φ (W j))
          = (∑ j ∈ Finset.range n,
              (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j)))) + (n : ℂ) := by
        have hstepeq : ∀ j ∈ Finset.range n,
            Φ (W (j + 1)) - Φ (W j)
              = (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j))) + 1 := by
          intro j hj
          have hj' : j < n := Finset.mem_range.mp hj
          have hab : Φ (Work.Pert.liftF u σ α (W j)) = Φ (W j) + 1 :=
            hΦ.2.2 (W j) (hWQ j (le_of_lt hj')) (hFmem j hj')
          rw [hab]
          ring
        calc ∑ j ∈ Finset.range n, (Φ (W (j + 1)) - Φ (W j))
            = ∑ j ∈ Finset.range n,
                ((Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j))) + 1) :=
              Finset.sum_congr rfl hstepeq
          _ = (∑ j ∈ Finset.range n,
                (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j)))) + (n : ℂ) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                mul_one]
      rw [hrec n le_rfl, h0, hsplit]
      push_cast
      ring
    -- ## 3. the Lipschitz bound for `Φ` on the walk
    have hlip : ∀ j : ℕ, j < n →
        ‖Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j))‖
          ≤ (1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31)
              * ‖W (j + 1) - Work.Pert.liftF u σ α (W j)‖ := by
      intro j hj
      have hja : ‖W (j + 1) - W j‖ < 2 := by
        rw [← hstep j hj]
        have h1 : ‖Work.Pert.F0f f₀ (W j) - (W j + 1)‖ ≤ 1 / 32 := hstepdef j hj
        have he : Work.Pert.F0f f₀ (W j) - W j
            = (Work.Pert.F0f f₀ (W j) - (W j + 1)) + 1 := by ring
        rw [he]
        have := norm_add_le (Work.Pert.F0f f₀ (W j) - (W j + 1)) (1 : ℂ)
        rw [norm_one] at this
        linarith
      have hjb : ‖Work.Pert.liftF u σ α (W j) - W j‖ < 2 := by
        have h1 : ‖Work.Pert.liftF u σ α (W j) - (W j + 1)‖ ≤ 1 / 32 :=
          (hNT.1.2 (W j) (hWQ j (le_of_lt hj))).1
        have he : Work.Pert.liftF u σ α (W j) - W j
            = (Work.Pert.liftF u σ α (W j) - (W j + 1)) + 1 := by ring
        rw [he]
        have := norm_add_le (Work.Pert.liftF u σ α (W j) - (W j + 1)) (1 : ℂ)
        rw [norm_one] at this
        linarith
      exact Phi_sub_le_of_marg hRde hDE hNT hΦ (hmargA j (le_of_lt hj))
        (hmargB j (le_of_lt hj)) hRd hC₂ hja hjb
    -- ## 4. the per-step bounds (sharp in the deep regime, crude in the shallow one)
    have hbnd : ∀ j : ℕ, j < n →
        ‖W (j + 1) - Work.Pert.liftF u σ α (W j)‖ ≤
          Cstep / (M + 1) + (1 / 16) * (if ‖W j‖ < MsE then (1 : ℝ) else 0) := by
      intro j hj
      have hjd := hdeep M δ f Df u σ α (W j) hMsM hδ hδle hnear hf0 hInF1 hαrot hdu hu2 hform
        hnorm hτQ hαM (hWQ j (le_of_lt hj)) (hW64 j (le_of_lt hj)) (hαW j (le_of_lt hj))
      by_cases hcase : MsE ≤ ‖W j‖
      · have h1 := hjd hcase
        rw [hstep j hj, norm_sub_rev] at h1
        have h2 : 0 ≤ (1 / 16 : ℝ) * (if ‖W j‖ < MsE then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        linarith [h1, h2]
      · have hcase' : ‖W j‖ < MsE := not_le.mp hcase
        have h1 : ‖W (j + 1) - Work.Pert.liftF u σ α (W j)‖ ≤ 1 / 16 := by
          have ha : ‖W (j + 1) - (W j + 1)‖ ≤ 1 / 32 := by
            rw [← hstep j hj]
            exact hstepdef j hj
          have hb : ‖Work.Pert.liftF u σ α (W j) - (W j + 1)‖ ≤ 1 / 32 :=
            (hNT.1.2 (W j) (hWQ j (le_of_lt hj))).1
          have he : W (j + 1) - Work.Pert.liftF u σ α (W j)
              = (W (j + 1) - (W j + 1)) - (Work.Pert.liftF u σ α (W j) - (W j + 1)) := by
            ring
          rw [he]
          linarith [norm_sub_le (W (j + 1) - (W j + 1))
            (Work.Pert.liftF u σ α (W j) - (W j + 1))]
        rw [if_pos hcase']
        have h2 : 0 ≤ Cstep / (M + 1) := div_nonneg hCstep (by linarith)
        linarith
    -- ## 5. the sum of the per-step bounds
    have hsum1 : ∑ j ∈ Finset.range n, ‖W (j + 1) - Work.Pert.liftF u σ α (W j)‖
        ≤ ∑ j ∈ Finset.range n,
            (Cstep / (M + 1) + (1 / 16) * (if ‖W j‖ < MsE then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun j hj => hbnd j (Finset.mem_range.mp hj))
    have hsum2 : ∑ j ∈ Finset.range n,
          (Cstep / (M + 1) + (1 / 16) * (if ‖W j‖ < MsE then (1 : ℝ) else 0))
        = (n : ℝ) * (Cstep / (M + 1))
          + (1 / 16) * (∑ j ∈ Finset.range n, (if ‖W j‖ < MsE then (1 : ℝ) else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.mul_sum]
      try ring
    have hcnt := hcount n W MsE Bn X₁ M hMsE.le hX₁
      (fun j hj => by rw [← hstep j hj]; exact hstepdef j hj) hWn hXn hnX
    have hsum3 : ∑ j ∈ Finset.range n, ‖W (j + 1) - Work.Pert.liftF u σ α (W j)‖
        ≤ Cstep + (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1) := by
      refine le_trans hsum1 ?_
      rw [hsum2]
      have hnM : (n : ℝ) * (Cstep / (M + 1)) ≤ Cstep := by
        have h1 : (n : ℝ) ≤ M + 1 := by linarith
        have h2 : (0 : ℝ) < M + 1 := by linarith
        have h3 : (n : ℝ) / (M + 1) ≤ 1 := (div_le_one h2).mpr h1
        calc (n : ℝ) * (Cstep / (M + 1)) = Cstep * ((n : ℝ) / (M + 1)) := by ring
          _ ≤ Cstep * 1 := mul_le_mul_of_nonneg_left h3 hCstep
          _ = Cstep := by ring
      have h4 : (1 / 16 : ℝ) * (∑ j ∈ Finset.range n, (if ‖W j‖ < MsE then (1 : ℝ) else 0))
          ≤ (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1) :=
        mul_le_mul_of_nonneg_left hcnt (by norm_num)
      linarith
    -- ## 6. assembly
    have hmain : Φ (W n) - W n = -(W n + (((M - (n : ℝ)) : ℝ) : ℂ)) +
        ∑ j ∈ Finset.range n,
          (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j))) := by
      rw [htel]
      push_cast
      ring
    have hΛ0 : 0 ≤ 1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31 := by
      have hRd4 : (0 : ℝ) < Rd - 4 := by
        have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        nlinarith [hRd, hRde, h2, hsq, mul_pos h2 hRde]
      positivity
    have hsum4 : ‖∑ j ∈ Finset.range n,
          (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j)))‖
        ≤ (1 + Real.sqrt 2 * C₂ / (Rd - 4) + 1 / 31)
            * (Cstep + (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1)) := by
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hsum3 hΛ0)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj => hlip j (Finset.mem_range.mp hj))
    rw [hmain]
    have h1 : ‖-(W n + (((M - (n : ℝ)) : ℝ) : ℂ)) +
        ∑ j ∈ Finset.range n, (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j)))‖
        ≤ ‖W n + (((M - (n : ℝ)) : ℝ) : ℂ)‖ +
          ‖∑ j ∈ Finset.range n, (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j)))‖ := by
      have h := norm_add_le (-(W n + (((M - (n : ℝ)) : ℝ) : ℂ)))
        (∑ j ∈ Finset.range n, (Φ (W (j + 1)) - Φ (Work.Pert.liftF u σ α (W j))))
      rwa [norm_neg] at h
    have h2 : Cstep + (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1)
        ≤ Cstep + (1 / 16) * ((32 / 31) * (MsE + X₁ + 1 + Bn) + 1) + 1 := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hΛ0
    linarith [h1, hsum4, hWn, h3]

theorem drift_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ Rde C₂ rr : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ) (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂)
    (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    {X₁ Rd Bn : ℝ} (hX₁ : 0 < X₁) (hBn : 0 ≤ Bn)
    (hRd : Real.sqrt 2 * (2 + 2 * Rde) + 2 ≤ Rd) :
    ∃ (K Ms : ℝ), 0 ≤ K ∧ 0 < Ms ∧
    ∀ (M : ℝ) (δ : ℝ) (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φ : ℂ → ℂ)
      (n : ℕ) (W : ℕ → ℂ),
      Ms ≤ M → 0 < δ → δ ≤ 1 / (1000 * (M + 1)) →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) δ →
      f 0 = 0 → MandelDim.InF1 α → α = MandelDim.rotOf f →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
      MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      ‖α‖ * M ≤ 1 / 2 →
      MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
      MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α) →
      W 0 = Work.Pert.Xc d (-(M : ℂ)) →
      Φ (Work.Pert.Xc d (-(M : ℂ))) = -(M : ℂ) →
      X₁ ≤ M - n →
      M - n ≤ X₁ + 1 →
      ‖W n + (((M - (n : ℝ)) : ℝ) : ℂ)‖ ≤ Bn →
      (∀ j ≤ n, W j ∈ Work.Pert.Qm Ξ α) →
      (∀ j < n, Work.Pert.F0f f₀ (W j) = W (j + 1)) →
      (∀ j < n, ‖Work.Pert.F0f f₀ (W j) - (W j + 1)‖ ≤ 1 / 32) →
      (∀ j ≤ n, ‖α‖ * ‖W j‖ ≤ 2 / 3) →
      (∀ j ≤ n, 64 ≤ ‖W j‖) →
      (∀ j ≤ n, Rd ≤ Work.Pert.margA Ξ α (W j)) →
      (∀ j ≤ n, Rd ≤ Work.Pert.margB Ξ α (W j)) →
      ‖Φ (W n) - W n‖ ≤ K := by
  obtain ⟨Cstep, MsE, hCstep, hMsE, hdeep⟩ := deep_step_le d hd Ξ rr hrr hrrD
  obtain ⟨K, Ms, hK, hMs, hrest⟩ :=
    drift_aux d hd Ξ Rde C₂ rr hΞ hRde hC₂ hrr hrrD hDE hX₁ hBn hRd Cstep MsE hCstep hMsE
      hdeep (fun n ζ T Bn' X₁' M' hT hX₁' hstep hn hXn hnX =>
        sum_shallow_indicator_le hT hX₁' hstep hn hXn hnX)
  exact ⟨K, Ms, hK, hMs, hrest⟩

end Work.Pert.PinLogDev
