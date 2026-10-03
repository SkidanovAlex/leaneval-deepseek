import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.scale_cauchy
import Submission.Work.Pert.liftF_sub_translation_le

/-!
# PERT · `Work.Pert.liftF_defect_le_tauC`

The defect of the lift `F_f = liftF u σ α` of Shishikura's perturbed Fatou coordinate is
controlled by the coordinate `τ_f = tauC σ α` itself: on the lower gate `Qm Ξ α` there is a
constant `C > 0` with

    ‖liftF u σ α z - (z + 1)‖ ≤ C ‖τ_f z‖ .

Note that this is *not* a consequence of the mere *boundedness* of the defect supplied by the
near-translation hypothesis `hNT` (`≤ 1/32`): `‖τ_f z‖` is not bounded below on the gate (it decays
like `exp (-κ z.im)` at the upper end), so at the upper end one really needs the analytic fact
that the defect itself decays with the same rate.

The proof splits the gate at the threshold `ε` of `Work.Pert.liftF_sub_translation_le`:

* where `‖τ_f z‖ ≤ ε`, that lemma (the algebraic identity `1 - s = A(1 + E)` of (A.1.7) together
  with the principal logarithm of `A = exp (2πiα)`) gives `‖defect‖ ≤ K ‖τ_f z‖`.  Its Lipschitz
  input `‖u 0 - u τ‖ ≤ C ‖τ‖` is produced here from the *boundedness* hypothesis `hu2` alone by the
  Cauchy estimate `Work.Pert.scale_cauchy` (`‖u'‖ ≤ 8/Rm` on `ball 0 (Rm/2)`) followed by the mean
  value inequality, with `C = 8/Rm` on `ball 0 (Rm/4)`;
* where `‖τ_f z‖ > ε`, the near-translation hypothesis `hNT` gives `‖defect‖ ≤ 1/32`, hence
  `‖defect‖ ≤ (1/(32ε)) ‖τ_f z‖`.

Taking `C := max K (1/(32ε))` gives the claim.  The remaining hypotheses of the statement
(`hΞ`, `hσ`, `hInF1`, `hτQ`) are not needed for this estimate; they belong to the surrounding
geometry in which the lemma is applied.
-/

namespace Work.Pert

theorem liftF_defect_le_tauC {u : ℂ → ℂ} {σ α : ℂ} {Ξ Rm : ℝ}
    (hΞ : 0 < Ξ) (hα : α ≠ 0) (hσ : σ ≠ 0) (hRm : 0 < Rm)
    (hInF1 : MandelDim.InF1 α) (hαsmall : ‖α‖ ≤ 1 / 64)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) Rm))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) Rm, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) Rm)
    (hNT : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Pert.Qm Ξ α,
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ C * ‖Work.Pert.tauC σ α z‖ := by
  -- ## Step 1: a Lipschitz bound for `u` on `ball 0 (Rm/4)`, from boundedness + Cauchy
  have hRm4 : 0 < Rm / 4 := by linarith
  have hC8 : 0 ≤ 8 / Rm := by positivity
  have hub : ∀ z ∈ Metric.ball (0 : ℂ) Rm, ‖u z‖ ≤ 2 := fun z hz => (hu2 z hz).2
  obtain ⟨hderiv, _⟩ := scale_cauchy hRm le_rfl hu hub
  have hu2' : ∀ z ∈ Metric.ball (0 : ℂ) (Rm / 4), 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2 :=
    fun z hz => hu2 z (Metric.ball_subset_ball (by linarith) hz)
  have huL : ∀ z ∈ Metric.ball (0 : ℂ) (Rm / 4), ∀ w ∈ Metric.ball (0 : ℂ) (Rm / 4),
      ‖u z - u w‖ ≤ (8 / Rm) * ‖z - w‖ := by
    intro z hz w hw
    have hzlt : ‖z‖ < Rm / 4 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hwlt : ‖w‖ < Rm / 4 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hzs : z ∈ Metric.closedBall (0 : ℂ) (Rm / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have hws : w ∈ Metric.closedBall (0 : ℂ) (Rm / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have hdiff : ∀ x ∈ Metric.closedBall (0 : ℂ) (Rm / 2), DifferentiableAt ℂ u x := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hu.differentiableAt (Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_zero_right]; linarith))
    have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) (Rm / 2), ‖deriv u x‖ ≤ 8 / Rm := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hderiv x hx
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_closedBall (0 : ℂ) (Rm / 2)) hzs hws
    simpa only [norm_sub_rev] using hmvt
  -- ## Step 2: the analytic estimate for small `τ_f`, valid for every `z`
  obtain ⟨ε, K, hεpos, hKpos, hK⟩ :=
    liftF_sub_translation_le hRm4 hC8 hu2' huL hnorm hα hαsmall
  -- ## Step 3: the threshold split
  refine ⟨max K (1 / (32 * ε)), lt_of_lt_of_le hKpos (le_max_left _ _), ?_⟩
  intro z hz
  by_cases hsmall : ‖tauC σ α z‖ ≤ ε
  · calc ‖liftF u σ α z - (z + 1)‖ ≤ K * ‖tauC σ α z‖ := hK z hsmall
      _ ≤ max K (1 / (32 * ε)) * ‖tauC σ α z‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have hεlt : ε < ‖tauC σ α z‖ := lt_of_not_ge hsmall
    have h32e : (32 : ℝ) * ε ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hεpos)
    have hkey : (1 : ℝ) / 32 = (1 / (32 * ε)) * ε := by
      rw [div_mul_eq_mul_div, one_mul,
        div_eq_div_iff (by norm_num : (32 : ℝ) ≠ 0) h32e, one_mul]
      ring
    calc ‖liftF u σ α z - (z + 1)‖ ≤ 1 / 32 := hNT z hz
      _ = (1 / (32 * ε)) * ε := hkey
      _ ≤ (1 / (32 * ε)) * ‖tauC σ α z‖ :=
            mul_le_mul_of_nonneg_left (le_of_lt hεlt) (by positivity)
      _ ≤ max K (1 / (32 * ε)) * ‖tauC σ α z‖ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end Work.Pert
