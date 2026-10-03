import Mathlib
import Submission.Work.Pert.PinLogDev.liftF_sub_model_le_pointwise_wide
import Submission.Work.Pert.PinLogDev.tauC_sub_tau0_alpha
import Submission.Work.Pert.PinLogDev.tauC_sub_tau0_u0
import Submission.Work.Pert.PinLogDev.u_sub_hF_le
import Submission.Work.Pert.PinLogDev.u_sub_hF_le_inner
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.SmallOfNearOnConst
import Submission.Work.Pert.Ksub2.F0f_eq_model
import Submission.Work.Pert.PinLogDev.PinAux2
import Submission.Work.Pert.Ksub2.exists_model_data_full
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.dev_base_v3

/-!
# `Work.Pert.PinLogDev.deep_step_le`

The **deep step** bound: at a deep point `w` of the gate (`64 ≤ ‖w‖`, `‖α‖‖w‖ ≤ 2/3`), the
perturbed lift `F_f = liftF u σ α` and the limit model `F0 = F0f f₀ = τ₀ ∘ f₀ ∘ τ₀` agree to
`O(1/(M+1))`, uniformly in `M ≥ Ms` and in the perturbation.

The ingredients are:

* the *pointwise model comparison* `liftF_sub_model_le_pointwise_wide`, bounding the difference by
  `1000 (D+1) (η + δ₂)` with `η ≥ max (‖α‖, ‖u 0 - 1‖, ‖u (τ_f w) - hF (τ_f w)‖)` and
  `δ₂ ≥ ‖τ_f w - τ₀ w‖`;
* the *smallness of the normal-form data* `SmallOfNearOnConst`: for `δ₀ = 1/(1000(M+1))`,
  `‖u 0 - 1‖ ≤ 10 (δ₀/ρ² + δ₀/(ρ rr))`, `‖σ‖ ≤ 10 δ₀/ρ` and `‖α‖ ≤ 10 δ₀/ρ`;
* the *Schwarz comparison* `u_sub_hF_le_inner`, turning those into
  `‖u z - hF z‖ ≤ C (δ/ρ² + ‖σ‖/ρ + ‖u 0 - 1‖)` on the inner half of the model ball;
* the chart comparison `tauC_sub_tau0_u0`: `‖τ_f w - τ₀ w‖ ≤ C (‖α‖ + ‖u 0 - 1‖/‖w‖)`.

Every constant is chosen *before* `Ms`, and `Ms` is then taken so large that each `K/(M+1)`-term
is below its allotted threshold.
-/

namespace Work.Pert.PinLogDev

open Complex Metric
open scoped Topology

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-- `K / (M+1) ≤ c` whenever `K ≤ c * M`, `K ≥ 0` and `c > 0`. -/
private lemma div_succ_le_of_le {K c M : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (h : K ≤ c * M) :
    K / (M + 1) ≤ c := by
  have hM0 : 0 ≤ M := by nlinarith [hK, hc, h]
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  rw [div_le_iff₀ hM1]
  nlinarith [h, hc]

/-- The chart comparison with the `u 0`-factor: if `σ u₀ = 1 - e^{2πiα}` and the lattice
separation is *relative* (`(1/2)‖α‖‖w‖ ≤ dist (α w) ℤ`), then
`‖τ_f w - τ₀ w‖ ≤ C (‖α‖ + ‖u 0 - 1‖/‖w‖)`. -/
private theorem tauC_sub_tau0_u0_local :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {σ α u0 w : ℂ},
      σ * u0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) → α ≠ 0 →
      1 ≤ ‖w‖ → ‖α‖ * ‖w‖ ≤ 2 → ‖u0 - 1‖ ≤ 1 / 2 →
      (1 / 2) * (‖α‖ * ‖w‖) ≤ (⨅ k : ℤ, dist (α * w) (k : ℂ)) →
      ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ C * (‖α‖ + ‖u0 - 1‖ / ‖w‖) :=
  tauC_sub_tau0_u0

theorem deep_step_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) (Ξ rr : ℝ) (hrr : 0 < rr)
    (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ C Ms : ℝ, 0 ≤ C ∧ 0 < Ms ∧
    ∀ (M δ : ℝ) (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (w : ℂ),
      Ms ≤ M → 0 < δ → δ ≤ 1 / (1000 * (M + 1)) →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) δ →
      f 0 = 0 → MandelDim.InF1 α → α = MandelDim.rotOf f →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
      ‖α‖ * M ≤ 1 / 2 →
      w ∈ Work.Pert.Qm Ξ α → 64 ≤ ‖w‖ → ‖α‖ * ‖w‖ ≤ 2 / 3 → Ms ≤ ‖w‖ →
      ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ C / (M + 1) := by
  -- ## the model datum of the germ
  obtain ⟨hF, ρ₀, D, hρ₀pos, hρ₀le, hDnn, hF0, _hclD0, hf₀eq, hhFd, hhFderiv, hhFbnd⟩ :=
    Work.Pert.Ksub2.exists_model_data_full hd
  -- ## the smallness package
  obtain ⟨r₀, hr₀pos, _hr₀sub, hsmall⟩ := Work.Pert.SmallOfNearOnConst hd
  -- ## the chart comparison constant
  obtain ⟨Cδ, hCδnn, hδmain⟩ := tauC_sub_tau0_u0_local
  -- ## the model radius
  set ρ : ℝ := min (min ρ₀ r₀) rr / 2 with hρdef
  have hminpos : 0 < min (min ρ₀ r₀) rr := lt_min (lt_min hρ₀pos hr₀pos) hrr
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρle0 : ρ ≤ min (min ρ₀ r₀) rr := by rw [hρdef]; linarith
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρle0 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρr₀ : ρ ≤ r₀ := le_trans hρle0 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρrr : ρ ≤ rr := le_trans hρle0 (min_le_right _ _)
  have hρle4 : ρ ≤ 1 / 4 := by linarith [hρρ₀, hρ₀le]
  -- ## the constants (all chosen before `Ms`)
  set Ku : ℝ := 10 * (1 / (1000 * ρ ^ 2) + 1 / (1000 * ρ * rr)) with hKudef
  set Kd : ℝ := 10 / (1000 * ρ) with hKddef
  obtain ⟨Ci, hCinn, hinner⟩ := u_sub_hF_le_inner ρ ρ hρpos hρpos (le_refl ρ)
  set Kη : ℝ := Ci * (1 / (1000 * ρ ^ 2) + Kd / ρ + Ku) with hKηdef
  set ηC : ℝ := max 1 (max Ku (max Kd Kη)) with hηCdef
  set Dδ : ℝ := Cδ * (Kd + Ku) with hDδdef
  set Cfin : ℝ := 1000 * (D + 1) * (ηC + Dδ) with hCfindef
  set Ms : ℝ := max 1 (max 64 (max (8 * Ku) (max (1000 * ηC) (max (2 * Real.pi * Kd)
      (max (8 * Dδ / ρ) (max (16 / ρ) (max (2 / ρ₀) (1 / (500 * ρ))))))))) with hMsdef
  -- ## nonnegativity
  have hKunn : 0 ≤ Ku := by
    rw [hKudef]
    have h1 : 0 < 1 / (1000 * ρ ^ 2) := by positivity
    have h2 : 0 < 1 / (1000 * ρ * rr) := by positivity
    linarith
  have hKdnn : 0 ≤ Kd := by rw [hKddef]; positivity
  have hKηnn : 0 ≤ Kη := by
    rw [hKηdef]
    have h1 : 0 ≤ 1 / (1000 * ρ ^ 2) + Kd / ρ + Ku := by
      have h2 : 0 ≤ Kd / ρ := div_nonneg hKdnn hρpos.le
      have h3 : 0 < 1 / (1000 * ρ ^ 2) := by positivity
      linarith
    exact mul_nonneg hCinn h1
  have hηCnn : 0 ≤ ηC := by rw [hηCdef]; exact le_trans zero_le_one (le_max_left _ _)
  have hDδnn : 0 ≤ Dδ := by
    rw [hDδdef]; exact mul_nonneg hCδnn (add_nonneg hKdnn hKunn)
  have hCfinnn : 0 ≤ Cfin := by
    rw [hCfindef]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (add_nonneg hηCnn hDδnn)
  have hMspos : 0 < Ms := by rw [hMsdef]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨Cfin, Ms, hCfinnn, hMspos, ?_⟩
  -- ## the main block
  intro M δ f Df u σ α w hM hδpos hδle hnear hf0 hInF1 hαeq hudiff hubnd hform hnorm hgate
    hαM hwQm hw64 hαw hwMs
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  -- ## the thresholds encoded in `Ms`
  have hMs1 : (1 : ℝ) ≤ Ms := by rw [hMsdef]; exact le_max_left _ _
  have hMs64 : (64 : ℝ) ≤ Ms := by
    rw [hMsdef]; exact le_trans (le_max_left 64 _) (le_max_right 1 _)
  have hMsKu : 8 * Ku ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (8 * Ku) _) (le_trans (le_max_right 64 _) (le_max_right 1 _))
  have hMsηC : 1000 * ηC ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (1000 * ηC) _)
      (le_trans (le_max_right (8 * Ku) _) (le_trans (le_max_right 64 _) (le_max_right 1 _)))
  have hMsπ : 2 * Real.pi * Kd ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (2 * Real.pi * Kd) _)
      (le_trans (le_max_right (1000 * ηC) _)
        (le_trans (le_max_right (8 * Ku) _) (le_trans (le_max_right 64 _) (le_max_right 1 _))))
  have hMsDδ : 8 * Dδ / ρ ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (8 * Dδ / ρ) _)
      (le_trans (le_max_right (2 * Real.pi * Kd) _)
        (le_trans (le_max_right (1000 * ηC) _)
          (le_trans (le_max_right (8 * Ku) _)
            (le_trans (le_max_right 64 _) (le_max_right 1 _)))))
  have hMs16 : 16 / ρ ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (16 / ρ) _)
      (le_trans (le_max_right (8 * Dδ / ρ) _)
        (le_trans (le_max_right (2 * Real.pi * Kd) _)
          (le_trans (le_max_right (1000 * ηC) _)
            (le_trans (le_max_right (8 * Ku) _)
              (le_trans (le_max_right 64 _) (le_max_right 1 _))))))
  have hMsρ₀ : 2 / ρ₀ ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (2 / ρ₀) _)
      (le_trans (le_max_right (16 / ρ) _)
        (le_trans (le_max_right (8 * Dδ / ρ) _)
          (le_trans (le_max_right (2 * Real.pi * Kd) _)
            (le_trans (le_max_right (1000 * ηC) _)
              (le_trans (le_max_right (8 * Ku) _)
                (le_trans (le_max_right 64 _) (le_max_right 1 _)))))))
  have hMs500 : 1 / (500 * ρ) ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_right (2 / ρ₀) _)
      (le_trans (le_max_right (16 / ρ) _)
        (le_trans (le_max_right (8 * Dδ / ρ) _)
          (le_trans (le_max_right (2 * Real.pi * Kd) _)
            (le_trans (le_max_right (1000 * ηC) _)
              (le_trans (le_max_right (8 * Ku) _)
                (le_trans (le_max_right 64 _) (le_max_right 1 _)))))))
  -- ## the normalized small data
  have hnearρ : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) (1 / (1000 * (M + 1))) := by
    refine ⟨hnear.1, ?_, hnear.2.2.1, ?_⟩
    · intro z hz
      exact hnear.2.1 (Metric.closedBall_subset_closedBall hρrr hz)
    · intro z hz
      exact lt_of_lt_of_le (hnear.2.2.2 z (Metric.closedBall_subset_closedBall hρrr hz)) hδle
  have hδ₀pos : 0 < 1 / (1000 * (M + 1)) := by positivity
  have h2δ₀ : 2 * (1 / (1000 * (M + 1))) ≤ ρ := by
    have h : 1 ≤ Ms * (500 * ρ) := by
      have hh := hMs500
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 500 * ρ)] at hh
      exact hh
    have h2 : Ms * (500 * ρ) ≤ (M + 1) * (500 * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hgoal : 2 * (1 / (1000 * (M + 1))) = 2 / (1000 * (M + 1)) := by ring
    rw [hgoal, div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (M + 1))]
    nlinarith [h, h2]
  obtain ⟨hu0b, hσb, hrotb⟩ :=
    hsmall (f := f) (Df := Df) (ρ := ρ) (δ₀ := 1 / (1000 * (M + 1))) (rr := rr) (u := u)
      (σ := σ) hρpos hρr₀ hδ₀pos h2δ₀ hrr hnearρ hf0 hudiff hubnd hform
  -- ## the bounds in `1/(M+1)`-form
  have hKu_eq : 10 * (1 / (1000 * (M + 1)) / ρ ^ 2 + 1 / (1000 * (M + 1)) / (ρ * rr))
      = Ku / (M + 1) := by
    rw [hKudef]; field_simp; try ring
  have hKd_eq : 10 * (1 / (1000 * (M + 1))) / ρ = Kd / (M + 1) := by
    rw [hKddef]; field_simp; try ring
  have hu0_le : ‖u 0 - 1‖ ≤ Ku / (M + 1) := le_trans hu0b (le_of_eq hKu_eq)
  have hσ_le : ‖σ‖ ≤ Kd / (M + 1) := le_trans hσb (le_of_eq hKd_eq)
  have hα_le : ‖α‖ ≤ Kd / (M + 1) := by
    have h1 : ‖α‖ = ‖MandelDim.rotOf f‖ := by rw [hαeq]
    rw [h1]
    exact le_trans hrotb (le_of_eq hKd_eq)
  -- ## elementary consequences
  have hu0small : ‖u 0 - 1‖ ≤ 1 / 8 := by
    have h : Ku / (M + 1) ≤ 1 / 8 := by
      have h8 : 8 * Ku ≤ M := le_trans hMsKu hM
      have hKule : Ku ≤ (1 / 8) * M := by nlinarith
      exact div_succ_le_of_le hKunn (by norm_num) hKule
    linarith
  have hu0ge : (1 : ℝ) / 2 ≤ ‖u 0‖ := by
    have h := abs_norm_sub_norm_le (u 0) (1 : ℂ)
    rw [norm_one, abs_le] at h
    linarith [h.1, h.2]
  have hu0ne : u 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hu0ge; norm_num at hu0ge
  have hα0 : α ≠ 0 := by
    have h : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
    intro hh; rw [hh] at h; simp at h
  have hδ1 : ‖MandelDim.tau0 w‖ ≤ 1 / Ms := by
    have hval : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
      simp only [MandelDim.tau0, norm_div, norm_neg, norm_one]
    rw [hval]
    exact one_div_le_one_div_of_le hMspos hwMs
  have hδ1' : 1 / Ms ≤ 1 / 64 :=
    one_div_le_one_div_of_le (by norm_num) hMs64
  have hρ16 : 1 / Ms ≤ ρ / 16 := by
    have h : 16 ≤ Ms * ρ := by
      have hh := hMs16
      rw [div_le_iff₀ hρpos] at hh
      exact hh
    rw [div_le_iff₀ hMspos]
    nlinarith [h]
  have hDδρ : Dδ / (M + 1) ≤ ρ / 8 := by
    have hh : 8 * Dδ ≤ Ms * ρ := by
      have h := hMsDδ
      rw [div_le_iff₀ hρpos] at h
      exact h
    have h2 : Ms * ρ ≤ M * ρ := mul_le_mul_of_nonneg_right hM hρpos.le
    have hle : Dδ ≤ (ρ / 8) * M := by nlinarith
    exact div_succ_le_of_le hDδnn (by positivity) hle
  have hηtop : ηC / (M + 1) ≤ 1 / 1000 := by
    have h : 1000 * ηC ≤ M := le_trans hMsηC hM
    have hle : ηC ≤ (1 / 1000) * M := by nlinarith
    exact div_succ_le_of_le hηCnn (by norm_num) hle
  have hηpos : 0 < ηC / (M + 1) := by
    have h : 0 < ηC := by
      rw [hηCdef]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  have hαπ : ‖α‖ ≤ 1 / (2 * Real.pi) := by
    have h : 2 * Real.pi * Kd ≤ M := le_trans hMsπ hM
    have hle : Kd ≤ (1 / (2 * Real.pi)) * M := by
      have hπ : 0 < 2 * Real.pi := by positivity
      have h' := mul_le_mul_of_nonneg_left h (le_of_lt hπ)
      have hπ' : 0 < 1 / (2 * Real.pi) := by positivity
      have h'' := mul_le_mul_of_nonneg_left h (le_of_lt hπ')
      have he : (2 * Real.pi * Kd) * (1 / (2 * Real.pi)) = Kd := by field_simp
      linarith [h'', he]
    have h2 := div_succ_le_of_le hKdnn (by positivity) hle
    linarith [hα_le, h2]
  -- ## `τ_f w` is close to `τ₀ w`
  have hrel : (1 / 2) * (‖α‖ * ‖w‖) ≤ (⨅ k : ℤ, dist (α * w) (k : ℂ)) := by
    have h1 : ‖α * w‖ ≤ 2 / 3 := by rw [norm_mul]; exact hαw
    have h2 := half_norm_le_iInf_dist h1
    rwa [norm_mul] at h2
  have hw1 : (1 : ℝ) ≤ ‖w‖ := by linarith
  have hαw2 : ‖α‖ * ‖w‖ ≤ 2 := by linarith
  have hσ₀ : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [← hnorm]; ring
  have hδ₂ : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ Dδ / (M + 1) := by
    have hmain := hδmain hσ₀ hα0 hw1 hαw2 (by linarith) hrel
    have h2 : ‖u 0 - 1‖ / ‖w‖ ≤ Ku / (M + 1) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖w‖)]
      have hKnn : 0 ≤ Ku / (M + 1) := div_nonneg hKunn hM1.le
      have h3 : (Ku / (M + 1)) * 1 ≤ (Ku / (M + 1)) * ‖w‖ :=
        mul_le_mul_of_nonneg_left hw1 hKnn
      linarith [hu0_le, h3]
    calc ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖
        ≤ Cδ * (‖α‖ + ‖u 0 - 1‖ / ‖w‖) := hmain
      _ ≤ Cδ * (Kd / (M + 1) + Ku / (M + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hCδnn
            linarith
      _ = Dδ / (M + 1) := by
            rw [hDδdef]; field_simp; try ring
  have hτf_le : ‖Work.Pert.tauC σ α w‖ ≤ ρ / 2 := by
    have hsplit : ‖Work.Pert.tauC σ α w‖
        ≤ ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ + ‖MandelDim.tau0 w‖ := by
      have h := norm_add_le (Work.Pert.tauC σ α w - MandelDim.tau0 w) (MandelDim.tau0 w)
      simpa using h
    linarith [hsplit, hδ₂, hDδρ, hδ1, hρ16, hρpos]
  have hτf_mem : Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith [hτf_le, hρpos]
  -- ## the Schwarz comparison `u ≈ hF` at `τ_f w`
  have hf₀diffρ : DifferentiableOn ℂ f₀ (Metric.ball (0 : ℂ) ρ) := by
    have hballD0 : Metric.ball (0 : ℂ) ρ ⊆ D₀ := fun z hz =>
      hrrD (Metric.closedBall_subset_closedBall hρrr (Metric.ball_subset_closedBall hz))
    exact hd.2.2.1.mono hballD0
  have hudiffρ : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ) :=
    hudiff.mono (Metric.ball_subset_ball hρrr)
  have hubndρ : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖u z‖ ≤ 2 := fun z hz =>
    (hubnd z (Metric.ball_subset_ball hρrr hz)).2
  have hhFcont : ContinuousAt hF 0 :=
    (hhFd.differentiableAt (Metric.ball_mem_nhds 0 hρ₀pos)).continuousAt
  have hhFb2ρ : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖hF z‖ ≤ 2 := fun z hz =>
    le_trans (hhFbnd z (Metric.ball_subset_ball hρρ₀ hz)) (by norm_num)
  have hf₀eqρ : ∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF z := fun z hz =>
    hf₀eq z (Metric.ball_subset_ball hρρ₀ hz)
  have hformρ : ∀ z ∈ Metric.ball (0 : ℂ) ρ, f z = z + z * (z - σ) * u z := fun z hz =>
    hform z (Metric.ball_subset_ball hρrr hz)
  have hf₀0 : f₀ 0 = 0 := hd.2.2.2.1
  have hηloc : ‖u 0 - hF 0‖ ≤ Ku / (M + 1) := by rw [hF0]; exact hu0_le
  have huτf : ‖u (Work.Pert.tauC σ α w) - hF (Work.Pert.tauC σ α w)‖ ≤ Kη / (M + 1) := by
    have happ := hinner (f := f) (Df := Df) (L := Metric.closedBall (0 : ℂ) ρ)
      (δ := 1 / (1000 * (M + 1))) (σ := σ) (η := Ku / (M + 1))
      hnearρ (le_refl _) hf₀diffρ hudiffρ hubndρ hhFcont hhFb2ρ hf₀eqρ hformρ hf₀0
      (le_of_lt (by positivity : (0 : ℝ) < Ku / (M + 1))) hηloc
      (Work.Pert.tauC σ α w) hτf_mem hτf_le
    refine le_trans happ ?_
    rw [hKηdef]
    have hAB : (1 / (1000 * (M + 1))) / ρ ^ 2 + ‖σ‖ / ρ + Ku / (M + 1)
        ≤ (1 / (1000 * ρ ^ 2) + Kd / ρ + Ku) / (M + 1) := by
      have h1 : (1 / (1000 * (M + 1))) / ρ ^ 2 = (1 / (1000 * ρ ^ 2)) / (M + 1) := by
        field_simp
      have h2 : ‖σ‖ / ρ ≤ (Kd / ρ) / (M + 1) := by
        have h2a : ‖σ‖ / ρ ≤ (Kd / (M + 1)) / ρ := div_le_div_of_nonneg_right hσ_le hρpos.le
        have h2b : (Kd / (M + 1)) / ρ = (Kd / ρ) / (M + 1) := by
          field_simp
        linarith [h2a, h2b.le, h2b.ge]
      have h3 : (1 / (1000 * ρ ^ 2)) / (M + 1) + (Kd / ρ) / (M + 1) + Ku / (M + 1)
          = (1 / (1000 * ρ ^ 2) + Kd / ρ + Ku) / (M + 1) := by
        rw [← add_div, ← add_div]
      linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
    calc Ci * ((1 / (1000 * (M + 1))) / ρ ^ 2 + ‖σ‖ / ρ + Ku / (M + 1))
        ≤ Ci * ((1 / (1000 * ρ ^ 2) + Kd / ρ + Ku) / (M + 1)) :=
          mul_le_mul_of_nonneg_left hAB hCinn
      _ = Ci * (1 / (1000 * ρ ^ 2) + Kd / ρ + Ku) / (M + 1) := by ring
  -- ## the η-bookkeeping
  have hαη : ‖α‖ ≤ ηC / (M + 1) := by
    have h : Kd ≤ ηC := by
      rw [hηCdef]
      exact le_trans (le_max_left Kd Kη) (le_trans (le_max_right Ku _) (le_max_right 1 _))
    calc ‖α‖ ≤ Kd / (M + 1) := hα_le
      _ ≤ ηC / (M + 1) := div_le_div_of_nonneg_right h hM1.le
  have hu0η : ‖u 0 - 1‖ ≤ ηC / (M + 1) := by
    have h : Ku ≤ ηC := by
      rw [hηCdef]
      exact le_trans (le_max_left Ku _) (le_max_right 1 _)
    calc ‖u 0 - 1‖ ≤ Ku / (M + 1) := hu0_le
      _ ≤ ηC / (M + 1) := div_le_div_of_nonneg_right h hM1.le
  have huτη : ‖u (Work.Pert.tauC σ α w) - hF (Work.Pert.tauC σ α w)‖ ≤ ηC / (M + 1) := by
    have h : Kη ≤ ηC := by
      rw [hηCdef]
      exact le_trans (le_max_right Kd Kη) (le_trans (le_max_right Ku _) (le_max_right 1 _))
    exact le_trans huτf (div_le_div_of_nonneg_right h hM1.le)
  have hδsum : 1 / Ms + Dδ / (M + 1) ≤ ρ / 4 := by
    linarith [hρ16, hDδρ, hρpos]
  have hδ₂nn : 0 ≤ Dδ / (M + 1) := div_nonneg hDδnn hM1.le
  have hhFdρ : DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) ρ) :=
    hhFd.mono (Metric.ball_subset_ball hρρ₀)
  have hhFderivρ : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv hF z‖ ≤ D := fun z hz =>
    hhFderiv z (Metric.ball_subset_ball hρρ₀ hz)
  have hhw : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw64; norm_num at hw64
  have hwide := liftF_sub_model_le_pointwise_wide (u := u) (hF := hF) (σ := σ) (α := α) (w := w)
    (ρ := ρ) (D := D) (η := ηC / (M + 1)) (δ₁ := 1 / Ms) (δ₂ := Dδ / (M + 1))
    hρpos hρle4 hDnn hηpos hηtop hδ1 hδ1' hδ₂ hδ₂nn hδsum hhFdρ hhFderivρ
    (fun z hz => hhFbnd z (Metric.ball_subset_ball hρρ₀ hz))
    huτη hu0η hα0 hαη hαπ hnorm hhw hαw2
  -- ## the limit model
  have hτ₀mem : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρ₀ := by
    have hw1' : 1 / ‖w‖ < ρ₀ := by
      have hh : 2 ≤ Ms * ρ₀ := by
        have h := hMsρ₀
        rw [div_le_iff₀ hρ₀pos] at h
        exact h
      have h2 : 1 / Ms ≤ ρ₀ / 2 := by
        rw [div_le_iff₀ hMspos]
        nlinarith [hh]
      have h3 : 1 / ‖w‖ ≤ 1 / Ms := one_div_le_one_div_of_le hMspos hwMs
      linarith [h3, h2, hρ₀pos]
    have hval : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
      simp only [MandelDim.tau0, norm_div, norm_neg, norm_one]
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hval]
    exact hw1'
  have hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0 := by
    intro hzero
    have hnorm : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ = 1 := by
      have h2 : MandelDim.tau0 w * hF (MandelDim.tau0 w) = -1 := by
        linear_combination hzero
      rw [h2, norm_neg, norm_one]
    have hle : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ≤ 1 / 2 := by
      rw [norm_mul]
      have h2 : ‖hF (MandelDim.tau0 w)‖ ≤ 3 / 2 := hhFbnd _ hτ₀mem
      have h4 : 1 / Ms ≤ 1 / 64 := hδ1'
      nlinarith [h2, hδ1, h4, norm_nonneg (MandelDim.tau0 w)]
    linarith [hnorm, hle]
  have hF0f : Work.Pert.F0f f₀ w
      = w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) :=
    Work.Pert.Ksub2.F0f_eq_model hhw (hf₀eq _ hτ₀mem) hden
  -- ## conclusion
  calc ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖
      = ‖Work.Pert.liftF u σ α w
          - (w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))‖ := by
        rw [hF0f]
    _ ≤ 1000 * (D + 1) * (ηC / (M + 1) + Dδ / (M + 1)) := hwide
    _ = Cfin / (M + 1) := by
        rw [hCfindef]; ring

end Work.Pert.PinLogDev
