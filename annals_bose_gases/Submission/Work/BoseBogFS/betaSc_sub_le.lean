import ChallengeDeps
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.betaSc_grad_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem betaSc_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ rlo Δ : ℝ},
      0 < R → 0 < ρ → 0 < _root_.BoseGases.a v → (∀ x, 0 ≤ v x) →
      _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      0 ≤ Δ → 0 < rlo → ∀ t t' : EuclideanSpace ℝ (Fin 3), ‖t - t'‖ ≤ Δ → rlo + Δ ≤ ‖t'‖ →
        |Work.BoseBogFS.betaSc v h ρ μ t - Work.BoseBogFS.betaSc v h ρ μ t'|
          ≤ K * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v) * Δ
              / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * rlo) := by
  obtain ⟨K, hK0, hK⟩ := betaSc_grad_decay
  refine ⟨K, hK0, ?_⟩
  intro v h R ρ μ rlo Δ hR hρ hav hv hvrad hv_supp hRℓ hΔ hrlo t t' hdist hfar
  -- the gradient bound of `betaSc_grad_decay`, at the chapter's parameters
  have hgrad := hK (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ)
    hR hρ hav hv hvrad hv_supp hRℓ
  have hs : 0 < Real.sqrt (ρ * _root_.BoseGases.a v) :=
    Real.sqrt_pos.mpr (mul_pos hρ hav)
  have hdenpos : 0 < 1 + Real.sqrt (ρ * _root_.BoseGases.a v) * rlo := by positivity
  have hCnn : 0 ≤ K * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v)
      / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * rlo) := by positivity
  -- the box scale is positive (`R > 0` together with `R ≤ ℓ·chiR0`)
  have hchi : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hℓ : 0 < Work.BoseFixR.ell v μ := by
    by_contra hcon
    have hcon' : Work.BoseFixR.ell v μ ≤ 0 := le_of_not_gt hcon
    have h2 : Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon' hchi.le
    linarith
  -- `Ŵ₁` is `C¹`, so the dilated composition `β` is differentiable everywhere
  have hcd : ContDiff ℝ 1
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))) :=
    (Work.BoseB7AK.W1rows.W1hat_even_contDiff hR hℓ hv hvrad hv_supp h hRℓ).2
  have hGd : Differentiable ℝ
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))) :=
    hcd.differentiable (by norm_num)
  have hfun : (fun s : E3 => Work.BoseBogFS.betaSc v h ρ μ s)
      = fun s : E3 => (_root_.BoseGases.a v)⁻¹ *
          Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Real.sqrt (ρ * _root_.BoseGases.a v) • s) := by
    funext s
    rw [betaSc_eq v hρ.ne' hav.ne' s]
  have hdiff : ∀ x ∈ Metric.closedBall t' Δ,
      DifferentiableAt ℝ (fun s : E3 => Work.BoseBogFS.betaSc v h ρ μ s) x := by
    intro x _
    rw [hfun]
    fun_prop
  -- the uniform gradient bound on the ball of radius `Δ` about `t'`
  have hb : ∀ x ∈ Metric.closedBall t' Δ,
      ‖fderiv ℝ (fun s : E3 => Work.BoseBogFS.betaSc v h ρ μ s) x‖
        ≤ K * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v)
            / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * rlo) := by
    intro x hx
    have hxd : ‖x - t'‖ ≤ Δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hx; exact hx
    -- every point of the ball has norm at least `rlo`
    have hnorm : rlo ≤ ‖x‖ := by
      have h1 : ‖t'‖ ≤ ‖x‖ + ‖x - t'‖ := by
        calc ‖t'‖ = ‖x - (x - t')‖ := by abel
          _ ≤ ‖x‖ + ‖x - t'‖ := norm_sub_le x (x - t')
      linarith
    refine (hgrad x).trans ?_
    have hnum : 0 ≤ K * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v) := by positivity
    have hden : 1 + Real.sqrt (ρ * _root_.BoseGases.a v) * rlo
        ≤ 1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖x‖ := by
      nlinarith [hnorm, Real.sqrt_nonneg (ρ * _root_.BoseGases.a v)]
    exact div_le_div_of_nonneg_left hnum hdenpos hden
  -- the mean value theorem along the segment from `t'` to `t` (inside that ball)
  have hMVT := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (x := t') (y := t)
    hdiff hb (convex_closedBall t' Δ)
    (by simpa [Metric.mem_closedBall] using hΔ)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist)
  have hle : ‖(fun s : E3 => Work.BoseBogFS.betaSc v h ρ μ s) t
        - (fun s : E3 => Work.BoseBogFS.betaSc v h ρ μ s) t'‖
      ≤ (K * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v)
            / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * rlo)) * Δ :=
    hMVT.trans (mul_le_mul_of_nonneg_left hdist hCnn)
  rw [← Real.norm_eq_abs]
  refine hle.trans (le_of_eq ?_)
  ring

end Work.BoseBogFS
