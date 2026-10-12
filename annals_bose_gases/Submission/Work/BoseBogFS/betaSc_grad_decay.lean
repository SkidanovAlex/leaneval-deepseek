import ChallengeDeps
import Submission.Work.BoseBogFS.BogFSCompare
import Submission.Work.BoseBogFS.chat_W1_fderiv_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.betaSc_grad_decay`

The gradient of the scaled pairing coefficient `β(t) = βSc v h ρ μ t = Ŵ₁(√(ρ a)•t)/(a v)`
inherits the `1/(1+√(ρ a)‖t‖)` decay of `Ŵ₁` itself, with an **absolute** constant:

  `∃ K ≥ 0, ∀ t, ‖∇β(t)‖ ≤ K (1+R)³ √(ρ/a) / (1 + √(ρ a)‖t‖)`.

## Route

* `betaSc_eq` rewrites `β` as `(a v)⁻¹ · Ŵ₁(√(ρ a)•·)` with `Ŵ₁ = chat (W1fun v h (ell v μ))`;
* `Ŵ₁` is `C¹` (`Work.BoseB7AK.W1rows.W1hat_even_contDiff`, hence everywhere differentiable)
  and its gradient obeys the absolute bound `C(1+R)³/(1+‖q‖)`
  (`Work.BoseBogFS.chat_W1_fderiv_decay`);
* the chain rule for the composition of `Ŵ₁` with the dilation `s ↦ √(ρ a)•s` gives
  `‖∇β(t)‖ = (a v)⁻¹ · √(ρ a) · ‖∇Ŵ₁(√(ρ a)•t)‖`, and `(a v)⁻¹√(ρ a) = √(ρ/a)`.
-/

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `a⁻¹·√(ρ a) = √(ρ/a)` for `ρ > 0`, `a > 0` (both sides are nonnegative and have the
same square). -/
private lemma inv_mul_sqrt_eq_sqrt_div {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    a⁻¹ * Real.sqrt (ρ * a) = Real.sqrt (ρ / a) := by
  have hP : 0 < ρ * a := mul_pos hρ ha
  have hsq : (a⁻¹ * Real.sqrt (ρ * a)) ^ 2 = ρ / a := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hP.le]
    field_simp
  have hnn : 0 ≤ a⁻¹ * Real.sqrt (ρ * a) :=
    mul_nonneg (inv_nonneg.mpr ha.le) (Real.sqrt_nonneg _)
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]

theorem betaSc_grad_decay :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ},
      0 < R → 0 < ρ → 0 < _root_.BoseGases.a v → (∀ x, 0 ≤ v x) →
      _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      ∀ t : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (fun s : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.betaSc v h ρ μ s) t‖
          ≤ K * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v)
            / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖) := by
  obtain ⟨C, hC0, hC⟩ := chat_W1_fderiv_decay
  refine ⟨C, hC0, ?_⟩
  intro v h R ρ μ hR hρ hav hv hvrad hv_supp hRℓ t
  -- the box scale is positive (`R > 0` and `R ≤ ℓ·chiR0`)
  have hchi : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hℓ : 0 < Work.BoseFixR.ell v μ := by
    by_contra hcon
    have hcon' : Work.BoseFixR.ell v μ ≤ 0 := le_of_not_gt hcon
    have h2 : Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon' hchi.le
    linarith
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ hav
  -- the one-body kernel and the momentum scale
  set F : E3 → ℝ :=
    Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) with hF
  set c : ℝ := Real.sqrt (ρ * _root_.BoseGases.a v) with hcdef
  have hc : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.mpr hP
  -- `Ŵ₁` is `C¹`, hence differentiable everywhere
  have hcd : ContDiff ℝ 1 F := by
    rw [hF]
    exact (Work.BoseB7AK.W1rows.W1hat_even_contDiff hR hℓ hv hvrad hv_supp h hRℓ).2
  have hFd : DifferentiableAt ℝ F (c • t) := hcd.differentiable (by norm_num) (c • t)
  -- pointwise identification of `betaSc` with the dilated kernel
  have hfun : (fun s : E3 => Work.BoseBogFS.betaSc v h ρ μ s)
      = fun s : E3 => (_root_.BoseGases.a v)⁻¹ * F (c • s) := by
    funext s
    rw [betaSc_eq v hρ.ne' hav.ne' s, hF, hcdef]
  -- the chain rule
  have hlin : HasFDerivAt (fun s : E3 => c • s) (c • (1 : E3 →L[ℝ] E3)) t :=
    (hasFDerivAt_id t).const_smul c
  have hG : HasFDerivAt (fun s : E3 => (_root_.BoseGases.a v)⁻¹ * F (c • s))
      ((_root_.BoseGases.a v)⁻¹ •
        ((fderiv ℝ F (c • t)) ∘SL (c • (1 : E3 →L[ℝ] E3)))) t :=
    (hFd.hasFDerivAt.comp t hlin).const_smul ((_root_.BoseGases.a v)⁻¹)
  rw [hfun, hG.fderiv]
  -- the two estimates
  have hFn : ‖fderiv ℝ F (c • t)‖ ≤ C * (1 + R) ^ 3 / (1 + ‖c • t‖) := by
    rw [hF]
    exact hC (v := v) (h := h) (R := R) (ℓ := Work.BoseFixR.ell v μ)
      hR hℓ hv hvrad hv_supp hRℓ (c • t)
  have hLnorm : ‖c • (1 : E3 →L[ℝ] E3)‖ = c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, norm_one, mul_one]
  have hLb : ‖(fderiv ℝ F (c • t)) ∘SL (c • (1 : E3 →L[ℝ] E3))‖
      ≤ C * (1 + R) ^ 3 / (1 + ‖c • t‖) * c := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    rw [hLnorm]
    exact mul_le_mul_of_nonneg_right hFn hc.le
  have hstep : ‖(_root_.BoseGases.a v)⁻¹ •
        ((fderiv ℝ F (c • t)) ∘SL (c • (1 : E3 →L[ℝ] E3)))‖
      ≤ (_root_.BoseGases.a v)⁻¹ *
        (C * (1 + R) ^ 3 / (1 + ‖c • t‖) * c) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hav)]
    exact mul_le_mul_of_nonneg_left hLb (inv_nonneg.mpr hav.le)
  refine hstep.trans (le_of_eq ?_)
  -- `a⁻¹·(C(1+R)³/(1+√(ρa)‖t‖))·√(ρa) = C(1+R)³·√(ρ/a)/(1+√(ρa)‖t‖)`
  have hq : ‖c • t‖ = Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖ := by
    rw [hcdef, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hP)]
  rw [hq, hcdef]
  calc (_root_.BoseGases.a v)⁻¹ *
        (C * (1 + R) ^ 3 / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖) *
          Real.sqrt (ρ * _root_.BoseGases.a v))
      = ((_root_.BoseGases.a v)⁻¹ * Real.sqrt (ρ * _root_.BoseGases.a v)) *
          (C * (1 + R) ^ 3 / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖)) := by
        ring
    _ = Real.sqrt (ρ / _root_.BoseGases.a v) *
          (C * (1 + R) ^ 3 / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖)) := by
        rw [inv_mul_sqrt_eq_sqrt_div hρ hav]
    _ = C * (1 + R) ^ 3 * Real.sqrt (ρ / _root_.BoseGases.a v)
          / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖) := by
        ring

end Work.BoseBogFS
