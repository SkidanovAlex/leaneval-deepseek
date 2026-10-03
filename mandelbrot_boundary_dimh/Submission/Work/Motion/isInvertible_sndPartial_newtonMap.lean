import Mathlib
import Submission.Work.Motion.pertSetup
import Submission.Work.Motion.differentiableAt_Fmap
import Submission.Work.Motion.deriv_Fmap

namespace Work.Motion

open Set Metric Filter in
/-- The partial derivative in the second (`w`) variable of the Newton residual
`p ↦ (Tc p.1.1)^[m](τ p.1.2 + p.2) - p.1.2` at `u` is invertible, since it is multiplication by
`deriv (Fmap τ m u.1) u.2`, which is within `b/4` of `Bmap τ m u.1` of norm `≥ b > 0`. -/
theorem isInvertible_sndPartial_newtonMap {τ : ℂ → ℂ} {m : ℕ} {u : (ℂ × ℂ) × ℂ} {b ε : ℝ}
    (hb : 0 < b) (hτ : DifferentiableAt ℂ τ u.1.2)
    (hB : b ≤ ‖Work.Motion.Pert.Bmap τ m u.1‖)
    (hbd : ∀ w ∈ Metric.closedBall (0 : ℂ) ε,
      ‖deriv (Work.Motion.Pert.Fmap τ m u.1) w - Work.Motion.Pert.Bmap τ m u.1‖ ≤ b / 4)
    (hu : u.2 ∈ Metric.closedBall (0 : ℂ) ε) :
    ((fderiv ℂ (fun p : (ℂ × ℂ) × ℂ => Work.Motion.Pert.TcIter m (p.1.1, τ p.1.2 + p.2) - p.1.2) u) ∘L
      (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ)).IsInvertible := by
  -- abbreviation for the Newton residual
  set g : (ℂ × ℂ) × ℂ → ℂ :=
    fun p => Pert.TcIter m (p.1.1, τ p.1.2 + p.2) - p.1.2 with hgdef
  -- `g` is complex differentiable at `u`
  have hg_diff : DifferentiableAt ℂ g u := by
    rw [hgdef]
    have h1 : DifferentiableAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.1) u :=
      (differentiableAt_fst (p := u.1)).comp u (differentiableAt_fst (p := u))
    have h2 : DifferentiableAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.2) u :=
      (differentiableAt_snd (p := u.1)).comp u (differentiableAt_fst (p := u))
    have h3 : DifferentiableAt ℂ (fun p : (ℂ × ℂ) × ℂ => τ p.1.2 + p.2) u :=
      (hτ.comp u h2).add (differentiableAt_snd (p := u))
    have h4 : DifferentiableAt ℂ (fun p : (ℂ × ℂ) × ℂ => (p.1.1, τ p.1.2 + p.2)) u :=
      h1.prodMk h3
    exact ((Pert.differentiable_TcIter m).differentiableAt.comp u h4).sub h2
  -- the translation `w ↦ u + (0, w)` has derivative `inr` at `0`
  have hΦ0 : (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w) 0 = u := by simp
  have hΦF : HasFDerivAt (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)
      (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ) 0 :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ)).const_add u
  have hΦfderiv : fderiv ℂ (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w) 0
      = ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ := hΦF.fderiv
  -- chain rule: the partial derivative is the derivative of `g ∘ Φ` at `0`
  have hcomp : fderiv ℂ (g ∘ (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)) 0
      = (fderiv ℂ g u) ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ := by
    have hgd : DifferentiableAt ℂ g
        ((fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w) 0) := by
      rw [hΦ0]; exact hg_diff
    have hkey : fderiv ℂ (g ∘ (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)) 0
        = (fderiv ℂ g u) ∘SL ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ := by
      simp only [fderiv_comp
        (f := fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w) 0 hgd
        hΦF.differentiableAt, hΦ0, hΦfderiv]
    exact hkey
  -- the composite is a translate of `Fmap`
  have heq : g ∘ (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)
      = fun w => Pert.Fmap τ m u.1 (u.2 + w) + Pert.Amap τ m u.1 := by
    funext w
    change g (u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)
      = Pert.Fmap τ m u.1 (u.2 + w) + Pert.Amap τ m u.1
    rw [hgdef]
    simp only [Pert.Fmap_apply, Pert.Amap_apply, ContinuousLinearMap.inr_apply,
      Prod.fst_add, Prod.snd_add, add_zero]
    ring
  -- derivative of the translate of `Fmap`
  have hψderiv : deriv (fun w : ℂ => Pert.Fmap τ m u.1 (u.2 + w) + Pert.Amap τ m u.1) 0
      = deriv (Pert.Fmap τ m u.1) u.2 := by
    have houter : HasDerivAt (Pert.Fmap τ m u.1) (deriv (Pert.Fmap τ m u.1) u.2)
        ((fun w : ℂ => u.2 + w) 0) := by
      simpa using (differentiableAt_Fmap τ m u.1 u.2).hasDerivAt
    have hshift : HasDerivAt (fun w : ℂ => u.2 + w) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add u.2
    have h2 := (houter.comp 0 hshift).add_const (Pert.Amap τ m u.1)
    simpa [Function.comp_apply, mul_one] using h2.deriv
  -- the value of the partial derivative at `1`
  have h1 : fderiv ℂ g u (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ 1)
      = deriv (Pert.Fmap τ m u.1) u.2 := by
    have hc1 : fderiv ℂ (g ∘ (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)) 0 1
        = fderiv ℂ g u (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ 1) := by
      simp only [hcomp, ContinuousLinearMap.comp_apply]
    rw [← hc1]
    change deriv (g ∘ (fun w : ℂ => u + ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ w)) 0
      = deriv (Pert.Fmap τ m u.1) u.2
    rw [heq]
    exact hψderiv
  -- identify the linear map with multiplication by the scalar derivative
  have hT : (fderiv ℂ g u) ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ
      = ContinuousLinearMap.toSpanSingleton ℂ (deriv (Pert.Fmap τ m u.1) u.2) := by
    apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one]
    exact h1
  -- the scalar is nonzero
  have hc_ne : deriv (Pert.Fmap τ m u.1) u.2 ≠ 0 := by
    intro h0
    have hbnd := hbd u.2 hu
    rw [h0, zero_sub, norm_neg] at hbnd
    linarith
  rw [hT]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℂ (deriv (Pert.Fmap τ m u.1) u.2)⁻¹) ?_ ?_
  · apply ContinuousLinearMap.ext_ring
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, inv_mul_cancel₀ hc_ne]
  · apply ContinuousLinearMap.ext_ring
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_inv_cancel₀ hc_ne]

end Work.Motion
