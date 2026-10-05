import Mathlib
import Submission.Work.RPV.Defs

/-!
# B4 · `flux_two_point`: the two-point flux identity

For a `2π`-periodic curve family `Γ : ℝ → ℝ → ℂ` (smooth in both variables, `C¹` is enough) and
two parameters `a b`, the difference of the ω_ℂ-fluxes of the two closed curves `Γ a ·` and `Γ b ·`
equals the flux of the "sum/difference" curve `(Γ b - Γ a, (Γ b)' + (Γ a)')`:

```
∮ ω_ℂ(Γ_b, Γ_b') - ∮ ω_ℂ(Γ_a, Γ_a') = ∮ ω_ℂ(Γ_b - Γ_a, Γ_b' + Γ_a').
```

Indeed `ω_ℂ` is the (antisymmetric, ℝ-bilinear) form `Im(conj x * y) = x.re * y.im - x.im * y.re`,
so expanding the right-hand integrand produces exactly the left-hand integrand plus the total
derivative `d/dt ω_ℂ(Γ_b t, Γ_a t)`, whose integral over one period vanishes by periodicity.

## Contents

* `ωC_eq`                -- `ω_ℂ` in real coordinates;
* `hasDerivAt_ωC`        -- the derivative of a pairing `t ↦ ω_ℂ (F t) (G t)`;
* `integral_omegaC_cross_zero` -- the cross term integrates to `0` over a period (FTC + periodicity);
* `flux_two_point`       -- the requested identity.
-/

open Complex Real MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B4

/-- `ω_ℂ(a,b) = Im(conj a * b)` in real coordinates: `a.re * b.im - a.im * b.re`. -/
lemma ωC_eq (a b : ℂ) : Work.RPV.ωC a b = a.re * b.im - a.im * b.re := by
  simp only [Work.RPV.ωC, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Derivative of the pairing `t ↦ ω_ℂ (F t) (G t)`: it is `ω_ℂ(F't, G t) + ω_ℂ(F t, G't)`,
because `ω_ℂ` is a bilinear form and `t ↦ (F t, G t)` is differentiable. -/
lemma hasDerivAt_ωC {F G : ℝ → ℂ} {t : ℝ} {f' g' : ℂ}
    (hF : HasDerivAt F f' t) (hG : HasDerivAt G g' t) :
    HasDerivAt (fun s => Work.RPV.ωC (F s) (G s))
      (Work.RPV.ωC f' (G t) + Work.RPV.ωC (F t) g') t := by
  have hFre : HasDerivAt (fun s => (F s).re) f'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hF
  have hFim : HasDerivAt (fun s => (F s).im) f'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hF
  have hGre : HasDerivAt (fun s => (G s).re) g'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hG
  have hGim : HasDerivAt (fun s => (G s).im) g'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hG
  have h := (hFre.mul hGim).sub (hFim.mul hGre)
  have hfun : (fun s => Work.RPV.ωC (F s) (G s))
      = fun s => (F s).re * (G s).im - (F s).im * (G s).re := by
    funext s; exact ωC_eq _ _
  have hd : Work.RPV.ωC f' (G t) + Work.RPV.ωC (F t) g'
      = f'.re * (G t).im + (F t).re * g'.im - (f'.im * (G t).re + (F t).im * g'.re) := by
    rw [ωC_eq, ωC_eq]; ring
  rw [hfun, hd]
  exact h

/-- The cross term `ω_ℂ(F', G) + ω_ℂ(F, G')` is the derivative of `t ↦ ω_ℂ(F t, G t)`, hence its
integral over one period vanishes when `F` and `G` are `2π`-periodic. -/
theorem integral_omegaC_cross_zero (F G : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFper : ∀ t, F (t + 2 * π) = F t) (hGper : ∀ t, G (t + 2 * π) = G t) :
    (∫ t in (0 : ℝ)..(2 * π),
      (Work.RPV.ωC (deriv F t) (G t) + Work.RPV.ωC (F t) (deriv G t))) = 0 := by
  have hD : ∀ t, HasDerivAt F (deriv F t) t := fun t => (hF.differentiable (by simp) t).hasDerivAt
  have hD' : ∀ t, HasDerivAt G (deriv G t) t := fun t => (hG.differentiable (by simp) t).hasDerivAt
  have hderiv : ∀ t, deriv (fun s => Work.RPV.ωC (F s) (G s)) t
      = Work.RPV.ωC (deriv F t) (G t) + Work.RPV.ωC (F t) (deriv G t) :=
    fun t => (hasDerivAt_ωC (hD t) (hD' t)).deriv
  have hcontω : Continuous (fun t =>
      Work.RPV.ωC (deriv F t) (G t) + Work.RPV.ωC (F t) (deriv G t)) :=
    (Complex.continuous_im.comp ((continuous_star.comp (hF.continuous_deriv le_rfl)).mul hG.continuous)).add
      (Complex.continuous_im.comp ((continuous_star.comp hF.continuous).mul (hG.continuous_deriv le_rfl)))
  rw [← funext hderiv]
  rw [intervalIntegral.integral_deriv_eq_sub]
  · have e1 := hFper 0; simp only [zero_add] at e1
    have e2 := hGper 0; simp only [zero_add] at e2
    rw [e1, e2]; ring
  · intro x hx; exact (hasDerivAt_ωC (hD x) (hD' x)).differentiableAt
  · rw [funext hderiv]; exact hcontω.intervalIntegrable _ _

/-- The two-point flux identity: `∮ ω_ℂ(Γ_b, Γ_b') - ∮ ω_ℂ(Γ_a, Γ_a') = ∮ ω_ℂ(Γ_b - Γ_a, Γ_b' + Γ_a')`
for a smooth `2π`-periodic family `Γ`. -/
theorem flux_two_point (Γ : ℝ → ℝ → ℂ) (hΓ : ContDiff ℝ 1 (fun z : ℝ × ℝ => Γ z.1 z.2))
    (hper : ∀ σ t, Γ σ (t + 2 * π) = Γ σ t) (a b : ℝ) :
    (∫ t in (0:ℝ)..(2*π), Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t))
      - (∫ t in (0:ℝ)..(2*π), Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t))
      = ∫ t in (0:ℝ)..(2*π), Work.RPV.ωC (Γ b t - Γ a t)
          (deriv (fun s => Γ b s) t + deriv (fun s => Γ a s) t) := by
  have hb : ContDiff ℝ 1 (fun t : ℝ => Γ b t) := hΓ.comp (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff ℝ 1 (fun t : ℝ => Γ a t) := hΓ.comp (contDiff_const.prodMk contDiff_id)
  -- the pure bilinearity expansion of the right-hand integrand
  have key : ∀ t, Work.RPV.ωC (Γ b t - Γ a t)
        (deriv (fun s => Γ b s) t + deriv (fun s => Γ a s) t)
      = (Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)
          - Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t))
        + (Work.RPV.ωC (deriv (fun s => Γ b s) t) (Γ a t)
          + Work.RPV.ωC (Γ b t) (deriv (fun s => Γ a s) t)) := by
    intro t
    simp only [ωC_eq, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    ring
  -- the cross term integrates to zero
  have hcross : (∫ t in (0:ℝ)..(2*π), (Work.RPV.ωC (deriv (fun s => Γ b s) t) (Γ a t)
      + Work.RPV.ωC (Γ b t) (deriv (fun s => Γ a s) t))) = 0 :=
    integral_omegaC_cross_zero (fun t => Γ b t) (fun t => Γ a t) hb ha
      (fun t => hper b t) (fun t => hper a t)
  have hIntA : IntervalIntegrable
      (fun t => Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)) volume 0 (2*π) :=
    (Complex.continuous_im.comp
      ((continuous_star.comp hb.continuous).mul (hb.continuous_deriv le_rfl))).intervalIntegrable _ _
  have hIntB : IntervalIntegrable
      (fun t => Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t)) volume 0 (2*π) :=
    (Complex.continuous_im.comp
      ((continuous_star.comp ha.continuous).mul (ha.continuous_deriv le_rfl))).intervalIntegrable _ _
  have hIntX : IntervalIntegrable (fun t => (Work.RPV.ωC (deriv (fun s => Γ b s) t) (Γ a t)
      + Work.RPV.ωC (Γ b t) (deriv (fun s => Γ a s) t))) volume 0 (2*π) :=
    ((Complex.continuous_im.comp
        ((continuous_star.comp (hb.continuous_deriv le_rfl)).mul ha.continuous)).add
      (Complex.continuous_im.comp
        ((continuous_star.comp hb.continuous).mul (ha.continuous_deriv le_rfl)))).intervalIntegrable _ _
  have hIntAB : IntervalIntegrable (fun t => (Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)
          - Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t))) volume 0 (2*π) := hIntA.sub hIntB
  have hc : (∫ t in (0:ℝ)..(2*π), Work.RPV.ωC (Γ b t - Γ a t)
        (deriv (fun s => Γ b s) t + deriv (fun s => Γ a s) t))
      = ∫ t in (0:ℝ)..(2*π), ((Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)
          - Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t))
        + (Work.RPV.ωC (deriv (fun s => Γ b s) t) (Γ a t)
          + Work.RPV.ωC (Γ b t) (deriv (fun s => Γ a s) t))) :=
    intervalIntegral.integral_congr (fun t ht => key t)
  have h1 : (∫ t in (0:ℝ)..(2*π), ((Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)
          - Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t))
        + (Work.RPV.ωC (deriv (fun s => Γ b s) t) (Γ a t)
          + Work.RPV.ωC (Γ b t) (deriv (fun s => Γ a s) t))))
      = (∫ t in (0:ℝ)..(2*π), (Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)
          - Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t)))
        + (∫ t in (0:ℝ)..(2*π), (Work.RPV.ωC (deriv (fun s => Γ b s) t) (Γ a t)
          + Work.RPV.ωC (Γ b t) (deriv (fun s => Γ a s) t))) :=
    intervalIntegral.integral_add hIntAB hIntX
  have h2 : (∫ t in (0:ℝ)..(2*π), (Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t)
          - Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t)))
      = (∫ t in (0:ℝ)..(2*π), Work.RPV.ωC (Γ b t) (deriv (fun s => Γ b s) t))
        - (∫ t in (0:ℝ)..(2*π), Work.RPV.ωC (Γ a t) (deriv (fun s => Γ a s) t)) :=
    intervalIntegral.integral_sub hIntA hIntB
  rw [hc, h1, h2, hcross]
  ring

end Work.RPB.B4
