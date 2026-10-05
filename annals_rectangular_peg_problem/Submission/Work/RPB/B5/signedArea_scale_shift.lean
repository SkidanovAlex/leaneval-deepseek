import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.area_normalised

/-!
# `signedArea_scale_shift`: the signed area of a scaled, shifted curve

Node B5 needs the signed area of any homothetic image `t ↦ R · c (t + ψ)` of the curves of a
`CurveIsotopy`:

`signedArea (t ↦ (R : ℂ) * CI.c τ (t + ψ)) = R ^ 2 * π`  for every `τ ∈ [0,1]`.

Two independent facts produce this.

* **Scaling.**  `ω_ℂ` is a real bilinear form, so the diagonal scaling `z ↦ R z` by a *real* `R`
  multiplies it by `R ^ 2`; `signedArea_const_mul` (from `Submission.Work.RPB.B5.area_normalised`)
  records exactly `signedArea (t ↦ (R : ℂ) * c t) = R ^ 2 * signedArea c`, with no regularity
  hypothesis on `c` (Mathlib's `deriv` vanishes at non-differentiability points, where the
  scaled curve is likewise non-differentiable).

* **Shifting.**  Translating the parameter by a constant does not change the signed area of a
  `2π`-periodic curve.  The one-variable integrand `t ↦ ω_ℂ (c t) (deriv c t)` of the area
  integral is `2π`-periodic — `deriv` of a periodic function is periodic, which is
  `deriv_comp_add_const` applied to the definitional identity `c (· + 2π) = c` — so its interval
  integral over one period does not depend on where the period starts
  (`Function.Periodic.intervalIntegral_add_eq`), and `∫₀^{2π} f (t + ψ) = ∫_ψ^{ψ+2π} f = ∫₀^{2π} f`
  by the substitution `intervalIntegral.integral_comp_add_right`.

Finally `signedArea (CI.c τ) = π` is the `area` field of the `CurveIsotopy`.  Note that no
smoothness of `CI.c τ` is used: the shift-invariance of the area integral is a formal consequence
of `2π`-periodicity alone.
-/

namespace Work.RPB.B5

open Work.RPV

/-- **Translating the parameter preserves the integral over a period.**
For a `2π`-periodic `f : ℝ → ℝ` and any `ψ`,
`∫₀^{2π} f (t + ψ) dt = ∫₀^{2π} f t dt`. -/
private lemma integral_shift_periodic (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    (ψ : ℝ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), f (x + ψ) = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  have h1 : ∫ x in (0 : ℝ)..(2 * Real.pi), f (x + ψ) = ∫ x in ψ..ψ + 2 * Real.pi, f x := by
    rw [intervalIntegral.integral_comp_add_right]
    simp only [zero_add, add_comm (2 * Real.pi) ψ]
  rw [h1, hf.intervalIntegral_add_eq ψ 0, zero_add]

/-- **`deriv` of a `2π`-periodic function is `2π`-periodic.**  The identity
`c (· + 2π) = c` between functions, differentiated at `t`, reads (by `deriv_comp_add_const`)
`deriv c (t + 2π) = deriv c t`. -/
private lemma deriv_periodic (c : ℝ → ℂ) (hc : ∀ t, c (t + 2 * Real.pi) = c t) (t : ℝ) :
    deriv c (t + 2 * Real.pi) = deriv c t := by
  have hfun : (fun x : ℝ => c (x + 2 * Real.pi)) = c := by
    funext x; exact hc x
  have h := congrArg (fun g : ℝ → ℂ => deriv g t) hfun
  rw [deriv_comp_add_const] at h
  simpa using h

/-- **Translating the parameter preserves the signed area of a `2π`-periodic curve.** -/
private lemma signedArea_shift (c : ℝ → ℂ) (hc : ∀ t, c (t + 2 * Real.pi) = c t) (ψ : ℝ) :
    Work.RPB.signedArea (fun t => c (t + ψ)) = Work.RPB.signedArea c := by
  -- the area integrand of `c` is `2π`-periodic
  have hgper : Function.Periodic (fun t => Work.RPV.ωC (c t) (deriv c t)) (2 * Real.pi) := by
    intro t
    simp only []
    rw [hc t, deriv_periodic c hc t]
  -- the derivative of the translate is the translate of the derivative
  have hcongr : ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (c (t + ψ)) (deriv (fun u => c (u + ψ)) t)
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
          Work.RPV.ωC (c (t + ψ)) (deriv c (t + ψ)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [deriv_comp_add_const]
  have hshift : ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (c (t + ψ)) (deriv c (t + ψ))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (c t) (deriv c t) :=
    integral_shift_periodic (fun s => Work.RPV.ωC (c s) (deriv c s)) hgper ψ
  rw [Work.RPB.signedArea, Work.RPB.signedArea, hcongr, hshift]

theorem signedArea_scale_shift (CI : Work.RPV.CurveIsotopy) (τ R ψ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Work.RPB.signedArea (fun t => (R : ℂ) * CI.c τ (t + ψ)) = R ^ 2 * Real.pi := by
  rw [signedArea_const_mul (fun t => CI.c τ (t + ψ)) R,
    signedArea_shift (CI.c τ) (CI.per τ) ψ]
  have hpi : Work.RPB.signedArea (CI.c τ) = Real.pi := CI.area τ hτ
  rw [hpi]

end Work.RPB.B5
