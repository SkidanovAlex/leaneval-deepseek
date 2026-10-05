import Mathlib
import Submission.Work.RPB.Defs

/-!
# `signedArea_comp_reparam`: the signed area is invariant under a periodic reparametrisation

The signed area `(1/2) ∮ ω_ℂ(c, c')` of a `2π`-periodic closed curve is unchanged by a `C¹`
reparametrisation `u` with `u (t + 2π) = u t + 2π` (a "degree one" reparametrisation of the
circle, though no monotonicity is needed to state it).

Write `g s = ω_ℂ (c s) (deriv c s)` for the real-valued area integrand of `c`.  Two ingredients
produce the identity.

* **Chain rule and bilinearity.**  `deriv (c ∘ u) t = deriv c (u t) * deriv u t`
  (`HasDerivAt.scomp`), and `ω_ℂ` is real-bilinear, `ω_ℂ a (b * r) = ω_ℂ a b * r` for real `r`.
  Hence the integrand of `c ∘ u` is `(g ∘ u) t * deriv u t`.

* **Signed change of variables.**  `intervalIntegral.integral_comp_mul_deriv` gives
  `∫ x in a..b, (g ∘ u) x * deriv u x = ∫ x in u a..u b, g x`; no monotonicity of `u` is
  required.  The integral of `g` over a period does not depend on the starting point
  (`Function.Periodic.intervalIntegral_add_eq`), because `g` is `2π`-periodic: `c` is, and the
  derivative of a periodic function is periodic.

Note that `ContDiff ℝ 1 c` is only used through differentiability of `c` and continuity of
`deriv c`, and `ContDiff ℝ 1 u` through differentiability of `u` and continuity of `deriv u`.
-/

namespace Work.RPB.B5

/-- `ω_ℂ` is real-linear in its second variable: multiplying the second variable by a real scalar
multiplies the value by that scalar. -/
private lemma omegaC_mul_ofReal (a b : ℂ) (r : ℝ) :
    Work.RPV.ωC a (b * (r : ℂ)) = Work.RPV.ωC a b * r := by
  rw [Work.RPV.ωC, Work.RPV.ωC, ← mul_assoc, Complex.mul_im]
  simp

/-- The derivative of a `2π`-periodic function is `2π`-periodic. -/
private lemma deriv_add_two_pi (c : ℝ → ℂ) (hper : ∀ t, c (t + 2 * Real.pi) = c t) (t : ℝ) :
    deriv c (t + 2 * Real.pi) = deriv c t := by
  have hfun : (fun x : ℝ => c (x + 2 * Real.pi)) = c := by funext x; exact hper x
  have h := congrArg (fun g : ℝ → ℂ => deriv g t) hfun
  rwa [deriv_comp_add_const] at h

theorem signedArea_comp_reparam (c : ℝ → ℂ) (u : ℝ → ℝ) (hc : ContDiff ℝ 1 c)
    (hper : ∀ t, c (t + 2 * Real.pi) = c t) (hu : ContDiff ℝ 1 u)
    (huper : ∀ t, u (t + 2 * Real.pi) = u t + 2 * Real.pi) :
    Work.RPB.signedArea (fun t => c (u t)) = Work.RPB.signedArea c := by
  have hcd : Differentiable ℝ c := hc.differentiable (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdu : Continuous (deriv u) := hu.continuous_deriv_one
  -- The area integrand `g s = ω_ℂ (c s) (deriv c s)` of `c` is continuous and `2π`-periodic.
  have hgcont : Continuous (fun s : ℝ => Work.RPV.ωC (c s) (deriv c s)) := by
    simp only [Work.RPV.ωC]
    fun_prop
  have hgper : Function.Periodic (fun s : ℝ => Work.RPV.ωC (c s) (deriv c s)) (2 * Real.pi) := by
    intro t
    simp only []
    rw [hper t, deriv_add_two_pi c hper t]
  -- The chain rule for `c ∘ u`.
  have hchain : ∀ t, deriv (fun s => c (u s)) t = deriv c (u t) * ((deriv u t : ℝ) : ℂ) := by
    intro t
    have h1 : HasDerivAt (fun s => c (u s)) (deriv u t • deriv c (u t)) t :=
      HasDerivAt.scomp t (hcd.differentiableAt.hasDerivAt) (hud.differentiableAt.hasDerivAt)
    rw [h1.deriv, Complex.real_smul, mul_comm]
  -- The integrand of `c ∘ u` is `(g ∘ u) * deriv u`.
  have hcongr : (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (c (u t)) (deriv (fun s => c (u s)) t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
          (Work.RPV.ωC (c (u t)) (deriv c (u t))) * deriv u t := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [hchain t, omegaC_mul_ofReal]
  -- Signed change of variables.
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := u) (f' := deriv u) (g := fun s : ℝ => Work.RPV.ωC (c s) (deriv c s))
      (fun x _ => hud.differentiableAt.hasDerivAt) hdu.continuousOn hgcont
  -- The integral of `g` over one period does not depend on where the period starts.
  have hperiod : (∫ x in u 0..u (2 * Real.pi), Work.RPV.ωC (c x) (deriv c x))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (c x) (deriv c x) := by
    have h1 : u (2 * Real.pi) = u 0 + 2 * Real.pi := by simpa using huper 0
    rw [h1, hgper.intervalIntegral_add_eq (u 0) 0]
    simp
  rw [Work.RPB.signedArea, Work.RPB.signedArea, hcongr]
  have hsub' : (∫ t in (0 : ℝ)..(2 * Real.pi),
        (fun s : ℝ => Work.RPV.ωC (c s) (deriv c s)) (u t) * deriv u t)
      = ∫ x in u 0..u (2 * Real.pi), Work.RPV.ωC (c x) (deriv c x) := by
    simpa only [Function.comp_apply] using hsub
  rw [hsub', hperiod]

end Work.RPB.B5
