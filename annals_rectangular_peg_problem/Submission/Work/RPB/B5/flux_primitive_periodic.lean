import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B4.periodic_deriv
import Submission.Work.RPB.B5.contDiff_omegaC_fderiv_snd
import Submission.Work.RPB.B5.deriv_signedArea_general
import Submission.Work.RPA3.deriv_deriv_swap

/-!
# `flux_primitive_periodic`

For a `C²` family `V : ℝ → ℝ → ℂ` of `2π`-periodic closed plane curves, whose signed area has
`σ`-derivative exactly `2π` (`hderiv`), the flux integrand

`q(t) = ω_ℂ(∂_σ V(σ,t), ∂_t V(σ,t))`

satisfies the three assertions of `flux_primitive_periodic`:

1. `∫_0^{2π} q = 2π` — this is `deriv_signedArea_general` (`d/ds signedArea = ∫ ω_ℂ(∂_s V, ∂_t V)`)
   combined with the hypothesis `hderiv = HasDerivAt (signedArea ∘ V) (2π) σ`;
2. the primitive `G(u) = ∫_0^u q` has `G' = q` (fundamental theorem of calculus, `q` continuous);
3. `G` is "periodic up to `2π`": `G(t + 2π) = G(t) + 2π`, because `q` is `2π`-periodic and the
   integral of `q` over one period is `2π` (assertion 1).

Nothing here depends on the geometric content of `ω_ℂ`: the argument is the classical
`d(area)/dσ = ∮ ω_ℂ(∂_σ, ∂_t)` together with the elementary theory of interval integrals.
-/

open MeasureTheory intervalIntegral
open scoped Interval ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The flux integrand `ω_ℂ(∂_σ Φ, ∂_t Φ)` of an (uncurried) family `Φ : ℝ × ℝ → ℂ`. -/
private def Q (Φ : ℝ × ℝ → ℂ) (σ t : ℝ) : ℝ :=
  Work.RPV.ωC (deriv (fun w => Φ (w, t)) σ) (deriv (fun y => Φ (σ, y)) t)

/-- `Q Φ σ` is continuous when `Φ` is `C²`: both partial derivatives are `fderiv`-evaluations of
the `C¹` map `fderiv Φ`, and `ω_ℂ` is a smooth bilinear form. -/
private lemma Q_continuous (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ 2 Φ) (σ : ℝ) :
    Continuous (fun t : ℝ => Q Φ σ t) := by
  have hΦd : ∀ p : ℝ × ℝ, HasFDerivAt Φ (fderiv ℝ Φ p) p :=
    fun p => ((hΦ.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hf1 : ContDiff ℝ 1 (fun t : ℝ => fderiv ℝ Φ (σ, t) (1, 0)) := by fun_prop
  have hf2 : ContDiff ℝ 1 (fun t : ℝ => fderiv ℝ Φ (σ, t) (0, 1)) := by fun_prop
  have hmain : ContDiff ℝ 1 (fun t : ℝ =>
      Work.RPV.ωC (fderiv ℝ Φ (σ, t) (1, 0)) (fderiv ℝ Φ (σ, t) (0, 1))) :=
    contDiff_omegaC_comp hf1 hf2
  have heq : (fun t : ℝ => Q Φ σ t) = fun t : ℝ =>
      Work.RPV.ωC (fderiv ℝ Φ (σ, t) (1, 0)) (fderiv ℝ Φ (σ, t) (0, 1)) := by
    funext t
    simp only [Q]
    rw [Work.RPA3.deriv_prodMk_left (hΦd (σ, t)),
      Work.RPA3.deriv_prodMk_right (hΦd (σ, t))]
  rw [heq]
  exact hmain.continuous

/-- The main analytic content: assertions (1), (2), (3) of `flux_primitive_periodic` for an
uncurried family `Φ`. -/
private lemma flux_aux (Φ : ℝ × ℝ → ℂ) (σ : ℝ)
    (hper : ∀ s t, Φ (s, t + 2 * Real.pi) = Φ (s, t))
    (hΦ : ContDiff ℝ 2 Φ)
    (hderiv : HasDerivAt (fun s => Work.RPB.signedArea (fun t => Φ (s, t))) (2 * Real.pi) σ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), Q Φ σ t) = 2 * Real.pi ∧
    (∀ t, deriv (fun u => ∫ s in (0 : ℝ)..u, Q Φ σ s) t = Q Φ σ t) ∧
    (∀ t, (fun u => ∫ s in (0 : ℝ)..u, Q Φ σ s) (t + 2 * Real.pi)
        = (fun u => ∫ s in (0 : ℝ)..u, Q Φ σ s) t + 2 * Real.pi) := by
  have hcont : Continuous (fun t : ℝ => Q Φ σ t) := Q_continuous Φ hΦ σ
  -- `q` is `2π`-periodic: `Φ` is, hence so are `∂_σ Φ` and `∂_t Φ`.
  have hper_Q : ∀ t : ℝ, Q Φ σ (t + 2 * Real.pi) = Q Φ σ t := by
    intro t
    have h1 : deriv (fun w => Φ (w, t + 2 * Real.pi)) σ = deriv (fun w => Φ (w, t)) σ := by
      rw [show (fun w => Φ (w, t + 2 * Real.pi)) = (fun w => Φ (w, t)) from
        funext (fun w => hper w t)]
    have h2 : deriv (fun y => Φ (σ, y)) (t + 2 * Real.pi) = deriv (fun y => Φ (σ, y)) t :=
      Work.RPB.B4.periodic_deriv (fun y => Φ (σ, y)) (2 * Real.pi) (fun y => hper σ y) t
    simp only [Q, h1, h2]
  -- Assertion (1): the derivative of the signed area is the flux.
  have h1 : (∫ t in (0 : ℝ)..(2 * Real.pi), Q Φ σ t) = 2 * Real.pi := by
    have hL := deriv_signedArea_general (fun a b => Φ (a, b)) σ (fun s t => hper s t) hΦ
    have h2 : deriv (fun s => Work.RPB.signedArea (fun t => Φ (s, t))) σ = 2 * Real.pi :=
      hderiv.deriv
    rw [h2] at hL
    exact hL.symm
  refine ⟨h1, ?_, ?_⟩
  -- Assertion (2): fundamental theorem of calculus.
  · intro t
    have hint : IntervalIntegrable (fun s : ℝ => Q Φ σ s) volume (0 : ℝ) t :=
      hcont.intervalIntegrable 0 t
    exact (intervalIntegral.integral_hasDerivAt_right hint
      (hcont.stronglyMeasurableAtFilter volume (nhds t)) hcont.continuousAt).deriv
  -- Assertion (3): `G(t + 2π) = G t + 2π`, by splitting the integral and substituting.
  · intro t
    show (∫ s in (0 : ℝ)..(t + 2 * Real.pi), Q Φ σ s)
        = (∫ s in (0 : ℝ)..t, Q Φ σ s) + 2 * Real.pi
    have hint0 : IntervalIntegrable (fun s : ℝ => Q Φ σ s) volume (0 : ℝ) (2 * Real.pi) :=
      hcont.intervalIntegrable _ _
    have hint1 : IntervalIntegrable (fun s : ℝ => Q Φ σ s) volume (2 * Real.pi)
        (t + 2 * Real.pi) := hcont.intervalIntegrable _ _
    have hsub : (∫ s in (2 * Real.pi)..(t + 2 * Real.pi), Q Φ σ s)
        = ∫ s in (0 : ℝ)..t, Q Φ σ s := by
      have hcomp := intervalIntegral.integral_comp_add_right (fun s : ℝ => Q Φ σ s)
        (2 * Real.pi) (a := (0 : ℝ)) (b := t)
      rw [zero_add] at hcomp
      rw [← hcomp]
      exact intervalIntegral.integral_congr (fun x _ => hper_Q x)
    rw [← intervalIntegral.integral_add_adjacent_intervals hint0 hint1, h1, hsub]
    ring

theorem flux_primitive_periodic (V : ℝ → ℝ → ℂ) (σ : ℝ) (hper : ∀ σ t, V σ (t + 2 * Real.pi) = V σ t) (hV : ContDiff ℝ 2 (fun z : ℝ × ℝ => V z.1 z.2)) (hderiv : HasDerivAt (fun σ => Work.RPB.signedArea (V σ)) (2 * Real.pi) σ) : (∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (deriv (fun s => V s t) σ) (deriv (V σ) t)) = 2 * Real.pi ∧ (∀ t, deriv (fun u => ∫ s in (0 : ℝ)..u, Work.RPV.ωC (deriv (fun w => V w s) σ) (deriv (V σ) s)) t = Work.RPV.ωC (deriv (fun s => V s t) σ) (deriv (V σ) t)) ∧ (∀ t, (fun u => ∫ s in (0 : ℝ)..u, Work.RPV.ωC (deriv (fun w => V w s) σ) (deriv (V σ) s)) (t + 2 * Real.pi) = (fun u => ∫ s in (0 : ℝ)..u, Work.RPV.ωC (deriv (fun w => V w s) σ) (deriv (V σ) s)) t + 2 * Real.pi) := by
  have haux := flux_aux (fun z : ℝ × ℝ => V z.1 z.2) σ (fun s t => hper s t) hV hderiv
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Q] using haux.1
  · intro t
    simpa only [Q] using haux.2.1 t
  · intro t
    simpa only [Q] using haux.2.2 t

end Work.RPB.B5
