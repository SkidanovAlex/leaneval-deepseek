/-
Work module for the Elgindi finite-time singularity project.

# Smoothness of the singular solution `LzeroSing` on the open angular interval

`LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)` (`Work.FTS.EllipticEst.LzeroSingDefs`)
has a genuine pole at the singular angular endpoint `θ = π/2` (it behaves like `-1/(4t)`,
`t = π/2 - θ`), but it is `C^∞` — hence `C^n` for every `n` — on the *open* interval
`(0, π/2)`; this is what the pole-coefficient calculus of the elliptic estimates needs.

The proof is a two-line argument once the two ingredients are in place:

* the integrand `s ↦ 1/(sin s · sin(2s)²)` is `C^∞` on `(0, π/2)` (both `sin s` and `sin 2s`
  are non-zero there, so the reciprocal is smooth);
* the primitive `u ↦ ∫_{π/4}^u g` of a `C^∞` function `g` on an *open ordered* set is again
  `C^∞` there (`contDiffOn_infty_integral_of_ordConnected`, the higher-order fundamental
  theorem of calculus, obtained from the one-dimensional recursion
  `contDiffOn_infty_iff_deriv_of_isOpen` together with `integral_hasDerivAt_right`).

Then `θ ↦ ∫_{π/4}^{π/2-θ} g` is the composition of that primitive with the affine map
`θ ↦ π/2 - θ`, and multiplying by the smooth `sin(2θ)` produces `LzeroSing`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.LzeroSingDefs
import Submission.Work.FTS.EllipticEst.LzeroSingODE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **Higher-order fundamental theorem of calculus.**  If `f` is `C^∞` on an open ordered set
`s` and `a ∈ s`, then the primitive `u ↦ ∫_a^u f` is `C^∞` on `s`.

The recursion `ContDiffOn 𝕜 ∞ F s ↔ DifferentiableOn 𝕜 F s ∧ ContDiffOn 𝕜 ∞ (deriv F) s`
(`contDiffOn_infty_iff_deriv_of_isOpen`) reduces this to `deriv (∫_a^· f) = f` on `s`, which is
`intervalIntegral.deriv_integral_right` (the integrand is continuous on `s`, and `s` being
ordered and containing `a` puts every interval `[a, x]`, `x ∈ s`, inside `s`). -/
theorem contDiffOn_infty_integral_of_ordConnected {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ}
    (hs : IsOpen s) (hsc : s.OrdConnected) (ha : a ∈ s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun u => ∫ t in a..u, f t) s := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen hs]
  have hcont : ContinuousOn f s := hf.continuousOn
  have hint : ∀ x ∈ s, IntervalIntegrable f volume a x := fun x hx =>
    (hcont.mono (hsc.uIcc_subset ha hx)).intervalIntegrable
  have hsm : ∀ x ∈ s, StronglyMeasurableAtFilter f (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter hs (fun y hy => hcont.continuousAt (hs.mem_nhds hy))
  constructor
  · intro x hx
    exact ((intervalIntegral.integral_hasDerivAt_right (hint x hx) (hsm x hx)
      (hcont.continuousAt (hs.mem_nhds hx))).differentiableAt).differentiableWithinAt
  · exact hf.congr (fun x hx =>
      intervalIntegral.deriv_integral_right (hint x hx) (hsm x hx)
        (hcont.continuousAt (hs.mem_nhds hx)))

/-- The reduction-of-order weight `s ↦ 1/(sin s · sin(2s)²)` of `LzeroSing` is `C^∞` on the
open interval `(0, π/2)` (`sin s > 0` and `sin(2s) > 0` there). -/
theorem contDiffOn_infty_LzeroSingIntegrand :
    ContDiffOn ℝ ∞ LzeroSingIntegrand (Set.Ioo 0 (Real.pi / 2)) := by
  have h : ContDiffOn ℝ ∞ (fun t : ℝ => 1 / (Real.sin t * (Real.sin (2 * t)) ^ 2))
      (Set.Ioo 0 (Real.pi / 2)) := by
    set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
    have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => (Real.sin (2 * t)) ^ 2) s :=
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).pow 2).contDiffOn
    have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => Real.sin t) s := Real.contDiff_sin.contDiffOn
    have hprod : ContDiffOn ℝ ∞ (fun t : ℝ => Real.sin t * (Real.sin (2 * t)) ^ 2) s :=
      h1.mul h2
    have hne : ∀ t ∈ s, Real.sin t * (Real.sin (2 * t)) ^ 2 ≠ 0 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htp : t < Real.pi / 2 := ht.2
      have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
      have hsin2 : 0 < Real.sin (2 * t) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      exact mul_ne_zero (ne_of_gt hsin) (ne_of_gt (pow_pos hsin2 2))
    exact (contDiffOn_const (c := (1 : ℝ)) (s := s)).div hprod hne
  exact h.congr (fun x _ => by simp [Work.FTS.EllipticEst.LzeroSingIntegrand])

/-- **`LzeroSing` is `C^∞` on `(0, π/2)`** (the pole sits at the endpoint `π/2`, which is not
part of the set).  Route: `SingInt θ = ∫_{π/4}^{π/2-θ} g` is the composition of the `C^∞`
primitive `u ↦ ∫_{π/4}^u g` with the affine map `θ ↦ π/2 - θ`, and `LzeroSing = sin(2·)·SingInt`. -/
theorem contDiffOn_infty_LzeroSing :
    ContDiffOn ℝ ∞ LzeroSing (Set.Ioo 0 (Real.pi / 2)) := by
  have main : ContDiffOn ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ) *
      (∫ t in (Real.pi / 4)..(Real.pi / 2 - θ), LzeroSingIntegrand t))
      (Set.Ioo 0 (Real.pi / 2)) := by
    set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
    have h24 : (Real.pi / 4 : ℝ) ∈ s :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hG : ContDiffOn ℝ ∞ (fun u : ℝ => ∫ t in (Real.pi / 4)..u, LzeroSingIntegrand t) s :=
      contDiffOn_infty_integral_of_ordConnected isOpen_Ioo Set.ordConnected_Ioo h24
        contDiffOn_infty_LzeroSingIntegrand
    have hcomp : ContDiffOn ℝ ∞
        ((fun u : ℝ => ∫ t in (Real.pi / 4)..u, LzeroSingIntegrand t) ∘
          (fun θ : ℝ => Real.pi / 2 - θ)) s := by
      refine hG.comp ?_ ?_
      · exact (contDiffOn_const.sub contDiff_id.contDiffOn)
      · intro θ hθ
        have h1 : 0 < θ := hθ.1
        have h2 : θ < Real.pi / 2 := hθ.2
        exact ⟨by linarith, by linarith⟩
    have hSingInt : ContDiffOn ℝ ∞ SingInt s := hcomp
    have hsin : ContDiffOn ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ)) s :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
    exact hsin.mul hSingInt
  exact main.congr (fun θ _ => by simp [Work.FTS.EllipticEst.LzeroSing])

theorem LzeroSingContDiffOn (n : ℕ) :
    ContDiffOn ℝ n Work.FTS.EllipticEst.LzeroSing (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_infty_LzeroSing.of_le (by simp)

end Work.FTS.EllipticEst
