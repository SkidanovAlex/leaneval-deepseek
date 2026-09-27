import Mathlib
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.mfderiv_injective_of_immersionAt

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

/-- The tangent map of `Circle.exp : ℝ → Circle` is nonzero at every point: its value on `1`
is (under the coercion `Circle → ℂ`) the derivative `Complex.exp (t * I) * I` of the function
`s ↦ Complex.exp (s * I)`, which never vanishes. -/
theorem circleExp_mfderiv_apply_one_ne_zero (t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (Circle.exp : ℝ → Circle) t) 1 ≠ 0 := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  -- the inclusion `Circle → ℂ`
  let f : Circle → ℂ := fun z => (z : ℂ)
  have hcoe : MDifferentiableAt (𝓡 1) (𝓘(ℝ, ℂ)) f (Circle.exp t) :=
    (contMDiff_coe_sphere (E := ℂ) (m := ω) (n := 1)).contMDiffAt.mdifferentiableAt (by decide)
  have hexp : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 1) (Circle.exp : ℝ → Circle) t :=
    (contMDiff_circleExp (m := ω)).contMDiffAt.mdifferentiableAt (by decide)
  intro h
  -- `(↑) ∘ Circle.exp` is the map `s ↦ Complex.exp (s * I)`
  have hfun : (f ∘ (Circle.exp : ℝ → Circle)) =
      (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) := by
    funext s; exact Circle.coe_exp s
  -- chain rule
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 1) (I'' := 𝓘(ℝ, ℂ)) t hcoe hexp
  have h2 : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (f ∘ (Circle.exp : ℝ → Circle)) t) 1 = 0 := by
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, h, map_zero]
  have h3 : deriv (f ∘ (Circle.exp : ℝ → Circle)) t = 0 := by
    rw [mfderiv_eq_fderiv] at h2
    exact h2
  have h4 : deriv (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) t = 0 := by
    rw [← hfun]; exact h3
  -- the explicit derivative
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    simpa using h1.mul_const Complex.I
  have hcomp2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t :=
    (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t hlin
  have hz : Complex.exp ((t : ℂ) * Complex.I) * Complex.I = 0 := by
    rw [← hcomp2.deriv]; exact h4
  exact (Complex.exp_ne_zero ((t : ℂ) * Complex.I))
    (((mul_eq_zero.mp hz).resolve_right Complex.I_ne_zero))

/-- The tangent of the plane curve `t ↦ γ (Circle.exp t)` of a smooth embedded closed plane
curve never vanishes.

This is proved by the chain rule: `mfderiv (γ ∘ Circle.exp) t` is the composite of
`mfderiv γ (Circle.exp t)` — injective, because `γ` is an immersion
(`Work.Drive.mfderiv_injective_of_immersionAt`) — with the nonvanishing
`mfderiv Circle.exp t` (`Work.Drive.circleExp_mfderiv_apply_one_ne_zero`). -/
theorem curve_deriv_ne_zero (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) (t : ℝ) :
    deriv (Work.Drive.curve γ) t ≠ 0 := by
  -- `γ` is an immersion at `Circle.exp t`, hence injective on tangent spaces
  have hinj : Function.Injective (mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) γ (Circle.exp t)) :=
    mfderiv_injective_of_immersionAt
      (hγ.isImmersion.isImmersionOfComplement_complement (Circle.exp t)) (by decide)
  -- differentiability of the two factors
  have hexp : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 1) (Circle.exp : ℝ → Circle) t :=
    (contMDiff_circleExp (m := ω)).contMDiffAt.mdifferentiableAt (by decide)
  have hγd : MDifferentiableAt (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) γ (Circle.exp t) :=
    (hγ.contMDiff (Circle.exp t)).mdifferentiableAt (by decide)
  -- chain rule
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 1) (I'' := 𝓘(ℝ, ℝ × ℝ)) t hγd hexp
  have hM : (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (Circle.exp : ℝ → Circle) t) 1 ≠ 0 :=
    circleExp_mfderiv_apply_one_ne_zero t
  have hval : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) (Work.Drive.curve γ) t) 1 ≠ 0 := by
    rw [show Work.Drive.curve γ = γ ∘ (Circle.exp : ℝ → Circle) from rfl, hchain]
    simp only [ContinuousLinearMap.comp_apply]
    intro hA
    exact hM (hinj (by simp [hA]))
  -- `deriv` is `mfderiv` applied to `1`
  have hderiv : deriv (Work.Drive.curve γ) t
      = (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) (Work.Drive.curve γ) t) 1 := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hderiv]
  exact hval

end Work.Drive
