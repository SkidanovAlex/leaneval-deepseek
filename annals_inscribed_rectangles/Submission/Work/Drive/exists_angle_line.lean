import Mathlib
import Submission.Work.Drive.UmlaufSetup

namespace Work.Drive

open scoped Manifold ContDiff

/-- `dirOf` is continuous along any continuous path that avoids `0`: on the complement of `0`
it agrees with `z ↦ z / ‖z‖`, which is continuous there. -/
lemma continuous_dirOf_comp {g : ℝ → ℂ} (hg : Continuous g) (hne : ∀ t, g t ≠ 0) :
    Continuous fun t => dirOf (g t) := by
  have hdiv : Continuous fun t => g t / ((‖g t‖ : ℝ) : ℂ) := by
    apply Continuous.div hg
    · exact Complex.continuous_ofReal.comp (continuous_norm.comp hg)
    · intro t
      simp [Complex.ofReal_eq_zero, norm_ne_zero_iff.mpr (hne t)]
  have hsub : Continuous fun t => dirOfNonzero (g t) (hne t) := by
    apply Continuous.subtype_mk
    simpa only [dirOfNonzero] using hdiv
  refine hsub.congr (fun t => ?_)
  rw [dirOf, dif_neg (hne t)]

/-- The tangent direction of a regular curve is continuous. -/
lemma continuous_tangDir (c : ℝ → ℝ × ℝ) (hc : RegCurve c) : Continuous (tangDir c) := by
  have hdc : Continuous (deriv c) := hc.contDiff.continuous_deriv_one
  have hg : Continuous fun t => toC (deriv c t) := continuous_toC.comp hdc
  have hne : ∀ t, toC (deriv c t) ≠ 0 := fun t => toC_ne_zero_iff.mpr (hc.deriv_ne_zero t)
  exact continuous_dirOf_comp hg hne

/-- A regular closed plane curve has a continuous angle function for its tangent direction.

`t ↦ Work.Drive.tangDir c t` is a continuous map `ℝ → Circle`: `deriv c` is continuous
(`hc.contDiff`, `ContDiff.continuous_deriv_one`), `Work.Drive.dirOf` is continuous off `0`, and
`deriv c t ≠ 0` (`hc.deriv_ne_zero`). Since `ℝ` is simply connected and locally path connected
and `Circle.exp : ℝ → Circle` is a covering map (`Circle.isCoveringMap_exp`), the lifting theorem
`IsCoveringMap.existsUnique_continuousMap_lifts` produces `θ : ℝ → ℝ` with
`Circle.exp ∘ θ = tangDir c`. -/
theorem exists_angle_line (c : ℝ → ℝ × ℝ) (hc : Work.Drive.RegCurve c) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ ∀ t, Circle.exp (θ t) = Work.Drive.tangDir c t := by
  have hcont : Continuous (tangDir c) := continuous_tangDir c hc
  let f : C(ℝ, Circle) := ⟨tangDir c, hcont⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (f 0)
  obtain ⟨F, hF⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 e₀ he₀
  refine ⟨F, F.continuous, fun t => ?_⟩
  have h2 : ⇑Circle.exp ∘ ⇑F = ⇑f := hF.1.2
  have := congrFun h2 t
  simpa [f] using this

end Work.Drive
