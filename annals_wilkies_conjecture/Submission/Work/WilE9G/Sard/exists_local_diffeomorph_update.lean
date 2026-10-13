import Mathlib
import Submission.Work.WilE9G.Sard.smulRight_continuousLinearEquiv
import Submission.Work.WilE9G.Sard.hasFDerivAt_update
import Submission.Work.WilE9G.Sard.analyticAt_update

namespace Work.WilE9G.Sard

/-- **Replacing one coordinate by an analytic function is locally a diffeomorphism.**  If `h` is
analytic at `x₀` and `∂ᵢ h (x₀) ≠ 0`, then `Φ z = Function.update z i (h z)` is a local analytic
diffeomorphism at `x₀`; the statement also produces the analytic inverse `Ψ` on a neighbourhood of
`Φ x₀`. -/
theorem exists_local_diffeomorph_update {n : ℕ} {h : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (i : Fin n) (hh : AnalyticAt ℝ h x₀) (hi : (fderiv ℝ h x₀) (Pi.single i 1) ≠ 0) :
    ∃ (Φ Ψ : (Fin n → ℝ) → (Fin n → ℝ)),
      AnalyticAt ℝ Φ x₀ ∧ AnalyticAt ℝ Ψ (Φ x₀) ∧
      (∀ᶠ z in nhds x₀, Φ z = Function.update z i (h z)) ∧
      (∀ᶠ z in nhds x₀, Ψ (Φ z) = z) ∧
      (∀ᶠ y in nhds (Φ x₀), Φ (Ψ y) = y) := by
  -- the derivative `a` of `h` at `x₀`, named so that expressions such as `a - proj i` elaborate
  obtain ⟨a, ha⟩ : ∃ a : (Fin n → ℝ) →L[ℝ] ℝ, a = fderiv ℝ h x₀ := ⟨_, rfl⟩
  rw [← ha] at hi
  -- the map `Φ` replacing coordinate `i` by `h`
  let Φ : (Fin n → ℝ) → (Fin n → ℝ) := fun z => Function.update z i (h z)
  have hΦa : AnalyticAt ℝ Φ x₀ := analyticAt_update i hh
  have hf' : HasFDerivAt h a x₀ := by
    rw [ha]; exact hh.hasStrictFDerivAt.hasFDerivAt
  -- the linear part of `Φ` is invertible: its determinant is `a (Pi.single i 1) = ∂ᵢ h (x₀) ≠ 0`
  have hc : 1 + ((a - ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single i 1) ≠ 0 := by
    have h1 : ((a - ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single i 1)
        = a (Pi.single i 1) - 1 := by
      simp
    rw [h1]
    intro hz
    exact hi (by linarith)
  obtain ⟨e, he⟩ := smulRight_continuousLinearEquiv (a - ContinuousLinearMap.proj i)
    (Pi.single i 1) hc
  have hF : HasFDerivAt Φ
      (1 + (a - ContinuousLinearMap.proj i).smulRight (Pi.single i 1)) x₀ :=
    hasFDerivAt_update i hf'
  have hΦd : fderiv ℝ Φ x₀ = (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    rw [hF.fderiv, he]
  have hstrict : HasStrictFDerivAt Φ (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x₀ := by
    simpa [hΦd] using hΦa.hasStrictFDerivAt
  -- the local inverse supplied by the inverse function theorem
  let R : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) := hstrict.toOpenPartialHomeomorph Φ
  have hR0 : x₀ ∈ R.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- ... is analytic at `Φ x₀`, because `Φ` is analytic with invertible derivative
  have hΨa : AnalyticAt ℝ (R.symm) (Φ x₀) := by
    have hA : AnalyticAt ℝ (R : (Fin n → ℝ) → (Fin n → ℝ)) x₀ := hΦa
    have hD : fderiv ℝ (R : (Fin n → ℝ) → (Fin n → ℝ)) x₀
        = (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := hΦd
    have := R.analyticAt_symm' hR0 hA hD
    simpa [R] using this
  refine ⟨Φ, R.symm, hΦa, hΨa, ?_, ?_, ?_⟩
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [hstrict.eventually_left_inverse] with z hz
    simpa [R, HasStrictFDerivAt.localInverse_def] using hz
  · filter_upwards [hstrict.eventually_right_inverse] with y hy
    simpa [R, HasStrictFDerivAt.localInverse_def] using hy

end Work.WilE9G.Sard
