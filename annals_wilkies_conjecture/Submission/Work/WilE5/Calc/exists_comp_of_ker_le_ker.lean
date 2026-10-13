import Mathlib

namespace Work.WilE5.Calc

/-- If a linear functional `ℓ` vanishes on the kernel of a surjective linear map `D`, then
`ℓ` factors as `φ ∘ D` for some linear functional `φ`: pick a right inverse `g` of `D` and
set `φ = ℓ ∘ g`; the defect `g (D x) - x` always lies in `ker D ≤ ker ℓ`. -/
theorem exists_comp_of_ker_le_ker {q k : ℕ} (D : (Fin q → ℝ) →L[ℝ] (Fin k → ℝ)) (ℓ : (Fin q → ℝ) →L[ℝ] ℝ)
    (hsurj : D.range = ⊤) (h : D.ker ≤ ℓ.ker) : ∃ φ : (Fin k → ℝ) →L[ℝ] ℝ, ℓ = φ.comp D := by
  obtain ⟨g, hg⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective D hsurj
  refine ⟨ℓ.comp g, ?_⟩
  ext x
  have h1 : (D : (Fin q → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (g (D x)) = (D : (Fin q → ℝ) →ₗ[ℝ] (Fin k → ℝ)) x := by
    have hh := congrArg (fun (f : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) => f (D x)) hg
    simpa using hh
  have hmem : g (D x) - x ∈ D.ker := by
    rw [LinearMap.mem_ker, map_sub, h1, sub_self]
  have h2 : ℓ (g (D x)) = ℓ x := by
    have hker : g (D x) - x ∈ ℓ.ker := h hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hker
    exact hker
  simp only [ContinuousLinearMap.comp_apply]
  exact h2.symm

end Work.WilE5.Calc
