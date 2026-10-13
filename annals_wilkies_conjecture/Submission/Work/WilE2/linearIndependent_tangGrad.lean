import Mathlib

namespace Work.WilE2

open LinearMap

/-- If the functionals `∂_a V(z) : (Fin (m+1) → ℝ) →L[ℝ] ℝ` (`a : Fin m`) are linearly
independent, then so are the corresponding gradient vectors
`i ↦ ∂_a V(z) (Pi.single i 1)` in `Fin (m+1) → ℝ`.

Indeed the map sending a functional to its values on the standard basis
`Pi.single i 1` is a linear injection (it has trivial kernel). -/
theorem linearIndependent_tangGrad {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (z : Fin (m + 1) → ℝ)
    (h : LinearIndependent ℝ (fun a => fderiv ℝ (fun w => V w a) z)) :
    LinearIndependent ℝ (fun a : Fin m => (fun i : Fin (m + 1) =>
      fderiv ℝ (fun w => V w a) z (Pi.single i (1 : ℝ)))) := by
  -- The linear map sending a functional to its values on the standard basis.
  let T : ((Fin (m + 1) → ℝ) →L[ℝ] ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    { toFun := fun L i => L (Pi.single i (1 : ℝ))
      map_add' := by intro L1 L2; ext i; simp
      map_smul' := by intro c L; ext i; simp }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro L1 L2 h12
    have hL : ∀ i, (L1 : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) (Pi.single i (1 : ℝ))
        = (L2 : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) (Pi.single i (1 : ℝ)) :=
      fun i => congrFun h12 i
    have hLM : (L1 : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) = (L2 : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) := by
      apply LinearMap.pi_ext
      intro i x
      have hx : (Pi.single i x : Fin (m + 1) → ℝ) = x • Pi.single i (1 : ℝ) := by
        ext j
        by_cases hj : j = i <;> simp [hj]
      rw [hx, map_smul, map_smul, hL i]
    ext v
    exact congrArg (fun f => f v) hLM
  have hmap := h.map' T hker
  simpa [T, Function.comp_def] using hmap

end Work.WilE2
