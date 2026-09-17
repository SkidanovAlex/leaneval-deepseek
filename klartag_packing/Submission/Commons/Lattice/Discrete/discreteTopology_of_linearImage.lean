import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace Commons.Lattice.Discrete

/-- The image of a discrete submodule of a finite-dimensional real Euclidean space under an
injective real-linear map is again discrete. -/
theorem discreteTopology_of_linearImage {n : ℕ} (f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : Function.Injective f) (S : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology S] :
    DiscreteTopology (Submodule.map (f.restrictScalars ℤ) S) := by
  let E := EuclideanSpace ℝ (Fin n)
  let T : Submodule ℤ E := Submodule.map (f.restrictScalars ℤ) S
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo f hf
  change DiscreteTopology T
  -- `e` is the linear equivalence underlying the injective endomorphism `f`
  have he (x : E) : e x = f x := by
    exact congrFun (LinearEquiv.coe_ofInjectiveEndo f hf) x
  -- its inverse is continuous (finite-dimensional linear maps are continuous)
  have hcont_e : Continuous (fun x : E => e.symm x) := by
    exact (e.symm : E →ₗ[ℝ] E).continuous_of_finiteDimensional
  -- the inverse of `e` maps `T` back into `S`
  have hm : ∀ y : E, y ∈ T → e.symm y ∈ S := by
    intro y hy
    rcases hy with ⟨x, hx, hxy⟩
    have hxy' : f x = y := by
      simpa using hxy
    have hyx : e.symm y = x := by
      calc
        e.symm y = e.symm (f x) := by rw [hxy']
        _ = e.symm (e x) := by rw [he x]
        _ = x := by simp
    rwa [hyx]
  let h : T → S := fun y => ⟨e.symm (y : E), hm (y : E) y.2⟩
  have h_inj : Function.Injective h := by
    intro y₁ y₂ hyy
    apply Subtype.ext
    have hyy' : (h y₁ : E) = (h y₂ : E) := congrArg (fun z : S => (z : E)) hyy
    dsimp [h] at hyy'
    exact (e.symm).injective hyy'
  have h_cont : Continuous h := by
    dsimp [h]
    apply Continuous.codRestrict
    exact Continuous.comp hcont_e continuous_subtype_val
  -- a continuous injective map from `T` into the discrete space `S` makes `T` discrete
  exact DiscreteTopology.of_continuous_injective (α := T) (β := S) h_cont h_inj

end Commons.Lattice.Discrete