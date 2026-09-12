import Mathlib.Analysis.InnerProductSpace.ExteriorPower

namespace Commons.Analysis.InnerProductSpace

lemma norm_iMulti_comp_perm {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (σ : Equiv.Perm (Fin k)) (v : Fin k → E) :
    ‖exteriorPower.ιMulti ℝ k (v ∘ σ)‖ = ‖exteriorPower.ιMulti ℝ k v‖ := by
  classical
  let x : ⋀[ℝ]^k E := exteriorPower.ιMulti ℝ k v
  have hx : exteriorPower.ιMulti ℝ k (v ∘ σ) = Equiv.Perm.sign σ • x := by
    dsimp [x]
    exact (exteriorPower.ιMulti ℝ k (M := E)).map_perm v σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [hx, hσ]
    simp [x]
  · rw [hx, hσ]
    simp [x, Units.smul_def]

end Commons.Analysis.InnerProductSpace
