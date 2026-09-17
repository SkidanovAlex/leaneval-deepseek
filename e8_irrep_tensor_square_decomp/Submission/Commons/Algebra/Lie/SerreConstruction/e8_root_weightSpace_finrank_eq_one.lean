import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_simple_root_weightSpace_finrank_compat
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_reflect_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple

set_option linter.unusedSectionVars false

noncomputable section

namespace Commons.Algebra.Lie.SerreConstruction

open scoped BigOperators

/-- The joint weight space of the Serre-constructed `e₈` at a weight `μ : Fin 8 → ℤ`
(the eigenvalue vector of the eight commuting operators `ad (H i)`). -/
abbrev wtSpace (μ : Fin 8 → ℤ) : Submodule ℂ (LieAlgebra.e₈ ℂ) :=
  ⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
    (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
      (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (μ i : ℂ) • 1) :
      Submodule ℂ (LieAlgebra.e₈ ℂ))

/-- The simple reflection `sᵢ` acting on weights in the `ω`-basis: `(sᵢμ)ⱼ = μⱼ - μᵢ A i j`. -/
abbrev wtReflect (i : Fin 8) (μ : Fin 8 → ℤ) : Fin 8 → ℤ :=
  fun j => μ j - μ i * CartanMatrix.E₈ i j

/-- The dimension of the weight space is invariant under a list of simple reflections. -/
theorem finrank_wtSpace_foldl (L : List (Fin 8)) (μ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(wtSpace (L.foldl (fun v i => wtReflect i v) μ))
      = Module.finrank ℂ ↥(wtSpace μ) := by
  induction L generalizing μ with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons]
    rw [ih (wtReflect i μ), e8_weightSpace_reflect_finrank i μ]

theorem e8_root_weightSpace_finrank_eq_one (μ : Fin 8 → ℤ) (hμ : μ ≠ 0)
    (h : (∑ i, ∑ j, (μ i : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (μ j : ℚ))
      = 2) :
    Module.finrank ℂ ↥(⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (μ i : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ))) = 1 := by
  obtain ⟨L, k, hL⟩ := Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple μ h
  show Module.finrank ℂ ↥(wtSpace μ) = 1
  have h1 : Module.finrank ℂ ↥(wtSpace μ)
      = Module.finrank ℂ ↥(wtSpace (fun i => CartanMatrix.E₈ k i)) := by
    rw [← finrank_wtSpace_foldl L μ, hL]
  rw [h1]
  exact e8_simple_root_weightSpace_finrank_compat k

end Commons.Algebra.Lie.SerreConstruction
