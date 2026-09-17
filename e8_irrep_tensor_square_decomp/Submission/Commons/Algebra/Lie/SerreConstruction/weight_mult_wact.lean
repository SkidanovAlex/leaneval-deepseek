import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.weight_mult_reflect

namespace Commons.Algebra.Lie.SerreConstruction

/-- Auxiliary form of `weight_mult_wact` phrased with the weight space `Mwt`. -/
theorem weight_mult_wact_aux {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule L8 M] [LieModule ℂ L8 M] [Module.Finite ℂ M]
    (L : List (Fin 8)) (μ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(Mwt (M := M) μ)
      = Module.finrank ℂ ↥(Mwt (M := M)
          (Commons.LinearAlgebra.Matrix.Cartan.wact L μ)) := by
  induction L generalizing μ with
  | nil => rfl
  | cons i L ih =>
      rw [Commons.LinearAlgebra.Matrix.Cartan.wact_cons]
      exact (weight_mult_reflect (M := M) i μ).trans
        (ih (Commons.LinearAlgebra.Matrix.Cartan.sref i μ))

/-- Full `W`-invariance of weight multiplicities, in the form needed for the dominant-chamber
Freudenthal recursion: the multiplicity of `μ` equals that of its image under any word `L` of
simple reflections (`wact L` = the fold of `sref` over `L`).  Immediate from
`Commons.Algebra.Lie.SerreConstruction.weight_mult_reflect` by induction on the word. -/
theorem weight_mult_wact {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 M]
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M] [Module.Finite ℂ M]
    (L : List (Fin 8)) (μ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(⨅ j : Fin 8, Module.End.eigenspace
        (LieModule.toEnd ℂ Commons.Algebra.Lie.SerreConstruction.L8 M
          (Commons.Algebra.Lie.SerreConstruction.SerreH j)) ((μ j : ℤ) : ℂ))
      = Module.finrank ℂ ↥(⨅ j : Fin 8, Module.End.eigenspace
        (LieModule.toEnd ℂ Commons.Algebra.Lie.SerreConstruction.L8 M
          (Commons.Algebra.Lie.SerreConstruction.SerreH j))
        (((Commons.LinearAlgebra.Matrix.Cartan.wact L μ) j : ℤ) : ℂ)) :=
  weight_mult_wact_aux (M := M) L μ

end Commons.Algebra.Lie.SerreConstruction
