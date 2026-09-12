import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

namespace Commons.LinearAlgebra.Independence

/-- Classical: a family of `j ≤ d` integer vectors in `ℤ^d` which is `ℤ`-linearly
independent (as real-valued functions on `Fin d`, i.e. no non-trivial integer relation)
remains `ℝ`-linearly independent when viewed in `ℝ^d`.

The hypotheses and conclusion are phrased with the real-valued functions
`fun i : Fin d => (v a i : ℝ)`; the `ℤ`-module structure on `Fin d → ℝ` is the
canonical one. -/
theorem li_real_of_li_int {d j : ℕ} (hj : j ≤ d) (v : Fin j → Fin d → ℤ)
    (h : LinearIndependent ℤ (fun a : Fin j => fun i : Fin d => (v a i : ℝ))) :
    LinearIndependent ℝ (fun a : Fin j => fun i : Fin d => (v a i : ℝ)) := by
  -- Embed ℤ^d into ℝ^d coordinatewise; the hypothesis says the composition is
  -- ℤ-linearly independent, hence the original integer family is ℤ-linearly independent.
  let g : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) :=
    { toFun := fun x i => (x i : ℝ)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro n x
        ext i
        simp }
  have hInt : LinearIndependent ℤ (fun a : Fin j => v a) := by
    exact LinearIndependent.of_comp g h
  -- Base change: a ℤ-linearly independent integer family remains ℝ-linearly
  -- independent after coercion to ℝ^d (Mathlib: `linearIndependent_algebraMap_comp_iff`).
  have hif : LinearIndependent ℝ (fun a : Fin j => fun i : Fin d => ((v a i : ℤ) : ℝ)) ↔
      LinearIndependent ℤ (fun a : Fin j => v a) := by
    exact linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (ι := Fin j) (ι' := Fin d)
      (v := v)
  simpa using hif.mpr hInt

end Commons.LinearAlgebra.Independence