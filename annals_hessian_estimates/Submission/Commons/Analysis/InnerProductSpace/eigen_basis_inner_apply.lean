import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace in
theorem eigen_basis_inner_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (i j : Fin (Module.finrank ℝ E)) :
    ⟪T ((hT.eigenvectorBasis rfl) i), (hT.eigenvectorBasis rfl) j⟫ =
      if i = j then hT.eigenvalues rfl i else 0 := by
  classical
  rw [show T ((hT.eigenvectorBasis rfl) i) =
      (hT.eigenvalues rfl i : ℝ) • (hT.eigenvectorBasis rfl) i from
        hT.apply_eigenvectorBasis rfl i,
    inner_smul_left, (hT.eigenvectorBasis rfl).inner_eq_ite i j]
  split_ifs with h
  · simp
  · simp

end Commons.Analysis.InnerProductSpace