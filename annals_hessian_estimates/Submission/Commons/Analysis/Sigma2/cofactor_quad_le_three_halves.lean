import Mathlib.Analysis.InnerProductSpace.Spectrum
import Submission.Commons.Analysis.Sigma2.linearized_upper_four
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply
import Submission.Commons.Analysis.InnerProductSpace.inner_smul_one_sub_eq_sum

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem cofactor_quad_le_three_halves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = 4)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4,
        if i < j then hT.eigenvalues hn i * hT.eigenvalues hn j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, hT.eigenvalues hn i) :
    ∀ v : E, ⟪((∑ i : Fin 4, hT.eigenvalues hn i) • (1 : E →L[ℝ] E) - T) v, v⟫
      ≤ (3 / 2 : ℝ) * (∑ i : Fin 4, hT.eigenvalues hn i) * ‖v‖ ^ 2 := by
  intro x
  set S : ℝ := ∑ i : Fin 4, hT.eigenvalues hn i with hS
  -- the eigenvalues of `T` are antitone, so `linearized_upper_four` applies
  have hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → hT.eigenvalues hn j ≤ hT.eigenvalues hn i :=
    hT.eigenvalues_antitone hn
  have hbound : ∀ i : Fin 4, S - hT.eigenvalues hn i ≤ (3 / 2 : ℝ) * S := by
    intro i
    have h := linearized_upper_four (hT.eigenvalues hn) hmono hσ2 hσ1 i
    simpa [hS] using h
  -- diagonalize the quadratic form in the eigenvector basis
  let b : OrthonormalBasis (Fin 4) ℝ E := hT.eigenvectorBasis hn
  have hdiag : ∀ i : Fin 4, T (b i) = hT.eigenvalues hn i • b i :=
    fun i => hT.apply_eigenvectorBasis hn i
  have hquad := Commons.Analysis.InnerProductSpace.inner_smul_one_sub_eq_sum
    b (hT.eigenvalues hn) hdiag S x
  rw [hquad]
  -- bound termwise and use Parseval
  have hstep : ∑ i : Fin 4, (S - hT.eigenvalues hn i) * ⟪b i, x⟫ ^ 2
      ≤ ∑ i : Fin 4, ((3 / 2 : ℝ) * S) * ⟪b i, x⟫ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg _)
  have hsum : ∑ i : Fin 4, ((3 / 2 : ℝ) * S) * ⟪b i, x⟫ ^ 2
      = (3 / 2 : ℝ) * S * ‖x‖ ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    exact OrthonormalBasis.sum_sq_inner_right b x
  calc ∑ i : Fin 4, (S - hT.eigenvalues hn i) * ⟪b i, x⟫ ^ 2
      ≤ ∑ i : Fin 4, ((3 / 2 : ℝ) * S) * ⟪b i, x⟫ ^ 2 := hstep
    _ = (3 / 2 : ℝ) * S * ‖x‖ ^ 2 := hsum
    _ = (3 / 2 : ℝ) * (∑ i : Fin 4, hT.eigenvalues hn i) * ‖x‖ ^ 2 := by rw [hS]

end Commons.Analysis.Sigma2