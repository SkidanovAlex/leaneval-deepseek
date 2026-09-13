import Mathlib
import Submission.Commons.Analysis.Sigma2.cofactor_psd_four

namespace Commons.Analysis.Sigma2

open scoped RealInnerProductSpace

/-- For a symmetric endomorphism `T` of a finite-dimensional real inner product space `E` of
dimension `4`, with eigenvalues `λᵢ = hT.eigenvalues hn i` sorted decreasingly, the quadratic form
of `(∑ᵢ λᵢ) • 1 - T` dominates `((∑ᵢ λᵢ) - λ₀) ‖v‖²`:

`((σ₁) - λ₀) * ‖v‖² ≤ ⟪(σ₁ • 1 - T) v, v⟫`.

Indeed the difference of the two sides is `⟪(λ₀ • 1 - T) v, v⟫ ≥ 0`, since `λ₀` is the largest
eigenvalue (the eigenvalues are sorted decreasingly), so that `λ₀ • 1 - T` is positive
semidefinite. -/
theorem cofactor_quad_ge_min {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = 4)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4,
        if i < j then hT.eigenvalues hn i * hT.eigenvalues hn j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, hT.eigenvalues hn i) :
    ∀ v : E, ((∑ i : Fin 4, hT.eigenvalues hn i) - hT.eigenvalues hn 0) * ‖v‖ ^ 2 ≤
      inner ℝ (((∑ i : Fin 4, hT.eigenvalues hn i) • (1 : E →L[ℝ] E) - T) v) v := by
  intro v
  -- `λ 0` is the largest eigenvalue since `eigenvalues` is listed in decreasing order.
  have hmax : ∀ i : Fin 4, hT.eigenvalues hn i ≤ hT.eigenvalues hn 0 :=
    fun i => hT.eigenvalues_antitone hn (Fin.zero_le i)
  -- hence `λ₀ • 1 - T` is positive semidefinite.
  have hnn : 0 ≤ inner ℝ ((hT.eigenvalues hn 0 • (1 : E →L[ℝ] E) - T) v) v :=
    quadform_nonneg_of_eigen_le hT 4 hn (hT.eigenvalues hn 0) hmax v
  -- `⟪(c • 1) v, v⟫ = c * ‖v‖²`.
  have hsmul : ∀ c : ℝ,
      inner ℝ ((c • (1 : E →L[ℝ] E)) v) v = c * ‖v‖ ^ 2 := by
    intro c
    rw [smul_apply, one_apply_eq_self, real_inner_smul_left, real_inner_self_eq_norm_sq]
  -- decompose the quadratic form.
  have key : inner ℝ (((∑ i : Fin 4, hT.eigenvalues hn i) • (1 : E →L[ℝ] E) - T) v) v
      = ((∑ i : Fin 4, hT.eigenvalues hn i) - hT.eigenvalues hn 0) * ‖v‖ ^ 2
        + inner ℝ ((hT.eigenvalues hn 0 • (1 : E →L[ℝ] E) - T) v) v := by
    rw [sub_apply, inner_sub_left, sub_apply, inner_sub_left, hsmul, hsmul]
    ring
  rw [key]
  linarith

end Commons.Analysis.Sigma2
