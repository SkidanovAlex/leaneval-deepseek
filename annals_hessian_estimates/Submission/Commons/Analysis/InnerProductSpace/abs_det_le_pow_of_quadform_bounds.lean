import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace in
theorem abs_det_le_pow_of_quadform_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : E →L[ℝ] E} (hS : S.IsSymmetric)
    {k : ℝ} (hk : 0 ≤ k) (h1 : ∀ v : E, 0 ≤ ⟪S v, v⟫) (h2 : ∀ v : E, ⟪S v, v⟫ ≤ k * ‖v‖ ^ 2) :
    |LinearMap.det (S : E →ₗ[ℝ] E)| ≤ k ^ Module.finrank ℝ E := by
  -- The eigenvalues `hS.eigenvalues rfl i` all lie in `[0, k]`.
  have hinner (i : Fin (Module.finrank ℝ E)) :
      ⟪S (hS.eigenvectorBasis rfl i), (hS.eigenvectorBasis rfl i)⟫
        = hS.eigenvalues rfl i := by
    have hSb : (S : E →ₗ[ℝ] E) (hS.eigenvectorBasis rfl i)
        = (hS.eigenvalues rfl i) • (hS.eigenvectorBasis rfl i) :=
      hS.apply_eigenvectorBasis rfl i
    have hb : ‖hS.eigenvectorBasis rfl i‖ = 1 := (hS.eigenvectorBasis rfl).orthonormal.1 i
    calc ⟪S (hS.eigenvectorBasis rfl i), (hS.eigenvectorBasis rfl i)⟫
        = ⟪(hS.eigenvectorBasis rfl i), S (hS.eigenvectorBasis rfl i)⟫ :=
          (real_inner_comm (S (hS.eigenvectorBasis rfl i)) _).symm
      _ = ⟪(hS.eigenvectorBasis rfl i), (S : E →ₗ[ℝ] E) (hS.eigenvectorBasis rfl i)⟫ := rfl
      _ = (hS.eigenvalues rfl i) * (‖hS.eigenvectorBasis rfl i‖ : ℝ)^2 :=
          inner_product_apply_eigenvector hSb
      _ = hS.eigenvalues rfl i := by rw [hb]; ring
  have hnonneg (i : Fin (Module.finrank ℝ E)) : 0 ≤ hS.eigenvalues rfl i := by
    rw [← hinner i]; exact h1 _
  have hle (i : Fin (Module.finrank ℝ E)) : hS.eigenvalues rfl i ≤ k := by
    have h := h2 (hS.eigenvectorBasis rfl i)
    rw [hinner i] at h
    have hb : ‖hS.eigenvectorBasis rfl i‖ = 1 := (hS.eigenvectorBasis rfl).orthonormal.1 i
    rw [hb] at h
    simpa using h
  -- The determinant is the product of the eigenvalues.
  have hdet : LinearMap.det (S : E →ₗ[ℝ] E)
      = ∏ i : Fin (Module.finrank ℝ E), (hS.eigenvalues rfl i : ℝ) :=
    hS.det_eq_prod_eigenvalues rfl
  have hprod_le : (∏ i : Fin (Module.finrank ℝ E), (hS.eigenvalues rfl i : ℝ))
      ≤ ∏ _i : Fin (Module.finrank ℝ E), k := by
    apply Finset.prod_le_prod
    · intro i _; exact hnonneg i
    · intro i _; exact hle i
  have hkpow : (∏ _i : Fin (Module.finrank ℝ E), k) = k ^ Module.finrank ℝ E := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdet]
  rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => hnonneg i))]
  exact le_trans hprod_le (le_of_eq hkpow)

end Commons.Analysis.InnerProductSpace