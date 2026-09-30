import Mathlib
import Submission.Work.Certificates.ChainMapCheck
import Submission.Work.Certificates.SOp.eqb_sound
import Submission.Work.Certificates.SOp.toMatrix_mul
import Submission.Work.Certificates.subsingleton_hom_of_subsingleton

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.Certificates

/-- In a `FinChainCx`, the differential `∂_{k+1} : C_{k+1} → C_k` is the linear map of the
sparse matrix `bd k`.  This is the definitional unfolding of `FinChainCx.toChainComplex`
through the `ChainComplex.of` constructor, exposed as a rewrite rule. -/
theorem toChainComplex_d (C : FinChainCx) (k : ℕ) :
    C.toChainComplex.d (k+1) k = ModuleCat.ofHom (Matrix.toLin' ((C.bd k).toMatrix)) := by
  change ChainComplex.of.d (fun j => ModuleCat.of ℤ (Fin (C.dim j) → ℤ))
      (fun j => ModuleCat.ofHom (Matrix.toLin' ((C.bd j).toMatrix))) (k+1) k
    = ModuleCat.ofHom (Matrix.toLin' ((C.bd k).toMatrix))
  rw [ChainComplex.of_d]

/-- The `k`-th chain group of a `FinChainCx` is a subsingleton whenever `dim k = 0`. -/
theorem subsingleton_X_of_dim_eq_zero (C : FinChainCx) {k : ℕ} (h : C.dim k = 0) :
    Subsingleton (C.toChainComplex.X k) := by
  change Subsingleton (ModuleCat.of ℤ (Fin (C.dim k) → ℤ))
  rw [h]
  infer_instance

theorem chainMapCheck_sound {C D : FinChainCx} {φ : ∀ k, SOp (D.dim k) (C.dim k)} {N : ℕ}
    (hC : ∀ k, N ≤ k → C.dim k = 0) (_hD : ∀ k, N ≤ k → D.dim k = 0)
    (h : chainMapCheck C D φ N = true) :
    ∃ cφ : ChainHom C.toChainComplex D.toChainComplex,
      ∀ k, cφ.f k = ModuleCat.ofHom (Matrix.toLin' ((φ k).toMatrix)) := by
  -- The candidate chain map, whose `k`-th component is the linear map of the matrix of `φ k`.
  refine ⟨⟨fun k => ModuleCat.ofHom (Matrix.toLin' ((φ k).toMatrix)), ?_⟩, fun _ => rfl⟩
  intro i j hij
  -- `hij : (ComplexShape.down ℕ).Rel i j` means `j + 1 = i`, so `i = j + 1`.
  rw [ComplexShape.down_Rel] at hij
  subst hij
  -- Replace the differentials by the linear maps of the sparse matrices.
  rw [toChainComplex_d C j, toChainComplex_d D j]
  change ModuleCat.ofHom (Matrix.toLin' ((φ (j+1)).toMatrix)) ≫
        ModuleCat.ofHom (Matrix.toLin' ((D.bd j).toMatrix))
      = ModuleCat.ofHom (Matrix.toLin' ((C.bd j).toMatrix)) ≫
        ModuleCat.ofHom (Matrix.toLin' ((φ j).toMatrix))
  rcases lt_or_ge j N with hj | hj
  · -- Below `N` the chain-map identity is exactly what `chainMapCheck` verified.
    have hk := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    have hmat : Matrix.toLin' ((D.bd j).toMatrix) ∘ₗ Matrix.toLin' ((φ (j+1)).toMatrix)
        = Matrix.toLin' ((φ j).toMatrix) ∘ₗ Matrix.toLin' ((C.bd j).toMatrix) := by
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← SOp.toMatrix_mul (D.bd j) (φ (j+1)), ← SOp.toMatrix_mul (φ j) (C.bd j)]
      exact congrArg Matrix.toLin' (SOp.eqb_sound hk).symm
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, hmat]
  · -- Above `N` the source `C_{j+1}` vanishes, so both composites agree trivially.
    have hsub : Subsingleton (C.toChainComplex.X (j+1)) :=
      subsingleton_X_of_dim_eq_zero C (hC (j+1) (by omega))
    exact (subsingleton_hom_of_subsingleton (M := C.toChainComplex.X (j+1))
      (N := D.toChainComplex.X j)).elim _ _

end Work.Certificates
