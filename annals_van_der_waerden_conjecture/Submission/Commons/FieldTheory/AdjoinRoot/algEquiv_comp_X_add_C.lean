import Mathlib.RingTheory.AdjoinRoot

namespace Commons.FieldTheory.AdjoinRoot

open Polynomial

noncomputable section

theorem algEquiv_comp_X_add_C (f : Polynomial ℚ) (k : ℚ) :
    Nonempty (AdjoinRoot (f.comp (Polynomial.X + Polynomial.C k)) ≃ₐ[ℚ] AdjoinRoot f) := by
  let g : Polynomial ℚ := f.comp (X + C k)
  let φ : AdjoinRoot g →ₐ[ℚ] AdjoinRoot f :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId ℚ (AdjoinRoot f))
      (AdjoinRoot.root f - algebraMap ℚ (AdjoinRoot f) k) (by
        rw [Algebra.toRingHom_ofId]
        rw [← Polynomial.aeval_def]
        rw [Polynomial.aeval_comp]
        have hx : aeval (AdjoinRoot.root f - algebraMap ℚ (AdjoinRoot f) k)
            (X + C k : Polynomial ℚ) = AdjoinRoot.root f := by
          simp [AdjoinRoot.algebraMap_eq]
        rw [hx]
        rw [AdjoinRoot.aeval_eq]
        exact AdjoinRoot.mk_self (f := f))
  let ψ : AdjoinRoot f →ₐ[ℚ] AdjoinRoot g :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId ℚ (AdjoinRoot g))
      (AdjoinRoot.root g + algebraMap ℚ (AdjoinRoot g) k) (by
        rw [Algebra.toRingHom_ofId]
        rw [← Polynomial.aeval_def]
        have hx : aeval (AdjoinRoot.root g) (X + C k : Polynomial ℚ) =
            AdjoinRoot.root g + algebraMap ℚ (AdjoinRoot g) k := by
          simp [AdjoinRoot.algebraMap_eq]
        rw [← hx]
        rw [← Polynomial.aeval_comp]
        rw [AdjoinRoot.aeval_eq]
        exact AdjoinRoot.mk_self (f := g))
  refine ⟨AlgEquiv.ofAlgHom φ ψ ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    simp [φ, ψ, AdjoinRoot.liftAlgHom_root, AdjoinRoot.algebraMap_eq]
  · apply AdjoinRoot.algHom_ext
    have hφroot : φ (AdjoinRoot.root g) = AdjoinRoot.root f - algebraMap ℚ (AdjoinRoot f) k := by
      simp [φ, AdjoinRoot.liftAlgHom_root]
    have hψroot : ψ (AdjoinRoot.root f) = AdjoinRoot.root g + algebraMap ℚ (AdjoinRoot g) k := by
      simp [ψ, AdjoinRoot.liftAlgHom_root]
    have hψ_comm : ψ (algebraMap ℚ (AdjoinRoot f) k) = algebraMap ℚ (AdjoinRoot g) k := ψ.commutes k
    change ψ (φ (AdjoinRoot.root g)) = AdjoinRoot.root g
    calc
      ψ (φ (AdjoinRoot.root g)) = ψ (AdjoinRoot.root f - algebraMap ℚ (AdjoinRoot f) k) := by
        rw [hφroot]
      _ = ψ (AdjoinRoot.root f) - ψ (algebraMap ℚ (AdjoinRoot f) k) := by simp
      _ = (AdjoinRoot.root g + algebraMap ℚ (AdjoinRoot g) k) - algebraMap ℚ (AdjoinRoot g) k := by
        rw [hψroot, hψ_comm]
      _ = AdjoinRoot.root g := by abel

end

end Commons.FieldTheory.AdjoinRoot