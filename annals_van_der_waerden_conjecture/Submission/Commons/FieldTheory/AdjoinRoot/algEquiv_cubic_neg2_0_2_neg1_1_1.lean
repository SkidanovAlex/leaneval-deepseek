import Mathlib.RingTheory.AdjoinRoot

namespace Commons.FieldTheory.AdjoinRoot

open Polynomial
open _root_.AdjoinRoot

noncomputable section

theorem algEquiv_cubic_neg2_0_2_neg1_1_1 :
    Nonempty (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ) : Polynomial ℚ) ≃ₐ[ℚ]
      AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ)) := by
  let p : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ)
  let q : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ)
  have hC2 : Polynomial.C (2 : ℚ) = (2 : Polynomial ℚ) := rfl
  have hcomp_f : p.comp (1 + X - X ^ 2) = -(X ^ 3 - X ^ 2 - X - 1) * q := by
    simp [p, q, hC2]
    ring
  have hcomp_g : q.comp (X - X ^ 2) = (-X ^ 3 + 2 * X ^ 2 - 2 * X + 2) * p := by
    simp [p, q, hC2]
    ring
  have hpoly_inv1 : ((1 + X - X ^ 2) - (1 + X - X ^ 2) ^ 2 - X : Polynomial ℚ) = -X * q := by
    simp [q, hC2]
    ring
  have hpoly_inv2 : ((1 + (X - X ^ 2) - (X - X ^ 2) ^ 2) - X : Polynomial ℚ) = (1 - X) * p := by
    simp [p]
    ring
  have hf_aeval : Polynomial.aeval (1 + root q - root q ^ 2) p = 0 := by
    rw [show (1 + root q - root q ^ 2) =
        Polynomial.aeval (root q : AdjoinRoot q) (1 + X - X ^ 2 : Polynomial ℚ) by simp]
    rw [← Polynomial.aeval_comp (x := root q)]
    rw [hcomp_f]
    simp [AdjoinRoot.aeval_eq]
  have hg_aeval : Polynomial.aeval (root p - root p ^ 2) q = 0 := by
    rw [show (root p - root p ^ 2) =
        Polynomial.aeval (root p : AdjoinRoot p) (X - X ^ 2 : Polynomial ℚ) by simp]
    rw [← Polynomial.aeval_comp (x := root p)]
    rw [hcomp_g]
    simp [AdjoinRoot.aeval_eq]
  have hf' : p.eval₂ (AdjoinRoot.of q) (1 + root q - root q ^ 2) = 0 := by
    simpa [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq] using hf_aeval
  have hg' : q.eval₂ (AdjoinRoot.of p) (root p - root p ^ 2) = 0 := by
    simpa [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq] using hg_aeval
  have hf : p.eval₂ (Algebra.ofId ℚ (AdjoinRoot q)) (1 + root q - root q ^ 2) = 0 := by
    simpa [Algebra.toRingHom_ofId, AdjoinRoot.algebraMap_eq] using hf'
  have hg : q.eval₂ (Algebra.ofId ℚ (AdjoinRoot p)) (root p - root p ^ 2) = 0 := by
    simpa [Algebra.toRingHom_ofId, AdjoinRoot.algebraMap_eq] using hg'
  let f : AdjoinRoot p →ₐ[ℚ] AdjoinRoot q :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId ℚ (AdjoinRoot q)) (1 + root q - root q ^ 2) hf
  let g : AdjoinRoot q →ₐ[ℚ] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ (AdjoinRoot p)) (root p - root p ^ 2) hg
  have h1 : f.comp g = AlgHom.id ℚ (AdjoinRoot q) := by
    apply AdjoinRoot.algHom_ext
    simp [f, g, AdjoinRoot.liftAlgHom_root]
    have hroot : Polynomial.aeval (root q)
        (((1 + X - X ^ 2) - (1 + X - X ^ 2) ^ 2 - X : Polynomial ℚ)) = 0 := by
      rw [hpoly_inv1]
      simp [AdjoinRoot.aeval_eq]
    have hdesired : (1 + root q - root q ^ 2) - (1 + root q - root q ^ 2) ^ 2 - root q = 0 := by
      simpa using hroot
    linear_combination hdesired
  have h2 : g.comp f = AlgHom.id ℚ (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    simp [f, g, AdjoinRoot.liftAlgHom_root]
    have hroot : Polynomial.aeval (root p)
        (((1 + (X - X ^ 2) - (X - X ^ 2) ^ 2) - X : Polynomial ℚ)) = 0 := by
      rw [hpoly_inv2]
      simp [AdjoinRoot.aeval_eq]
    have hdesired :
        (1 + (root p - root p ^ 2) - (root p - root p ^ 2) ^ 2) - root p = 0 := by
      simpa using hroot
    linear_combination hdesired
  exact ⟨AlgEquiv.ofAlgHom f g h1 h2⟩

end

end Commons.FieldTheory.AdjoinRoot