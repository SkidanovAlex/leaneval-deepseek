import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Commons.LinearAlgebra.Matrix

theorem sum_comp_mul_mul {m n : ℕ} (S : Matrix (Fin m) (Fin m) (ZMod 2))
    (T : Matrix (Fin n) (Fin n) (ZMod 2))
    (hS : Function.Bijective S.mulVecLin) (hT : Function.Bijective T.mulVecLin)
    (g : Matrix (Fin m) (Fin n) (ZMod 2) → ℝ) :
    (∑ A : Matrix (Fin m) (Fin n) (ZMod 2), g (S * A * T)) = ∑ A, g A := by
  have hSurjS : Function.Surjective S.mulVec := by simpa only [Matrix.coe_mulVecLin] using hS.2
  have hSurjT : Function.Surjective T.mulVec := by simpa only [Matrix.coe_mulVecLin] using hT.2
  have huS : IsUnit S := Matrix.mulVec_surjective_iff_isUnit.mp hSurjS
  have huT : IsUnit T := Matrix.mulVec_surjective_iff_isUnit.mp hSurjT
  obtain ⟨S', hSS', hS'S⟩ := isUnit_iff_exists.mp huS
  obtain ⟨T', hTT', hT'T⟩ := isUnit_iff_exists.mp huT
  have key1 : ∀ A : Matrix (Fin m) (Fin n) (ZMod 2), S * (S' * A * T') * T = A := by
    intro A
    rw [Matrix.mul_assoc S' A T', ← Matrix.mul_assoc S S' (A * T'), hSS', Matrix.one_mul,
        Matrix.mul_assoc A T' T, hT'T, Matrix.mul_one]
  have key2 : ∀ A : Matrix (Fin m) (Fin n) (ZMod 2), S' * (S * A * T) * T' = A := by
    intro A
    rw [Matrix.mul_assoc S A T, ← Matrix.mul_assoc S' S (A * T), hS'S, Matrix.one_mul,
        Matrix.mul_assoc A T T', hTT', Matrix.mul_one]
  refine Function.Bijective.sum_comp ⟨?_, ?_⟩ g
  · intro A B hAB
    have h : S' * (S * A * T) * T' = S' * (S * B * T) * T' :=
      congrArg (fun X : Matrix (Fin m) (Fin n) (ZMod 2) => S' * X * T') hAB
    rwa [key2 A, key2 B] at h
  · intro B
    exact ⟨S' * B * T', key1 B⟩

end Commons.LinearAlgebra.Matrix