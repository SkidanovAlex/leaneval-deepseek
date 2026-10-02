import Mathlib
import Submission.Work.ThomBordism.OrthFrame.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-!
# The determinant sign of a pair frame is the product of the two block signs

Let `Euc (8+k)` be written as the concatenation of a `Fin 8`-frame `F` and a `Fin k`-frame `G`, and
similarly with primed frames.  If the primed frames are related to the unprimed ones by the
change-of-frame matrices `C` and `M` (`F a = ∑ C a' a • F' a'`, `G b = ∑ M b' b • G' b'`), then the
determinant sign of the pair frame changes by the product of the two block signs:

  `sign det (pairMat F G) · sign det (pairMat F' G') = sign (C.det) · sign (M.det)`.

This is the algebraic content of "the sum of a vector bundle with its complement is trivial": the
sign cocycle of the whole bundle trivialises, so the product of the two block cocycles is a
coboundary.
-/
open scoped BigOperators

namespace Work.ThomBordism.OrthFrame

open Work.ThomBordism.PontryaginThom

noncomputable section

/-- The coordinate expansion of a frame vector in the primed frame. -/
theorem pairMat_coord_expand {k : ℕ}
    {F F' : Fin 8 → Euc (8 + k)} {G G' : Fin k → Euc (8 + k)}
    {C : Matrix (Fin 8) (Fin 8) ℝ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hC : ∀ a, F a = ∑ a', C a' a • F' a')
    (hM : ∀ b, G b = ∑ b', M b' b • G' b') (r : Fin 8 ⊕ Fin k) :
    (∀ a : Fin 8, eucToFun (8 + k) (F a) (finSumFinEquiv r)
        = ∑ a', C a' a * eucToFun (8 + k) (F' a') (finSumFinEquiv r)) ∧
    (∀ b : Fin k, eucToFun (8 + k) (G b) (finSumFinEquiv r)
        = ∑ b', M b' b * eucToFun (8 + k) (G' b') (finSumFinEquiv r)) := by
  constructor
  · intro a
    rw [hC a]
    simp only [map_sum, Finset.sum_apply, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
  · intro b
    rw [hM b]
    simp only [map_sum, Finset.sum_apply, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]

/-- The coordinate matrix of the pair frame is the block matrix built from the two blocks. -/
theorem pairMat_mul_fromBlocks {k : ℕ}
    {F F' : Fin 8 → Euc (8 + k)} {G G' : Fin k → Euc (8 + k)}
    {C : Matrix (Fin 8) (Fin 8) ℝ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hC : ∀ a, F a = ∑ a', C a' a • F' a')
    (hM : ∀ b, G b = ∑ b', M b' b • G' b') :
    pairMat F G = pairMat F' G' * Matrix.fromBlocks C 0 (0 : Matrix (Fin k) (Fin 8) ℝ) M := by
  ext r c
  obtain ⟨hC', hM'⟩ := pairMat_coord_expand hC hM r
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  match c with
  | Sum.inl a =>
      simp only [pairMat_inl, pairMat_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, add_zero, zero_add]
      rw [hC' a]
      exact Finset.sum_congr rfl fun a' _ => by rw [mul_comm]
  | Sum.inr b =>
      simp only [pairMat_inl, pairMat_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, add_zero, zero_add]
      rw [hM' b]
      exact Finset.sum_congr rfl fun b' _ => by rw [mul_comm]

/-- **The determinant sign of the pair frame is the product of the two block determinant signs.** -/
theorem sign_det_pairMat {k : ℕ}
    {F F' : Fin 8 → Euc (8 + k)} {G G' : Fin k → Euc (8 + k)}
    {C : Matrix (Fin 8) (Fin 8) ℝ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hC : ∀ a, F a = ∑ a', C a' a • F' a')
    (hM : ∀ b, G b = ∑ b', M b' b • G' b')
    (hdet : (pairMat F' G').det ≠ 0) (hCdet : C.det ≠ 0) (hMdet : M.det ≠ 0) :
    Real.sign (pairMat F G).det * Real.sign (pairMat F' G').det
      = Real.sign C.det * Real.sign M.det := by
  have hblock := pairMat_mul_fromBlocks hC hM
  have hdetmul : (pairMat F G).det = (pairMat F' G').det * (C.det * M.det) := by
    rw [hblock, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂]
  have hblockdet : C.det * M.det ≠ 0 := mul_ne_zero hCdet hMdet
  have hsig : Real.sign (pairMat F G).det
      = Real.sign (pairMat F' G').det * (Real.sign C.det * Real.sign M.det) := by
    rw [hdetmul, sign_mul_of_ne_zero hdet hblockdet, sign_mul_of_ne_zero hCdet hMdet]
  have hsquare := sign_mul_self_of_ne_zero hdet
  calc Real.sign (pairMat F G).det * Real.sign (pairMat F' G').det
      = Real.sign (pairMat F' G').det * (Real.sign C.det * Real.sign M.det)
          * Real.sign (pairMat F' G').det := by rw [hsig]
    _ = (Real.sign (pairMat F' G').det * Real.sign (pairMat F' G').det)
          * (Real.sign C.det * Real.sign M.det) := by ring
    _ = Real.sign C.det * Real.sign M.det := by rw [hsquare, one_mul]

end

end Work.ThomBordism.OrthFrame
