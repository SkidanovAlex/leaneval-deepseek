import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.killingForm_SerreH
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple

namespace Commons.Algebra.Lie.SerreConstruction

/-!
# The Killing form on the Cartan subalgebra of `e₈`, in terms of the inverse Cartan matrix

(The file lives in namespace `Commons.Algebra.Lie.SerreConstruction`, so the name below is
qualified accordingly when imported.)

Let `y, z` lie in the Cartan subalgebra `e8W 0 = span{SerreH i}` of `e₈`, and suppose that
`κ (SerreH i) y = μ i` and `κ (SerreH j) z = ν j` for all `i, j`.  Then

  `κ y z = (1/60) * ∑ i, ∑ j, μᵢ · (A⁻¹)ᵢⱼ · νⱼ`,

where `A⁻¹ = Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv` is the inverse Cartan matrix.

Proof sketch (all inputs are in the commons):
* write `y = ∑ l, c l • SerreH l` using `e8W_zero_eq_span_SerreH` plus linear independence of the
  `SerreH l` (`e8_H_linearIndependent`; you may use `Module.Basis` of the span);
* from `hμ` and `killingForm_SerreH` (`κ (SerreH i) (SerreH j) = 60 * A i j`) get
  `∑ l, (60 * A i l) * c l = μ i`; multiplying by `E8inv` and using `E8inv_mul_E8` gives
  `60 * c j = ∑ i, E8inv j i * μ i`;
* hence `κ y z = 60 * ∑ l, ∑ m, c l * (A l m) * d m = (1/60) * ∑ i, ∑ j, μᵢ (A⁻¹)ᵢⱼ νⱼ`
  using `E8inv * E8 = 1`.
-/

open scoped BigOperators

private abbrev AC : Matrix (Fin 8) (Fin 8) ℂ := CartanMatrix.E₈.map (Int.castRingHom ℂ)

private abbrev IC : Matrix (Fin 8) (Fin 8) ℂ :=
  Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv.map (Int.castRingHom ℂ)

/-- Bilinearity of a bilinear form over two finite sums of scalar multiples. -/
private lemma bilinForm_sum_sum {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) (f g : Fin 8 → ℂ) (v : Fin 8 → V) :
    (B (∑ a, f a • v a)) (∑ b, g b • v b)
      = ∑ a, ∑ b, f a * g b * (B (v a)) (v b) := by
  rw [LinearMap.BilinForm.sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.BilinForm.sum_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  ring

/-- `u ⬝ (M *ᵥ v)` as a double sum of the matrix entries. -/
private lemma dotProduct_mulVec_eq_sum (u : Fin 8 → ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ)
    (v : Fin 8 → ℂ) : u ⬝ᵥ M.mulVec v = ∑ i, ∑ j, u i * M i j * v j := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  show u i * (∑ j, M i j * v j) = ∑ j, u i * M i j * v j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The `E₈` Cartan matrix is symmetric, so the associated bilinear form is symmetric. -/
private lemma dotProduct_mulVec_AC_symm (c d : Fin 8 → ℂ) :
    c ⬝ᵥ AC.mulVec d = AC.mulVec c ⬝ᵥ d := by
  have hA : AC.transpose = AC := by
    ext i j
    simp only [Matrix.transpose_apply, AC, Matrix.map_apply]
    rw [Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm.1 j i]
  have h := Matrix.dotProduct_transpose_mulVec AC.transpose c d
  simp only [hA] at h
  rw [h]
  exact dotProduct_comm _ _

/-- The integral inverse Cartan matrix inverts the Cartan matrix over `ℂ`. -/
private lemma IC_mulVec_AC_mulVec (d : Fin 8 → ℂ) : IC.mulVec (AC.mulVec d) = d := by
  have hIA : IC * AC = 1 := by
    have h := congrArg (fun M => M.map (Int.castRingHom ℂ))
      Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv_mul_E8
    rw [Matrix.map_mul, Matrix.map_one (Int.castRingHom ℂ) (by simp) (by simp)] at h
    simpa only [IC, AC] using h
  rw [Matrix.mulVec_mulVec, hIA, Matrix.one_mulVec]


theorem killingForm_cartanDual (μ ν : Fin 8 → ℤ)
    (y z : LieAlgebra.e₈ ℂ)
    (hy : y ∈ Commons.Algebra.Lie.e8W 0) (hz : z ∈ Commons.Algebra.Lie.e8W 0)
    (hμ : ∀ i : Fin 8, killingForm ℂ (LieAlgebra.e₈ ℂ)
      (Commons.Algebra.Lie.SerreConstruction.SerreH i) y = ((μ i : ℤ) : ℂ))
    (hν : ∀ j : Fin 8, killingForm ℂ (LieAlgebra.e₈ ℂ)
      (Commons.Algebra.Lie.SerreConstruction.SerreH j) z = ((ν j : ℤ) : ℂ)) :
    killingForm ℂ (LieAlgebra.e₈ ℂ) y z
      = (1 / 60) * ∑ i : Fin 8, ∑ j : Fin 8, ((μ i : ℤ) : ℂ) *
          ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j : ℤ) : ℂ) *
          ((ν j : ℤ) : ℂ) := by
  classical
  -- write `y` and `z` as linear combinations of the `SerreH i`
  have hy' : y ∈ Submodule.span ℂ (Set.range SerreH) := by
    rw [← e8W_zero_eq_span_SerreH]; exact hy
  have hz' : z ∈ Submodule.span ℂ (Set.range SerreH) := by
    rw [← e8W_zero_eq_span_SerreH]; exact hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ (v := SerreH)).mp hy'
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ (v := SerreH)).mp hz'
  -- the coordinates of `y` (resp. `z`) relative to `A` are the `μ i` (resp. `ν j`), up to `60`
  have hAc : ∀ i : Fin 8, ((μ i : ℤ) : ℂ) = 60 * (AC.mulVec c) i := by
    intro i
    have h : killingForm ℂ (LieAlgebra.e₈ ℂ) (SerreH i) y
        = ∑ a : Fin 8, c a * (60 * ((CartanMatrix.E₈ i a : ℤ) : ℂ)) := by
      rw [← hc]
      rw [LinearMap.BilinForm.sum_right]
      exact Finset.sum_congr rfl fun a _ => by
        rw [LinearMap.BilinForm.smul_right, killingForm_SerreH]
    rw [← hμ i, h]
    show (∑ a : Fin 8, c a * (60 * ((CartanMatrix.E₈ i a : ℤ) : ℂ)))
        = 60 * ∑ a : Fin 8, ((CartanMatrix.E₈ i a : ℤ) : ℂ) * c a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hAd : ∀ j : Fin 8, ((ν j : ℤ) : ℂ) = 60 * (AC.mulVec d) j := by
    intro j
    have h : killingForm ℂ (LieAlgebra.e₈ ℂ) (SerreH j) z
        = ∑ b : Fin 8, d b * (60 * ((CartanMatrix.E₈ j b : ℤ) : ℂ)) := by
      rw [← hd]
      rw [LinearMap.BilinForm.sum_right]
      exact Finset.sum_congr rfl fun b _ => by
        rw [LinearMap.BilinForm.smul_right, killingForm_SerreH]
    rw [← hν j, h]
    show (∑ b : Fin 8, d b * (60 * ((CartanMatrix.E₈ j b : ℤ) : ℂ)))
        = 60 * ∑ b : Fin 8, ((CartanMatrix.E₈ j b : ℤ) : ℂ) * d b
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- left hand side
  have hL : killingForm ℂ (LieAlgebra.e₈ ℂ) y z = 60 * (c ⬝ᵥ AC.mulVec d) := by
    rw [← hc, ← hd, bilinForm_sum_sum]
    simp only [killingForm_SerreH]
    rw [dotProduct_mulVec_eq_sum]
    simp only [AC, Matrix.map_apply, Int.coe_castRingHom]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  -- right hand side
  have hR : (1 / 60) * (∑ i : Fin 8, ∑ j : Fin 8, ((μ i : ℤ) : ℂ) *
        ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j : ℤ) : ℂ) * ((ν j : ℤ) : ℂ))
      = 60 * (AC.mulVec c ⬝ᵥ d) := by
    have hsum : (∑ i : Fin 8, ∑ j : Fin 8, ((μ i : ℤ) : ℂ) *
          ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j : ℤ) : ℂ) * ((ν j : ℤ) : ℂ))
        = ∑ i : Fin 8, ∑ j : Fin 8, (60 * (AC.mulVec c) i) *
            (IC i j) * (60 * (AC.mulVec d) j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hAc i, hAd j]
      rfl
    rw [hsum]
    have h2 : (∑ i : Fin 8, ∑ j : Fin 8, (60 * (AC.mulVec c) i) * (IC i j) *
          (60 * (AC.mulVec d) j))
        = 3600 * ((AC.mulVec c) ⬝ᵥ IC.mulVec (AC.mulVec d)) := by
      rw [dotProduct_mulVec_eq_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2, IC_mulVec_AC_mulVec d, ← mul_assoc, show (1/60 : ℂ) * 3600 = 60 by norm_num]
  rw [hL, dotProduct_mulVec_AC_symm c d]
  exact hR.symm

end Commons.Algebra.Lie.SerreConstruction
