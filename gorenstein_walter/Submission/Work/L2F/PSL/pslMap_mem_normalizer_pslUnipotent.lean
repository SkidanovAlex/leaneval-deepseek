import Mathlib
import Submission.Work.L2F.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- The elementary computation behind the normalizer statement: an upper triangular matrix
`A ∈ SL(2,F)` (upper triangular meaning `A 1 0 = 0`) conjugates the upper unipotent element
`unipotent b = !![1,b;0,1]` to `unipotent (p² b)`, where `p = A 0 0`.

Writing `A = !![p,q;0,s]` with `p * s = 1` (its determinant is `1`), one has
`A * unipotent b = unipotent (p² b) * A`, since the `(0,1)`-entry of the left-hand side is
`p*b + q` and that of the right-hand side is `q + p² b s = q + p b`. Multiplying by `A⁻¹`
on the right gives the claim. -/
theorem conj_unipotent (F : Type*) [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (b : F) :
    (A * Work.PSL2.unipotent F b * A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) =
      Work.PSL2.unipotent F (((A : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * b) := by
  -- The determinant of `A = !![p,q;0,s]` is `p * s`, so `p * s = 1`.
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  have hps : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    rw [hA, mul_zero, sub_zero] at hdet
    exact hdet
  -- hence `p² * b * s = p * b`.
  have key : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b * (A : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 * b := by
    calc (A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b * (A : Matrix (Fin 2) (Fin 2) F) 1 1
        = ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1) *
            ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * b) := by ring
      _ = 1 * ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * b) := by rw [hps]
      _ = (A : Matrix (Fin 2) (Fin 2) F) 0 0 * b := one_mul _
  have hmul : A * Work.PSL2.unipotent F b =
      Work.PSL2.unipotent F (((A : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * b) * A := by
    apply Subtype.ext
    change ((A * Work.PSL2.unipotent F b : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      ((Work.PSL2.unipotent F (((A : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * b) * A :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_unipotent,
        Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_unipotent,
        Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F), Matrix.mul_fin_two,
        Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, key]
    all_goals ring
  rw [hmul, mul_assoc, mul_inv_cancel, mul_one]

/-- Conjugation by `pslMap A` maps the upper unipotent subgroup of `PSL(2,F)` into itself,
for `A ∈ SL(2,F)` upper triangular.  This is `conj_unipotent` transported through the
quotient map `pslMap`, using that `pslUnipotent F` is the image of the range of
`unipotentHom F`. -/
theorem pslMap_conj_mem_pslUnipotent (F : Type*) [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hx : x ∈ Work.L2F.pslUnipotent F) :
    Work.PSL2.pslMap F A * x * (Work.PSL2.pslMap F A)⁻¹ ∈ Work.L2F.pslUnipotent F := by
  -- `x = pslMap A'` for some upper unipotent `A' = unipotent b`.
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
  have hbm : Work.PSL2.unipotentHom F m = Work.PSL2.unipotent F (Multiplicative.toAdd m) := rfl
  rw [hbm]
  -- pass the conjugation through `pslMap` and apply the matrix computation
  rw [← map_mul, ← map_inv, ← map_mul]
  rw [conj_unipotent F A hA]
  exact Subgroup.mem_map.mpr ⟨Work.PSL2.unipotent F (((A : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 *
    Multiplicative.toAdd m), ⟨Multiplicative.ofAdd _, rfl⟩, rfl⟩

/-- An upper triangular `G ∈ SL(2,F)` (i.e. its `(1,0)`-entry vanishes) normalizes the upper
unipotent subgroup, hence `pslMap G` normalizes `pslUnipotent F` in `PSL(2,F)`.
Key computation: for `G = !![p,q;0,s]` with `p*s = 1` and `u = unipotent c`,
`G u G⁻¹ = unipotent (p^2 * c)` is again upper unipotent. -/
theorem pslMap_mem_normalizer_pslUnipotent (F : Type*) [Field F]
    (G : Matrix.SpecialLinearGroup (Fin 2) F)
    (hG : (G : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    Work.PSL2.pslMap F G ∈ Subgroup.normalizer
      (Work.L2F.pslUnipotent F : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
  -- The matrix of `G⁻¹` is `G.adjugate = !![G 1 1, -G 0 1; -G 1 0, G 0 0]`, whose
  -- `(1,0)`-entry is `-G 1 0 = 0`, so the computation
  -- applies to `G⁻¹` as well; that supplies the reverse implication of the normalizer test.
  have hGinv : ((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [Matrix.adjugate_fin_two, hG]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact pslMap_conj_mem_pslUnipotent F G hG h hh
  · intro hh
    have hx : Work.PSL2.pslMap F G⁻¹ *
        (Work.PSL2.pslMap F G * h * (Work.PSL2.pslMap F G)⁻¹) *
        (Work.PSL2.pslMap F G⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    rw [← hx]
    exact pslMap_conj_mem_pslUnipotent F G⁻¹ hGinv _ hh

end Work.L2F.PSL
