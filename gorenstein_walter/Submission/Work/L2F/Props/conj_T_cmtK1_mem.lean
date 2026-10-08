import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

open scoped MatrixGroups

/-- Conjugating an element of the reflection coset `cmtK1 F S` by another element of `cmtK1 F S`
stays in `cmtK1 F S`: for `a, b ∈ cmtK1 F S` one has `a * b * a⁻¹ ∈ cmtK1 F S`.

Indeed `(a b a⁻¹) S (a b a⁻¹)⁻¹ = a b (a⁻¹ S a) b⁻¹ a⁻¹`, and `a⁻¹ S a = -S` (from `a S a⁻¹ = -S`
by conjugating, i.e. `conj_inv_of_eq_neg`), so the expression equals
`a (b (-S) b⁻¹) a⁻¹ = a (-(b S b⁻¹)) a⁻¹ = a (-(-S)) a⁻¹ = a S a⁻¹ = -S` (using centrality of
`-1 = negOneGL`). -/
theorem cmtK1_conj_mem (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (a b : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : a ∈ cmtK1 F S) (hb : b ∈ cmtK1 F S) : a * b * a⁻¹ ∈ cmtK1 F S := by
  rw [mem_cmtK1_iff]
  have ha' : (Matrix.SpecialLinearGroup.toGL a)⁻¹ * S * Matrix.SpecialLinearGroup.toGL a =
      negGL F S := by
    have h := conj_inv_of_eq_neg F a S ha
    rw [map_inv, inv_inv] at h
    exact h
  have hval : Matrix.SpecialLinearGroup.toGL (a * b * a⁻¹) =
      Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL b *
        (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hval]
  calc Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL b *
        (Matrix.SpecialLinearGroup.toGL a)⁻¹ * S *
        (Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL b *
          (Matrix.SpecialLinearGroup.toGL a)⁻¹)⁻¹
      = Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL b *
          ((Matrix.SpecialLinearGroup.toGL a)⁻¹ * S *
            Matrix.SpecialLinearGroup.toGL a) *
          (Matrix.SpecialLinearGroup.toGL b)⁻¹ *
          (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by group
    _ = Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL b * negGL F S *
          (Matrix.SpecialLinearGroup.toGL b)⁻¹ *
          (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by rw [ha']
    _ = Matrix.SpecialLinearGroup.toGL a *
          (Matrix.SpecialLinearGroup.toGL b * negGL F S *
            (Matrix.SpecialLinearGroup.toGL b)⁻¹) *
          (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by group
    _ = Matrix.SpecialLinearGroup.toGL a *
          negGL F (Matrix.SpecialLinearGroup.toGL b * S *
            (Matrix.SpecialLinearGroup.toGL b)⁻¹) *
          (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by rw [conj_negGL F b S]
    _ = Matrix.SpecialLinearGroup.toGL a * negGL F (negGL F S) *
          (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by rw [hb]
    _ = Matrix.SpecialLinearGroup.toGL a * S * (Matrix.SpecialLinearGroup.toGL a)⁻¹ := by
          rw [negGL_negGL]
    _ = negGL F S := ha

/-- `T` (with `toGL T * S = (-S) * toGL T`, i.e. `T S T⁻¹ = -S`) preserves the "reflection coset"
`cmtK1 F S = {x ∈ SL(2,F) | x S x⁻¹ = -S}`: for `x ∈ cmtK1 F S` one has `T * x * T⁻¹ ∈ cmtK1 F S`.
Proof: `(T x T⁻¹) S (T x T⁻¹)⁻¹ = T x (T⁻¹ S T) x⁻¹ T⁻¹` and `T⁻¹ S T = -S` (derived from
`hST` and centrality of `-1 = negOneGL`, e.g. `conj_inv_of_eq_neg` applied to the fact that
`T ∈ cmtK1 F S`), so the expression is `-T (x S x⁻¹) T⁻¹ = -T(-S)T⁻¹ = -(-S) = -S` (using
`conj_negGL`, `negGL_negGL` and `Matrix.SpecialLinearGroup.coe_mul`).  Everything stays in
`SL(2,F)`; no characteristic hypothesis is needed. -/
theorem conj_T_cmtK1_mem (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F)
    (hST : Matrix.SpecialLinearGroup.toGL T * S = Work.L2F.Props.negGL F S *
      Matrix.SpecialLinearGroup.toGL T) :
    ∀ x ∈ Work.L2F.Props.cmtK1 F S, T * x * T⁻¹ ∈ Work.L2F.Props.cmtK1 F S := by
  have hT : T ∈ cmtK1 F S := by
    rw [mem_cmtK1_iff_comm]
    exact hST
  intro x hx
  exact cmtK1_conj_mem F S T x hT hx

end Work.L2F.Props
