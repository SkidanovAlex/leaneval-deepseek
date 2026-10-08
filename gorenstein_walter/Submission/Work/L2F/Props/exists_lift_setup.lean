import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Involution.lift_sq_neg_one
import Submission.Work.L2F.Props.isSquare_det_iff_mem_toPGL_range
import Submission.Work.L2F.Props.isSquare_det_of_commute_sq_neg_one
import Submission.Work.L2F.Props.exists_sl_lift_sq_neg_one
import Submission.Work.L2F.Props.center_sq_eq_one

namespace Work.L2F.Props

open scoped MatrixGroups
open Matrix

/-- Group-theoretic bookkeeping for the sign in `exists_lift_setup`: if `A` and `Q * Q` are
central and `P * Q * P⁻¹ = A * Q`, then `A * A = 1`.

Indeed `(P * Q * P⁻¹)² = P * (Q * Q) * P⁻¹ = Q * Q` (as `Q * Q` is central), while
`(A * Q)² = A * A * (Q * Q)` (as `A` is central); cancelling `Q * Q` gives `A * A = 1`. -/
theorem sq_eq_one_of_conj_eq_mul {G : Type*} [Group G] (P Q A : G)
    (hA : ∀ X : G, A * X = X * A) (hQ : ∀ X : G, (Q * Q) * X = X * (Q * Q))
    (h : P * Q * P⁻¹ = A * Q) : A * A = 1 := by
  have h1 : (P * Q * P⁻¹) * (P * Q * P⁻¹) = Q * Q := by
    calc (P * Q * P⁻¹) * (P * Q * P⁻¹) = P * (Q * Q) * P⁻¹ := by group
      _ = Q * Q := by rw [← hQ P]; group
  have h2 : (P * Q * P⁻¹) * (P * Q * P⁻¹) = A * A * (Q * Q) := by
    rw [h]
    calc (A * Q) * (A * Q) = A * (Q * A) * Q := by group
      _ = A * (A * Q) * Q := by rw [← hA Q]
      _ = A * A * (Q * Q) := by group
  exact mul_right_cancel (by rw [← h2, h1, one_mul])

/-- Lifting the data of `PGL2CommutatorTorusProp` to matrices: `t ∈ L₂(q)` lifts to `T ∈ SL(2,F)`
with `T² = -1`, `s ∉ L₂(q)` lifts to `S ∈ GL(2,F)` with `S² = lam • 1` and nonsquare determinant,
and the commutativity of `t, s` forces `T S = - S T` (the sign cannot be changed by rescaling `S`,
which acts on `S` by central elements: if `T S = S T` then `S` lies in `F[T]²` and `S² = lam • 1`
forces `S` scalar or `S = bT`, whence `det S` is a square, contradicting `s ∉ L₂(q)`).
The `T` part is `Work.L2F.Involution.lift_sq_neg_one` composed with the injectivity of
`Matrix.ProjectiveSpecialLinearGroup.toPGL`. -/
theorem exists_lift_setup (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (t s : Matrix.ProjGenLinGroup (Fin 2) F)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hcomm : t * s = s * t)
    (htL : t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →*
        Matrix.ProjGenLinGroup (Fin 2) F).range)
    (hsL : s ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →*
        Matrix.ProjGenLinGroup (Fin 2) F).range) :
    ∃ (S : Matrix.GeneralLinearGroup (Fin 2) F) (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F),
      lam ≠ 0 ∧
      Matrix.ProjGenLinGroup.mk S = s ∧
      Matrix.SpecialLinearGroup.toPGL T = t ∧
      (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1 ∧
      (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1 ∧
      Matrix.SpecialLinearGroup.toGL T * S = Work.L2F.Props.negGL F S *
        Matrix.SpecialLinearGroup.toGL T ∧
      ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det ∧
      ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
  -- **The lift `T ∈ SL(2,F)` of `t`, with `T² = -1`.**
  obtain ⟨T, hTt, hT2⟩ := exists_sl_lift_sq_neg_one F h2 t ht htL
  -- **The lift `S ∈ GL(2,F)` of `s`.**
  obtain ⟨S, hSs⟩ := Matrix.ProjGenLinGroup.mk_surjective s
  -- `s ^ 2 = 1`, so `S * S` is central: it is a scalar matrix `scalar u`.
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hS2mk : Matrix.ProjGenLinGroup.mk (S * S) = 1 := by
    rw [map_mul, hSs, ← pow_two, hs2]
  have hS2mem : S * S ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hS2mk
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) u = S * S := by
    have h := hS2mem
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    exact h
  have hS2mat : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = (u : F) • 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, ← hu, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  -- `det S` is not a square: otherwise `S` could be rescaled into `SL(2,F)`, giving `s ∈ L₂(F)`.
  have hnotsq : ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det := fun h =>
    hsL ((isSquare_det_iff_mem_toPGL_range F S s hSs).mp h)
  -- **The sign.**  Write `P` for `toGL T`; in `PGL(2,F)`, `P` and `S` commute, so `P S = S P A`
  -- for a central `A`, and `(P S P⁻¹)² = S² = (A S)²` forces `A² = 1`, i.e. `A = ±1`.
  set P : Matrix.GeneralLinearGroup (Fin 2) F := Matrix.SpecialLinearGroup.toGL T with hP
  have hPs : Matrix.ProjGenLinGroup.mk P = t := by rw [hP]; exact hTt
  have hmkeq : Matrix.ProjGenLinGroup.mk (P * S) = Matrix.ProjGenLinGroup.mk (S * P) := by
    rw [map_mul, map_mul, hPs, hSs]
    exact hcomm
  obtain ⟨v, hv⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmkeq
  set A : Matrix.GeneralLinearGroup (Fin 2) F :=
    (Matrix.GeneralLinearGroup.scalar (Fin 2) v)⁻¹ with hAdef
  have hAcenter : A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [hAdef, ← map_inv, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨v⁻¹, rfl⟩
  have hAcomm : ∀ X : Matrix.GeneralLinearGroup (Fin 2) F, A * X = X * A :=
    fun X => (Subgroup.mem_center_iff.mp hAcenter X).symm
  have hQcomm : ∀ X : Matrix.GeneralLinearGroup (Fin 2) F, (S * S) * X = X * (S * S) :=
    fun X => (Subgroup.mem_center_iff.mp hS2mem X).symm
  have hPB : P * S = S * P * A := by
    rw [hAdef]
    calc P * S = (P * S) * Matrix.GeneralLinearGroup.scalar (Fin 2) v *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) v)⁻¹ := by group
      _ = (S * P) * (Matrix.GeneralLinearGroup.scalar (Fin 2) v)⁻¹ := by rw [hv]
  have hSPA : S * P * A = A * S * P := by
    rw [mul_assoc S P A, ← hAcomm P, ← mul_assoc S A P, ← hAcomm S]
  have hW : P * S * P⁻¹ = A * S := by
    rw [hPB, hSPA]
    group
  have hAA : A * A = 1 :=
    sq_eq_one_of_conj_eq_mul P S A hAcomm hQcomm hW
  -- **The conclusion.**  `A = 1` would make `S` commute with `T`, forcing `det S` to be a square;
  -- hence `A = -1`, i.e. `T S = - S T`.
  have hfin : P * S = Work.L2F.Props.negGL F S * P := by
    rcases center_sq_eq_one F A hAcenter hAA with hA1 | hAneg
    · exfalso
      have hPS : P * S = S * P := by
        have h' : P * S * P⁻¹ = S := by rw [hW, hA1, one_mul]
        calc P * S = (P * S * P⁻¹) * P := by group
          _ = S * P := by rw [h']
      rw [hP] at hPS
      exact hnotsq (isSquare_det_of_commute_sq_neg_one F h2 T S (u : F) hT2 hS2mat hPS)
    · have h' : P * S * P⁻¹ = Work.L2F.Props.negGL F S := by rw [hW, hAneg]
      calc P * S = (P * S * P⁻¹) * P := by group
        _ = Work.L2F.Props.negGL F S * P := by rw [h']
  refine ⟨S, T, (u : F), u.ne_zero, hSs, hTt, hS2mat, hT2, hfin, hnotsq, ?_⟩
  intro c hc
  exact hnotsq ⟨c, by rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]; ring⟩

end Work.L2F.Props
