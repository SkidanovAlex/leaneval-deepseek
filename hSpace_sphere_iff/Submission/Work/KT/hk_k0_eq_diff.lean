import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-- The class of a zero matrix is zero. -/
lemma cls_zero_mat (n : ℕ) : cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) = 0 := by
  have hidem0 : Mat.IsIdem (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
    show (0 : Matrix (Fin 0) (Fin 0) R) * 0 = 0
    rw [mul_zero]
  have hidemn : Mat.IsIdem (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R) := by
    show (0 : Matrix (Fin n) (Fin n) R) * 0 = 0
    rw [mul_zero]
  have hmvN : Mat.MvN (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
    refine ⟨0, 0, ?_, ?_⟩
    · ext i j; simp
    · ext i j; exact Fin.elim0 i
  have h1 : cls (⟨n, (0 : Matrix (Fin n) (Fin n) R)⟩ : Mat R)
      = cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) :=
    cls_eq_of_mvN hidemn hidem0 hmvN
  have hsum : Mat.sum (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) = ⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      ext i j
      exact Fin.elim0 i
  have h2 : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) = 0 := by
    have h := cls_sum hidem0 hidem0
    rw [hsum] at h
    have hc : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) + (0 : K0 R)
        = cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R)
          + cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) R)⟩ : Mat R) := by
      rw [add_zero]; exact h
    exact (add_left_cancel hc).symm
  rw [h1, h2]

/-- `x` is the difference of the classes of two idempotent matrices of the same size. -/
def K0Good (x : K0 R) : Prop :=
  ∃ (n : ℕ) (P Q : Matrix (Fin n) (Fin n) R), Mat.IsIdem (⟨n, P⟩ : Mat R) ∧
    Mat.IsIdem (⟨n, Q⟩ : Mat R) ∧ x = cls (⟨n, P⟩ : Mat R) - cls (⟨n, Q⟩ : Mat R)

lemma k0Good_zero : K0Good (0 : K0 R) := by
  refine ⟨0, 0, 0, ?_, ?_, ?_⟩
  · show (0 : Matrix (Fin 0) (Fin 0) R) * 0 = 0
    rw [mul_zero]
  · show (0 : Matrix (Fin 0) (Fin 0) R) * 0 = 0
    rw [mul_zero]
  · simp

lemma k0Good_cls_idem {p : Mat R} (hp : p.IsIdem) : K0Good (cls p) := by
  obtain ⟨n, M⟩ := p
  refine ⟨n, M, 0, hp, ?_, ?_⟩
  · show (0 : Matrix (Fin n) (Fin n) R) * 0 = 0
    rw [mul_zero]
  · rw [cls_zero_mat n, sub_zero]

lemma k0Good_neg {x : K0 R} (h : K0Good x) : K0Good (-x) := by
  obtain ⟨n, P, Q, hP, hQ, hx⟩ := h
  refine ⟨n, Q, P, hQ, hP, ?_⟩
  rw [hx]
  abel

lemma k0Good_add {x y : K0 R} (hx : K0Good x) (hy : K0Good y) : K0Good (x + y) := by
  obtain ⟨n, P, Q, hP, hQ, hx⟩ := hx
  obtain ⟨m, P', Q', hP', hQ', hy⟩ := hy
  refine ⟨n + m, (Mat.sum (⟨n, P⟩ : Mat R) (⟨m, P'⟩ : Mat R)).2,
    (Mat.sum (⟨n, Q⟩ : Mat R) (⟨m, Q'⟩ : Mat R)).2, ?_, ?_, ?_⟩
  · exact Mat.sum_idem hP hP'
  · exact Mat.sum_idem hQ hQ'
  · have e1 : cls (⟨n + m, (Mat.sum (⟨n, P⟩ : Mat R) (⟨m, P'⟩ : Mat R)).2⟩ : Mat R)
        = cls (⟨n, P⟩ : Mat R) + cls (⟨m, P'⟩ : Mat R) := cls_sum hP hP'
    have e2 : cls (⟨n + m, (Mat.sum (⟨n, Q⟩ : Mat R) (⟨m, Q'⟩ : Mat R)).2⟩ : Mat R)
        = cls (⟨n, Q⟩ : Mat R) + cls (⟨m, Q'⟩ : Mat R) := cls_sum hQ hQ'
    rw [hx, hy, e1, e2]
    abel

lemma k0Good_mk (w : FreeAbelianGroup (Mat R)) :
    K0Good (QuotientAddGroup.mk' (K0Rel R) w) := by
  induction w using FreeAbelianGroup.induction_on with
  | zero => simpa using k0Good_zero
  | of p =>
      rw [show (QuotientAddGroup.mk' (K0Rel R)) (FreeAbelianGroup.of p) = cls p from rfl]
      by_cases hp : p.IsIdem
      · exact k0Good_cls_idem hp
      · rw [cls_of_not_idem hp]; exact k0Good_zero
  | neg p ih =>
      rw [map_neg]
      exact k0Good_neg ih
  | add p q ihp ihq =>
      rw [map_add]
      exact k0Good_add ihp ihq

end

/-- Every element of `K₀ A` is the difference of the classes of two idempotent square matrices
of the same size. -/
theorem hk_k0_eq_diff (A : Type) [Ring A] (x : K0 A) :
    ∃ (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A), P * P = P ∧ Q * Q = Q ∧
      x = cls (⟨n, P⟩ : Mat A) - cls (⟨n, Q⟩ : Mat A) := by
  change K0Good x
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective x
  rw [← hw]
  exact k0Good_mk w

end Work.KT
