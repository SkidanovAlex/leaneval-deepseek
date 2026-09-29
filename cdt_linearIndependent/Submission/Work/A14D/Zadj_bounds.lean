import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.A14D.Zadj_generic
import Submission.Work.A14D.Zadj_singular

/-!
# Local order bounds for solutions of the adjoint Zagier equation

`LZf β = RhsZ c` with `RhsZ c` having poles of order at most `3` at `x = 0` and `2` at `x = 1`
forces `β` to have poles of order at most `2` at `0` and `1` and to be regular everywhere else:
the operator `LZf = P2Z·∂² + P1Z·∂ + P0Z` has the simple roots `0, 1/9, 1` of `P2Z` as its only
singular points, and at each of them the indicial value (`N²`, `8N²`, `−(8/9)N²` with
`N = ordAt · β < 0`) does not vanish, so `LZf` loses one order there (at a regular point it loses
two, `Zadj_generic`).
-/

open Polynomial
open Commons.FieldTheory.RatFunc

noncomputable section
namespace Work.A14D

theorem Zadj_bounds {β : RatFunc ℂ} (hβ : β ≠ 0) {c : Fin 3 → ℂ}
    (h : LZf β = RhsZ c)
    (hrhs : ∀ α : ℂ, (if α = 0 then (-3 : ℤ) else if α = 1 then (-2 : ℤ) else 0)
      ≤ Commons.FieldTheory.RatFunc.ordAtT α (RhsZ c)) :
    (-2 : ℤ) ≤ Commons.FieldTheory.RatFunc.ordAt 0 β ∧
      (-1 : ℤ) ≤ Commons.FieldTheory.RatFunc.ordAt 1 β ∧
      (∀ α : ℂ, α ≠ 0 → α ≠ 1 → (0 : ℤ) ≤ Commons.FieldTheory.RatFunc.ordAt α β) := by
  have hR : ∀ α : ℂ, ordAtT α (LZf β) = ordAtT α (RhsZ c) := fun α => by rw [h]
  have hcast : ∀ (N : ℤ), N < 0 → ((N : ℤ) : ℂ) ≠ 0 := fun N hN hz => by
    exact (ne_of_lt hN) (Int.cast_eq_zero.mp hz)
  constructor
  · by_contra hcon
    push_neg at hcon
    have hN : ordAt (0 : ℂ) β < 0 := by omega
    have hN0 : ((ordAt (0 : ℂ) β : ℤ) : ℂ) ≠ 0 := hcast _ (by omega)
    have hcoef : (((ordAt (0 : ℂ) β : ℤ) : ℂ)
        * ((((ordAt (0 : ℂ) β : ℤ) : ℂ) - 1) * Zs0.eval 0 + P1Z.eval 0)) ≠ 0 := by
      have heq : (((ordAt (0 : ℂ) β : ℤ) : ℂ)
          * ((((ordAt (0 : ℂ) β : ℤ) : ℂ) - 1) * Zs0.eval 0 + P1Z.eval 0))
          = (((ordAt (0 : ℂ) β : ℤ) : ℂ)) ^ 2 := by
        rw [Zs0_eval_zero, eval_P1Z]; ring
      rw [heq]; exact pow_ne_zero 2 hN0
    have hord := Zadj_singular hβ hN P2Z_eq_X_mul_Zs0 (by rw [Zs0_eval_zero]; norm_num) hcoef
    have hrhs0 : ((-3 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℂ) (RhsZ c) := by
      have h' := hrhs 0
      rwa [if_pos rfl] at h'
    rw [← hR 0, hord] at hrhs0
    have h3 : (-3 : ℤ) ≤ (ordAt (0 : ℂ) β : ℤ) - 1 := WithTop.coe_le_coe.mp hrhs0
    omega
  constructor
  · by_contra hcon
    push_neg at hcon
    have hN : ordAt (1 : ℂ) β < 0 := by omega
    have hN0 : ((ordAt (1 : ℂ) β : ℤ) : ℂ) ≠ 0 := hcast _ (by omega)
    have hcoef : (((ordAt (1 : ℂ) β : ℤ) : ℂ)
        * ((((ordAt (1 : ℂ) β : ℤ) : ℂ) - 1) * Zs1.eval 1 + P1Z.eval 1)) ≠ 0 := by
      have heq : (((ordAt (1 : ℂ) β : ℤ) : ℂ)
          * ((((ordAt (1 : ℂ) β : ℤ) : ℂ) - 1) * Zs1.eval 1 + P1Z.eval 1))
          = 8 * (((ordAt (1 : ℂ) β : ℤ) : ℂ)) ^ 2 := by
        rw [Zs1_eval_one, eval_P2Z_deriv_one]; ring
      rw [heq]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hN0)
    have hord := Zadj_singular hβ hN P2Z_eq_Xsub1_mul_Zs1 (by rw [Zs1_eval_one]; norm_num) hcoef
    have hrhs1 : ((-2 : ℤ) : WithTop ℤ) ≤ ordAtT (1 : ℂ) (RhsZ c) := by
      have h' := hrhs 1
      rwa [if_neg (by norm_num : ¬((1 : ℂ) = 0)), if_pos rfl] at h'
    rw [← hR 1, hord] at hrhs1
    have h3 : (-2 : ℤ) ≤ (ordAt (1 : ℂ) β : ℤ) - 1 := WithTop.coe_le_coe.mp hrhs1
    omega
  · intro α h0 h1
    by_contra hcon
    push_neg at hcon
    have hN : ordAt α β < 0 := hcon
    have hN0 : ((ordAt α β : ℤ) : ℂ) ≠ 0 := hcast _ (by omega)
    have hrhsα : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT α (RhsZ c) := by
      have h' := hrhs α
      rwa [if_neg h0, if_neg h1] at h'
    by_cases h9 : α = (1 : ℂ) / 9
    · subst h9
      have hcoef : (((ordAt ((1 : ℂ) / 9) β : ℤ) : ℂ)
          * ((((ordAt ((1 : ℂ) / 9) β : ℤ) : ℂ) - 1) * Zs9.eval ((1 : ℂ) / 9)
            + P1Z.eval ((1 : ℂ) / 9))) ≠ 0 := by
        have heq : (((ordAt ((1 : ℂ) / 9) β : ℤ) : ℂ)
            * ((((ordAt ((1 : ℂ) / 9) β : ℤ) : ℂ) - 1) * Zs9.eval ((1 : ℂ) / 9)
              + P1Z.eval ((1 : ℂ) / 9))) = (-(8 / 9)) * (((ordAt ((1 : ℂ) / 9) β : ℤ) : ℂ)) ^ 2 := by
          rw [Zs9_eval_ninth, eval_P2Z_deriv_ninth]; ring
        rw [heq]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hN0)
      have hord := Zadj_singular hβ hN P2Z_eq_Xsub9_mul_Zs9 (by rw [Zs9_eval_ninth]; norm_num) hcoef
      rw [← hR ((1 : ℂ) / 9), hord] at hrhsα
      have h3 : (0 : ℤ) ≤ (ordAt ((1 : ℂ) / 9) β : ℤ) - 1 := WithTop.coe_le_coe.mp hrhsα
      omega
    · have hP2 : (P2Z).eval α ≠ 0 := by
        intro hev
        rw [eval_P2Z] at hev
        rcases mul_eq_zero.mp hev with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact h0 h''
          · exact h1 (sub_eq_zero.mp h'').symm
        · have h9a : (9 : ℂ) * α = 1 := by linear_combination -h'
          exact h9 ((eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)).mpr (by linear_combination h9a))
      have hord := Zadj_generic hβ hP2 hN
      rw [← hR α, hord] at hrhsα
      have h3 : (0 : ℤ) ≤ (ordAt α β : ℤ) - 2 := WithTop.coe_le_coe.mp hrhsα
      omega

end Work.A14D
