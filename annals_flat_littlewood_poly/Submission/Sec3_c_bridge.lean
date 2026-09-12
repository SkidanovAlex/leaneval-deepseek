import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs

/-! Bridge between the H-analysis (x-space) and the cosine polynomial `c`
(θ-space), paper arXiv:1907.09464v1 §3:

    H(2Tθ) = scale · (z^T P_t(z) + z^{2T} Q_t(z))      (z = e^{2iθ})
    Re(H(2Tθ)) = scale · c(θ),   i.e.  c(θ) = √(2^(t+1)) · Re(H(2Tθ)).

Here `scale = 1/√(2^(t+1))`.  This lets the interval analysis in `x = 2Tθ`
transfer to `c`. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3BridgeAux

/-! Internal helpers (kept in their own namespace to avoid collisions with the
shared lemmas of other Section-3 modules). -/

/-- `e^{i(a+b)} = e^{ia} e^{ib}`. -/
lemma eθ_add (a b : ℝ) : Sec3.eθ (a + b) = Sec3.eθ a * Sec3.eθ b := by
  unfold Sec3.eθ
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e^{i·n·x} = (e^{ix})^n` for a natural `n`. -/
lemma eθ_nat_mul (n : ℕ) (x : ℝ) : Sec3.eθ ((n : ℝ) * x) = (Sec3.eθ x) ^ n := by
  unfold Sec3.eθ
  calc
    Complex.exp ((((n : ℝ) * x : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((n : ℂ) * ((x : ℂ) * Complex.I)) := by
          congr 1
          push_cast
          ring
    _ = (Complex.exp ((x : ℂ) * Complex.I)) ^ n := by rw [Complex.exp_nat_mul]

/-- `e^{2πi} = 1`. -/
lemma eθ_two_pi : Sec3.eθ (2 * Real.pi) = 1 := by
  unfold Sec3.eθ
  rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = (2 : ℂ) * (Real.pi : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_two_pi_mul_I

/-- `conj (e^{iθ}) = e^{-iθ}`. -/
lemma eθ_neg (θ : ℝ) : star (Sec3.eθ θ) = Sec3.eθ (-θ) := by
  unfold Sec3.eθ
  rw [← starRingEnd_apply]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `T t = 2^(t+10) > 0`. -/
lemma T_pos (t : ℕ) : 0 < Sec3H.T t := by
  unfold Sec3H.T
  positivity

/-- The substitution `x = 2Tθ` makes the `eθ` argument in `α`, `β` equal `2θ`. -/
lemma x_div_T (t : ℕ) (θ : ℝ) : (2 * (Sec3H.T t : ℝ) * θ) / (Sec3H.T t : ℝ) = 2 * θ := by
  field_simp [show (Sec3H.T t : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt (T_pos t))]

/-- `e^{i·2Tθ} = z^T` with `z = e^{2iθ}`. -/
lemma phase1 (t : ℕ) (θ : ℝ) :
    Sec3.eθ (2 * (Sec3H.T t : ℝ) * θ) = (Sec3.zθ θ) ^ Sec3H.T t := by
  unfold Sec3.zθ
  calc
    Sec3.eθ (2 * (Sec3H.T t : ℝ) * θ) = Sec3.eθ ((Sec3H.T t : ℝ) * (2 * θ)) := by
      congr 1
      ring
    _ = (Sec3.eθ (2 * θ)) ^ Sec3H.T t := by rw [eθ_nat_mul]

/-- `e^{i·4Tθ} = z^{2T}` with `z = e^{2iθ}`. -/
lemma phase2 (t : ℕ) (θ : ℝ) :
    Sec3.eθ (2 * (2 * (Sec3H.T t : ℝ) * θ)) = (Sec3.zθ θ) ^ (2 * Sec3H.T t) := by
  unfold Sec3.zθ
  calc
    Sec3.eθ (2 * (2 * (Sec3H.T t : ℝ) * θ)) = Sec3.eθ (((2 * Sec3H.T t : ℕ) : ℝ) * (2 * θ)) := by
      congr 1
      norm_num [Nat.cast_mul]
      ring
    _ = (Sec3.eθ (2 * θ)) ^ (2 * Sec3H.T t) := by rw [eθ_nat_mul]

/-- `α` at the substitution point. -/
lemma alpha_at_x (t : ℕ) (θ : ℝ) :
    Sec3H.alpha t (2 * (Sec3H.T t : ℝ) * θ) = (Sec3H.scale t : ℂ) * (RudinShapiro.P t).eval (Sec3.zθ θ) := by
  unfold Sec3H.alpha Sec3.zθ
  rw [x_div_T]

/-- `β` at the substitution point. -/
lemma beta_at_x (t : ℕ) (θ : ℝ) :
    Sec3H.beta t (2 * (Sec3H.T t : ℝ) * θ) = (Sec3H.scale t : ℂ) * (RudinShapiro.Q t).eval (Sec3.zθ θ) := by
  unfold Sec3H.beta Sec3.zθ
  rw [x_div_T]

/-- `z(θ+π) = z(θ)` because `z = e^{2iθ}` has period `π`. -/
lemma zθ_add_pi (θ : ℝ) : Sec3.zθ (θ + Real.pi) = Sec3.zθ θ := by
  unfold Sec3.zθ
  calc
    Sec3.eθ (2 * (θ + Real.pi)) = Sec3.eθ (2 * θ + 2 * Real.pi) := by congr 1; ring
    _ = Sec3.eθ (2 * θ) * Sec3.eθ (2 * Real.pi) := eθ_add _ _
    _ = Sec3.eθ (2 * θ) := by rw [eθ_two_pi]; ring

/-- `z(−θ) = conj z(θ)` for `z = e^{2iθ}` (unit modulus). -/
lemma zθ_neg (θ : ℝ) : Sec3.zθ (-θ) = star (Sec3.zθ θ) := by
  unfold Sec3.zθ
  calc
    Sec3.eθ (2 * (-θ)) = Sec3.eθ (-(2 * θ)) := by congr 1; ring
    _ = star (Sec3.eθ (2 * θ)) := by rw [eθ_neg]

/-- Conjugation commutes with evaluation of the Rudin-Shapiro polynomials. -/
lemma star_eval_PQ (t : ℕ) (z : ℂ) :
    starRingEnd ℂ ((RudinShapiro.P t).eval z) = (RudinShapiro.P t).eval (starRingEnd ℂ z) ∧
    starRingEnd ℂ ((RudinShapiro.Q t).eval z) = (RudinShapiro.Q t).eval (starRingEnd ℂ z) := by
  induction t with
  | zero => simp
  | succ t ih =>
      constructor
      · rw [RudinShapiro.eval_P_succ]
        rw [map_add, map_mul, map_pow]
        rw [ih.1, ih.2]
        rw [RudinShapiro.eval_P_succ]
      · rw [RudinShapiro.eval_Q_succ]
        rw [map_sub, map_mul, map_pow]
        rw [ih.1, ih.2]
        rw [RudinShapiro.eval_Q_succ]

/-- `F`-form of `cval`: `cval t θ = F (zθ θ)` with
`F z = z^A P_t(z) + z^{2A} Q_t(z)`, `A = 2^(t+10)`. -/
def cvalF (t : ℕ) (z : ℂ) : ℂ :=
  (z ^ 2 ^ (t + 10)) * (RudinShapiro.P t).eval z +
    (z ^ (2 * 2 ^ (t + 10))) * (RudinShapiro.Q t).eval z

/-- `F(conj z) = conj (F z)` for the Rudin-Shapiro combination. -/
lemma cvalF_conj (t : ℕ) (z : ℂ) : cvalF t (star z) = star (cvalF t z) := by
  rw [← starRingEnd_apply, ← starRingEnd_apply]
  unfold cvalF
  rw [map_add, map_mul, map_mul, map_pow, map_pow]
  rw [(star_eval_PQ t z).1, (star_eval_PQ t z).2]

/-- `cval` has period `π` (all frequencies in `c` are even). -/
lemma cval_add_pi (t : ℕ) (θ : ℝ) : Sec3.cval t (θ + Real.pi) = Sec3.cval t θ := by
  have hcval (θ' : ℝ) : Sec3.cval t θ' = cvalF t (Sec3.zθ θ') := by
    simp [Sec3.cval, cvalF]
  calc
    Sec3.cval t (θ + Real.pi) = cvalF t (Sec3.zθ (θ + Real.pi)) := hcval (θ + Real.pi)
    _ = cvalF t (Sec3.zθ θ) := by rw [zθ_add_pi]
    _ = Sec3.cval t θ := (hcval θ).symm

/-- `cval(−θ) = conj (cval θ)`. -/
lemma cval_neg (t : ℕ) (θ : ℝ) : Sec3.cval t (-θ) = star (Sec3.cval t θ) := by
  have hcval (θ' : ℝ) : Sec3.cval t θ' = cvalF t (Sec3.zθ θ') := by
    simp [Sec3.cval, cvalF]
  calc
    Sec3.cval t (-θ) = cvalF t (Sec3.zθ (-θ)) := hcval (-θ)
    _ = cvalF t (star (Sec3.zθ θ)) := by rw [zθ_neg]
    _ = star (cvalF t (Sec3.zθ θ)) := cvalF_conj t (Sec3.zθ θ)
    _ = star (Sec3.cval t θ) := by rw [hcval θ]

end Sec3BridgeAux

namespace Sec3H

/-- `H(2Tθ) = scale · cval(θ)` (complex identity). -/
lemma H_two_T_mul_eq_cval (t : ℕ) (θ : ℝ) :
    H t (2 * (T t : ℝ) * θ) = (scale t : ℂ) * Sec3.cval t θ := by
  unfold H
  rw [Sec3BridgeAux.alpha_at_x, Sec3BridgeAux.beta_at_x]
  rw [Sec3BridgeAux.phase1, Sec3BridgeAux.phase2]
  unfold Sec3.cval Sec3.zθ T
  ring

/-- `Re(H(2Tθ)) = scale · c(θ)`. -/
lemma H_re_two_T_mul (t : ℕ) (θ : ℝ) :
    (H t (2 * (T t : ℝ) * θ)).re = (scale t : ℝ) * Sec3.c t θ := by
  rw [H_two_T_mul_eq_cval]
  unfold Sec3.c
  rw [Complex.re_ofReal_mul]

/-- `c(θ) = √(2^(t+1)) · Re(H(2Tθ))`. -/
lemma c_eq_sqrt_re_H (t : ℕ) (θ : ℝ) :
    Sec3.c t θ = Real.sqrt (2 ^ (t + 1) : ℝ) * (H t (2 * (T t : ℝ) * θ)).re := by
  rw [H_re_two_T_mul]
  unfold scale
  rw [← mul_assoc]
  have hpos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by
    exact Real.sqrt_pos.2 (by positivity)
  rw [mul_inv_cancel₀ hpos.ne']
  simp

/-- Symmetry `c(θ + π) = c(θ)`. -/
lemma c_add_pi (t : ℕ) (θ : ℝ) : Sec3.c t (θ + Real.pi) = Sec3.c t θ := by
  unfold Sec3.c
  rw [Sec3BridgeAux.cval_add_pi t θ]

/-- Symmetry `c(−θ) = c(θ)`. -/
lemma c_neg (t : ℕ) (θ : ℝ) : Sec3.c t (-θ) = Sec3.c t θ := by
  unfold Sec3.c
  rw [Sec3BridgeAux.cval_neg]
  rw [← starRingEnd_apply]
  exact Complex.conj_re (Sec3.cval t θ)

/-- Symmetry `c(π − θ) = c(θ)`. -/
lemma c_pi_sub (t : ℕ) (θ : ℝ) : Sec3.c t (Real.pi - θ) = Sec3.c t θ := by
  have h : Real.pi - θ = -θ + Real.pi := by ring
  rw [h]
  rw [c_add_pi, c_neg]

/-- `c` is `2π`-periodic. -/
lemma c_periodic (t : ℕ) (θ : ℝ) : Sec3.c t (θ + 2 * Real.pi) = Sec3.c t θ := by
  have h : θ + 2 * Real.pi = (θ + Real.pi) + Real.pi := by ring
  rw [h]
  rw [c_add_pi, c_add_pi]

/-- Global upper bound `|c(θ)| ≤ C·√(2^(t+1))` with `C = 1`
(immediate from the RS norm bounds; the constant is loose). -/
lemma c_abs_bound (t : ℕ) (θ : ℝ) :
    |Sec3.c t θ| ≤ Real.sqrt (2 ^ (t + 1) : ℝ) + Real.sqrt (2 ^ (t + 1) : ℝ) :=
  Sec3.abs_c_le t θ

end Sec3H
end Submission
