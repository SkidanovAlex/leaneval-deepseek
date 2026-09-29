import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Solutions.iterC_qpow

/-!
# The polynomial excess rate at the multiples of the period

For a rational frequency `α = p/q` the `q`-step transfer matrix `A_q(x) = iterC α λ E q x` is
the *period* of the cocycle: `A_{mq}(x) = A_q(x)^m` (`iterC_qpow`).  The Lyapunov exponent is
the phase average of `log ρ(A_q(x))` (`lyap_periodic`), while the finite scale average at
`N = mq` is the average of `(1/(mq)) log ‖A_q(x)^m‖_F`.  Because a real `SL₂` matrix has
`ρ ≥ 1` and `‖A^m‖` grows at most like `m ρ^m` (Chebyshev: `A^m = U_{m-1}(τ/2)A - U_{m-2}(τ/2)`,
combined with the sharp bound `|U_k(τ/2)| ≤ (k+1)ρ^{k+1}`), the excess
`lyapAvg (mq) - lyap` is `O(log(mq)/(mq))`.

This is the quantitative input of the rational case of `prop9_main`; it is stated (and proved)
here in the exact form requested by `Scale/rational_case.rat_defect_of_rate`.
-/

set_option maxHeartbeats 1000000

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.Frobenius
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

open Work.TMC7Core


/-! ## Cayley--Hamilton for `2 × 2` matrices and the Chebyshev formula for powers -/

theorem two_by_two_CH (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 = A.trace • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two, Fin.sum_univ_two]
      <;> ring

theorem sl2_pow_eq_chebU_real (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (k : ℕ) :
    A ^ k = (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (A.trace / 2) • A
      - (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 2)).eval (A.trace / 2) • 1 := by
  have hCH : A ^ 2 = A.trace • A - 1 := by rw [two_by_two_CH, hdet]; simp
  have hrec : ∀ n : ℤ,
      (Polynomial.Chebyshev.U ℝ n).eval (A.trace / 2)
        = A.trace * (Polynomial.Chebyshev.U ℝ (n - 1)).eval (A.trace / 2)
          - (Polynomial.Chebyshev.U ℝ (n - 2)).eval (A.trace / 2) := by
    intro n
    have h := congrArg (fun p : Polynomial ℝ => p.eval (A.trace / 2))
      (Polynomial.Chebyshev.U_eq ℝ n)
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] at h
    have h2 : (2 : ℝ) * (A.trace / 2)
        * Polynomial.eval (A.trace / 2) (Polynomial.Chebyshev.U ℝ (n - 1))
        = A.trace * Polynomial.eval (A.trace / 2) (Polynomial.Chebyshev.U ℝ (n - 1)) := by ring
    rw [h2] at h
    exact h
  induction k with
  | zero =>
    have h1 : (((0 : ℕ) : ℤ) - 1) = (-1 : ℤ) := by norm_num
    have h2 : (((0 : ℕ) : ℤ) - 2) = (-2 : ℤ) := by norm_num
    rw [h1, h2, Polynomial.Chebyshev.U_neg_one, Polynomial.Chebyshev.U_neg_two]
    simp
  | succ k ih =>
    have h1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by omega
    have h2 : (((k + 1 : ℕ) : ℤ) - 2) = (k : ℤ) - 1 := by omega
    rw [h1, h2]
    rw [pow_succ', ih, mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    rw [show A * A = A ^ 2 from (pow_two A).symm, hCH]
    rw [smul_sub, smul_smul, sub_right_comm, ← sub_smul]
    rw [mul_comm (Polynomial.eval (A.trace / 2) (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1))) A.trace,
      ← hrec (k : ℤ)]

/-! ## Elementary inequalities -/
lemma abs_add_le' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le x, neg_abs_le y, le_abs_self x, le_abs_self y]

/-! ## elementary bounds -/

lemma abs_sin_nat_mul_le' (θ : ℝ) (n : ℕ) :
    |Real.sin ((n : ℝ) * θ)| ≤ (n : ℝ) * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, add_mul, one_mul, Real.sin_add]
    calc |Real.sin ((n : ℝ) * θ) * Real.cos θ + Real.cos ((n : ℝ) * θ) * Real.sin θ|
        ≤ |Real.sin ((n : ℝ) * θ) * Real.cos θ| + |Real.cos ((n : ℝ) * θ) * Real.sin θ| :=
          abs_add_le' _ _
      _ = |Real.sin ((n : ℝ) * θ)| * |Real.cos θ| + |Real.cos ((n : ℝ) * θ)| * |Real.sin θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ (n : ℝ) * |Real.sin θ| + |Real.sin θ| := by
          refine add_le_add ?_ ?_
          · calc |Real.sin ((n : ℝ) * θ)| * |Real.cos θ|
                ≤ ((n : ℝ) * |Real.sin θ|) * 1 :=
                  mul_le_mul ih (Real.abs_cos_le_one θ) (abs_nonneg _) (by positivity)
              _ = (n : ℝ) * |Real.sin θ| := by ring
          · calc |Real.cos ((n : ℝ) * θ)| * |Real.sin θ| ≤ 1 * |Real.sin θ| :=
                  mul_le_mul (Real.abs_cos_le_one _) le_rfl (abs_nonneg _) (by norm_num)
              _ = |Real.sin θ| := one_mul _
      _ = ((n : ℝ) + 1) * |Real.sin θ| := by ring

lemma cosh_le_exp' (y : ℝ) (hy : 0 ≤ y) : Real.cosh y ≤ Real.exp y := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma sinh_mul_le' (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    Real.sinh ((k:ℝ) * θ) ≤ (k:ℝ) * Real.exp (((k:ℝ) - 1) * θ) * Real.sinh θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : (((k+1:ℕ)) : ℝ) * θ = (k:ℝ)*θ + θ := by push_cast; ring
    rw [hk1, Real.sinh_add]
    have hcoshθ : (0:ℝ) ≤ Real.cosh θ := le_of_lt (Real.cosh_pos θ)
    have hsinhθ : (0:ℝ) ≤ Real.sinh θ := Real.sinh_nonneg_iff.mpr hθ
    have hkθ : (0:ℝ) ≤ (k:ℝ)*θ := by positivity
    have hX : (0:ℝ) ≤ (k:ℝ) * Real.exp (((k:ℝ)-1)*θ) * Real.sinh θ := by positivity
    have h1 : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [h1]
    rw [show ((k:ℝ) + 1 - 1) * θ = (k:ℝ) * θ by ring]
    have hexp : Real.exp (((k:ℝ)-1)*θ) * Real.exp θ = Real.exp ((k:ℝ)*θ) := by
      rw [← Real.exp_add]; congr 1; ring
    have he : (k:ℝ) * Real.exp (((k:ℝ)-1)*θ) * Real.sinh θ * Real.exp θ
        = (k:ℝ) * Real.exp ((k:ℝ)*θ) * Real.sinh θ := by
      calc (k:ℝ) * Real.exp (((k:ℝ)-1)*θ) * Real.sinh θ * Real.exp θ
          = (k:ℝ) * Real.sinh θ * (Real.exp (((k:ℝ)-1)*θ) * Real.exp θ) := by ring
        _ = (k:ℝ) * Real.sinh θ * Real.exp ((k:ℝ)*θ) := by rw [hexp]
        _ = (k:ℝ) * Real.exp ((k:ℝ)*θ) * Real.sinh θ := by ring
    calc Real.sinh ((k:ℝ)*θ) * Real.cosh θ + Real.cosh ((k:ℝ)*θ) * Real.sinh θ
        ≤ (k:ℝ) * Real.exp (((k:ℝ)-1)*θ) * Real.sinh θ * Real.cosh θ
            + Real.exp ((k:ℝ)*θ) * Real.sinh θ := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right ih hcoshθ
          · exact mul_le_mul_of_nonneg_right (cosh_le_exp' _ hkθ) hsinhθ
      _ ≤ (k:ℝ) * Real.exp (((k:ℝ)-1)*θ) * Real.sinh θ * Real.exp θ
            + Real.exp ((k:ℝ)*θ) * Real.sinh θ := by
          refine add_le_add ?_ le_rfl
          exact mul_le_mul_of_nonneg_left (cosh_le_exp' θ hθ) hX
      _ = ((k:ℝ) + 1) * Real.exp ((k:ℝ)*θ) * Real.sinh θ := by rw [he]; ring

/-! ## the elliptic case -/

lemma chebU_abs_le_one (x : ℝ) (hx : |x| ≤ 1) (m : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x| ≤ (m : ℝ) + 1 := by
  have hx1 : -1 ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ 1 := (abs_le.mp hx).2
  rcases lt_or_eq_of_le hx1 with hgt | heq
  · rcases lt_or_eq_of_le hx2 with hlt | heq2
    · -- -1 < x < 1
      set θ : ℝ := Real.arccos x with hθdef
      have hcos : Real.cos θ = x := Real.cos_arccos hx1 hx2
      have hsin : Real.sin θ = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
      have hsq : x ^ 2 < 1 := by nlinarith
      have hsinpos : 0 < Real.sin θ := by
        rw [hsin]; exact Real.sqrt_pos.mpr (by linarith)
      have hkey := Polynomial.Chebyshev.U_real_cos θ (m : ℤ)
      rw [hcos] at hkey
      have hcast : ((↑(m:ℤ) : ℝ) + 1) = (m:ℝ) + 1 := by push_cast; ring
      rw [hcast] at hkey
      have hb := abs_sin_nat_mul_le' θ (m+1)
      have hcast2 : (((m+1:ℕ)) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
      rw [hcast2] at hb
      have h1 : |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x| * Real.sin θ
          = |Real.sin (((m:ℝ)+1) * θ)| := by
        rw [← abs_of_pos hsinpos, ← abs_mul, hkey]
      have h3 : |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x| * Real.sin θ
          ≤ ((m:ℝ) + 1) * Real.sin θ := by
        rw [h1]
        rwa [abs_of_pos hsinpos] at hb
      exact le_of_mul_le_mul_right h3 hsinpos
    · -- x = 1
      rw [heq2, Polynomial.Chebyshev.U_eval_one]
      have hcast : ((↑(m:ℤ) : ℝ) + 1) = (m:ℝ) + 1 := by push_cast; ring
      rw [hcast, abs_of_nonneg (by positivity)]
  · -- x = -1
    rw [← heq, Polynomial.Chebyshev.U_eval_neg_one]
    have h1 : |(((m:ℤ).negOnePow : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, Int.abs_negOnePow]; norm_num
    rw [abs_mul, h1, one_mul]
    have hcast : ((↑(m:ℤ) : ℝ) + 1) = (m:ℝ) + 1 := by push_cast; ring
    rw [hcast, abs_of_nonneg (by positivity)]



/-! ## the hyperbolic case -/

lemma chebU_abs_le_cosh (x : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x|
      ≤ ((m : ℝ) + 1) * (x + Real.sqrt (x ^ 2 - 1)) ^ m := by
  rcases eq_or_lt_of_le hx with hx1 | hx1
  · rw [← hx1, Polynomial.Chebyshev.U_eval_one]
    have h1 : ((↑(m:ℤ) : ℝ) + 1) = (m:ℝ)+1 := by push_cast; ring
    rw [h1, abs_of_nonneg (by positivity)]
    rw [show (1:ℝ) + Real.sqrt (1 ^ 2 - 1) = 1 by norm_num, one_pow, mul_one]
  · set θ : ℝ := Real.arcosh x with hθdef
    have hθnn : 0 ≤ θ := le_of_lt (Real.arcosh_pos hx1)
    have hcosh : Real.cosh θ = x := Real.cosh_arcosh hx
    have hsinhpos : 0 < Real.sinh θ := by
      rw [Real.sinh_arcosh hx]
      exact Real.sqrt_pos.mpr (by nlinarith)
    have hexp : Real.exp θ = x + Real.sqrt (x ^ 2 - 1) := Real.exp_arcosh hx
    have hkey := Polynomial.Chebyshev.U_real_cosh θ (m : ℤ)
    rw [hcosh] at hkey
    have hcast : ((↑(m:ℤ) : ℝ) + 1) = (m:ℝ) + 1 := by push_cast; ring
    rw [hcast] at hkey
    have hb2 : Real.sinh (((m:ℝ)+1) * θ) ≤ ((m:ℝ)+1) * Real.exp ((m:ℝ)*θ) * Real.sinh θ := by
      have h := sinh_mul_le' θ hθnn (m+1)
      rw [show (((m+1:ℕ)):ℝ) = (m:ℝ)+1 by push_cast; ring] at h
      rw [show (((m:ℝ)+1) - 1)*θ = (m:ℝ)*θ by ring] at h
      exact h
    have h1 : |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x| * Real.sinh θ
        = |Real.sinh (((m:ℝ)+1) * θ)| := by
      rw [← abs_of_pos hsinhpos, ← abs_mul, hkey]
    have h4 : |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x| ≤ ((m:ℝ)+1) * Real.exp ((m:ℝ)*θ) := by
      refine le_of_mul_le_mul_right ?_ hsinhpos
      rw [h1, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
      exact hb2
    rw [show Real.exp ((m:ℝ)*θ) = (x + Real.sqrt (x^2 - 1))^m by
      rw [Real.exp_nat_mul, hexp]] at h4
    exact h4

/-! ## `rhoSL` in the two regimes -/

lemma rhoSL_eq_one_of_abs_le (τ : ℝ) (h : |τ| ≤ 2) : rhoSL τ = 1 := by
  rw [rhoSL]
  split_ifs with h2
  · have hτ2 : |τ| = 2 := le_antisymm h h2
    have hsq : τ ^ 2 = 4 := by
      have := sq_abs τ
      rw [hτ2] at this
      linarith
    rw [show τ ^ 2 - 4 = 0 by linarith, Real.sqrt_zero, hτ2]
    norm_num
  · rfl

lemma rhoSL_eq_of_two_lt_abs (τ : ℝ) (h : 2 < |τ|) :
    rhoSL τ = (|τ| + Real.sqrt (τ ^ 2 - 4)) / 2 := by
  rw [rhoSL, if_pos (le_of_lt h)]

/-! ## the main Chebyshev bound -/

theorem chebU_abs_le_rhoSL (τ : ℝ) (m : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval (τ / 2)| ≤ ((m : ℝ) + 1) * (rhoSL τ) ^ (m + 1) := by
  set x : ℝ := τ / 2 with hx
  have hτ2 : τ = 2 * x := by rw [hx]; ring
  rcases le_or_gt |x| 1 with hle | hlt
  · have hτ : |τ| ≤ 2 := by
      rw [hτ2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    rw [rhoSL_eq_one_of_abs_le τ hτ, one_pow, mul_one]
    exact chebU_abs_le_one x hle m
  · have hτ : 2 < |τ| := by
      rw [hτ2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    rw [rhoSL_eq_of_two_lt_abs τ hτ]
    have hU : |(Polynomial.Chebyshev.U ℝ (m : ℤ)).eval x|
        ≤ ((m : ℝ) + 1) * (|x| + Real.sqrt (|x| ^ 2 - 1)) ^ m := by
      rcases le_or_gt 0 x with hx0 | hx0
      · have hx1 : 1 ≤ x := by
          rw [abs_of_nonneg hx0] at hlt
          exact le_of_lt hlt
        rw [abs_of_nonneg hx0]
        exact chebU_abs_le_cosh x hx1 m
      · have hx1 : 1 ≤ -x := by
          rw [abs_of_neg hx0] at hlt
          exact le_of_lt hlt
        have hneg := Polynomial.Chebyshev.U_eval_neg ℝ m x
        have h1 : |(((m:ℤ).negOnePow : ℤ) : ℝ)| = 1 := by
          rw [← Int.cast_abs, Int.abs_negOnePow]; norm_num
        have hnegeq : |(Polynomial.Chebyshev.U ℝ (m:ℤ)).eval (-x)|
            = |(Polynomial.Chebyshev.U ℝ (m:ℤ)).eval x| := by
          rw [hneg, abs_mul, h1, one_mul]
        rw [abs_of_neg hx0, ← hnegeq]
        exact chebU_abs_le_cosh (-x) hx1 m
    have hρ : (|τ| + Real.sqrt (τ ^ 2 - 4)) / 2 = |x| + Real.sqrt (|x| ^ 2 - 1) := by
      have h1 : |τ| = 2 * |x| := by
        rw [hτ2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have h2 : τ ^ 2 - 4 = 4 * (|x| ^ 2 - 1) := by rw [hτ2, sq_abs]; ring
      have h3 : Real.sqrt (4 * (|x| ^ 2 - 1)) = 2 * Real.sqrt (|x| ^ 2 - 1) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
      rw [h1, h2, h3]; ring
    rw [hρ]
    refine le_trans hU ?_
    have hρ1 : 1 ≤ |x| + Real.sqrt (|x| ^ 2 - 1) := by
      have := Real.sqrt_nonneg (|x| ^ 2 - 1); linarith
    calc ((m : ℝ) + 1) * (|x| + Real.sqrt (|x| ^ 2 - 1)) ^ m
        ≤ ((m : ℝ) + 1) * (|x| + Real.sqrt (|x| ^ 2 - 1)) ^ (m + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_right₀ hρ1 (Nat.le_succ m)


theorem frob_neg' (M : Matrix (Fin 2) (Fin 2) ℂ) : frob (-M) = frob M := by
  rw [Cocycle.frob_eq_norm, Cocycle.frob_eq_norm, norm_neg]

theorem frob_sub_le' (M N : Matrix (Fin 2) (Fin 2) ℂ) : frob (M - N) ≤ frob M + frob N := by
  have h := Cocycle.frob_add_le M (-N)
  simpa [sub_eq_add_neg, frob_neg'] using h

theorem frob_smul' (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : frob (c • M) = ‖c‖ * frob M := by
  rw [Cocycle.frob_eq_norm, Cocycle.frob_eq_norm, norm_smul]

theorem frob_smul_real' (x : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : frob (x • M) = |x| * frob M := by
  rw [Cocycle.frob_eq_norm, Cocycle.frob_eq_norm, norm_smul, Real.norm_eq_abs]

theorem norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simp

/-! ## trace and determinant through `Complex.ofRealHom` -/

theorem trace_map_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ((A.map Complex.ofRealHom).trace).re = A.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [Matrix.map_apply]

theorem det_map_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (A.map Complex.ofRealHom).det = (A.det : ℂ) := by
  have hc : ∀ x : ℝ, Complex.ofRealHom x = (x : ℂ) := fun x => rfl
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, hc]
  push_cast
  ring

/-! ## The power bound for a complexified real `SL₂` matrix -/

theorem frob_pow_le_map (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) (hm : 1 ≤ m) :
    frob ((A.map Complex.ofRealHom) ^ m)
      ≤ (m : ℝ) * (frob (A.map Complex.ofRealHom) + Real.sqrt 2) * (rhoSL A.trace) ^ m := by
  set u₁ : ℝ := (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1)).eval (A.trace / 2) with hu₁
  set u₂ : ℝ := (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 2)).eval (A.trace / 2) with hu₂
  have hmap : (A.map Complex.ofRealHom) ^ m
      = u₁ • (A.map Complex.ofRealHom)
        - u₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← Matrix.map_pow A Complex.ofRealHom m]
    rw [sl2_pow_eq_chebU_real A hdet m, ← hu₁, ← hu₂]
    rw [Matrix.map_sub Complex.ofRealHom (fun a b => map_sub _ _ _),
      Matrix.map_smul Complex.ofRealHom u₁ (fun a => map_mul _ _ _),
      Matrix.map_smul Complex.ofRealHom u₂ (fun a => map_mul _ _ _),
      Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)]
  have hbnd1 : |u₁| ≤ (m : ℝ) * (rhoSL A.trace) ^ m := by
    have h := chebU_abs_le_rhoSL A.trace (m - 1)
    have e1 : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
    have e2 : (((m - 1 : ℕ)) : ℝ) + 1 = (m : ℝ) := by
      rw [Nat.cast_sub hm]; ring
    have e3 : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel hm
    rw [e2, e3, e1] at h
    rw [hu₁]
    exact h
  have hbnd2 : |u₂| ≤ (m : ℝ) * (rhoSL A.trace) ^ m := by
    have hρ1 : 1 ≤ rhoSL A.trace := rhoSL_one_le _
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      subst hm1
      have h0 : (Polynomial.Chebyshev.U ℝ (((1 : ℕ) : ℤ) - 2)).eval (A.trace / 2) = 0 := by
        have e : (((1 : ℕ) : ℤ) - 2) = (-1 : ℤ) := by norm_num
        rw [e, Polynomial.Chebyshev.U_neg_one]
        simp
      rw [hu₂, h0, abs_zero]
      positivity
    · have h := chebU_abs_le_rhoSL A.trace (m - 2)
      have e1 : (((m - 2 : ℕ)) : ℤ) = (m : ℤ) - 2 := by omega
      have e2 : (((m - 2 : ℕ)) : ℝ) + 1 = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 2 ≤ m)]; ring
      have e3 : (m - 2 : ℕ) + 1 = m - 1 := by omega
      rw [e2, e3, e1] at h
      rw [hu₂]
      have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have hc1 : ((m : ℝ) - 1) * (rhoSL A.trace) ^ (m - 1) ≤ (m : ℝ) * (rhoSL A.trace) ^ (m - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hc2 : (m : ℝ) * (rhoSL A.trace) ^ (m - 1) ≤ (m : ℝ) * (rhoSL A.trace) ^ m := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_right₀ hρ1 (by omega : m - 1 ≤ m)
      exact le_trans h (le_trans hc1 hc2)
  calc frob ((A.map Complex.ofRealHom) ^ m)
      = frob (u₁ • (A.map Complex.ofRealHom)
          - u₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [hmap]
    _ ≤ frob (u₁ • (A.map Complex.ofRealHom))
          + frob (u₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := frob_sub_le' _ _
    _ = |u₁| * frob (A.map Complex.ofRealHom) + |u₂| * Real.sqrt 2 := by
        rw [frob_smul_real', frob_smul_real', frob_one]
    _ ≤ (m : ℝ) * (rhoSL A.trace) ^ m * frob (A.map Complex.ofRealHom)
          + (m : ℝ) * (rhoSL A.trace) ^ m * Real.sqrt 2 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right hbnd1 (frob_nonneg _)
        · exact mul_le_mul_of_nonneg_right hbnd2 (Real.sqrt_nonneg 2)
    _ = (m : ℝ) * (frob (A.map Complex.ofRealHom) + Real.sqrt 2) * (rhoSL A.trace) ^ m := by ring

/-! ## Continuity of the `log rhoSL` integrand -/

theorem continuous_rhoSL' : Continuous rhoSL := by
  have h : rhoSL = fun τ : ℝ => if (2 : ℝ) ≤ |τ| then (|τ| + Real.sqrt (τ ^ 2 - 4)) / 2 else 1 := rfl
  rw [h]
  refine Continuous.if_le (f := fun _ : ℝ => (2 : ℝ)) (g := fun τ : ℝ => |τ|)
    (f' := fun τ : ℝ => (|τ| + Real.sqrt (τ ^ 2 - 4)) / 2) (g' := fun _ : ℝ => (1 : ℝ))
    ?_ continuous_const continuous_const continuous_abs ?_
  · fun_prop
  · intro τ hτ
    have h2 : |τ| = 2 := hτ.symm
    have hsq : τ ^ 2 - 4 = 0 := by
      have := sq_abs τ
      rw [h2] at this
      nlinarith
    rw [hsq, Real.sqrt_zero, h2]
    norm_num

theorem continuous_log_rhoSL' : Continuous fun τ : ℝ => Real.log (rhoSL τ) :=
  continuous_rhoSL'.log (fun τ => ne_of_gt (lt_of_lt_of_le one_pos (rhoSL_one_le τ)))

theorem continuous_log_rhoSL_iterC' (α lam : ℝ) (E : ℂ) (q : ℕ) :
    Continuous fun x : ℝ => Real.log (rhoSL ((iterC α lam E q x).trace).re) := by
  have h00 : Continuous fun x : ℝ => iterC α lam E q x 0 0 :=
    (continuous_apply (0 : Fin 2)).comp
      ((continuous_apply (0 : Fin 2)).comp (continuous_iterC α lam E q))
  have h11 : Continuous fun x : ℝ => iterC α lam E q x 1 1 :=
    (continuous_apply (1 : Fin 2)).comp
      ((continuous_apply (1 : Fin 2)).comp (continuous_iterC α lam E q))
  have htr : Continuous fun x : ℝ => ((iterC α lam E q x).trace).re := by
    have h : Continuous fun x : ℝ => (iterC α lam E q x).trace := by
      have : (fun x : ℝ => (iterC α lam E q x).trace)
          = fun x => iterC α lam E q x 0 0 + iterC α lam E q x 1 1 := by
        funext x; rw [Matrix.trace_fin_two]
      rw [this]; exact h00.add h11
    exact Complex.continuous_re.comp h
  exact continuous_log_rhoSL'.comp htr

/-! ## The pointwise bound for the iterate at a multiple of the period -/

theorem log_iterC_mul_qpow_le (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (x : ℝ) :
    Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x))
      ≤ (m : ℝ) * Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)
        + (Real.log (m : ℝ)
            + Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2)) := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x with hA
  set Ar : Matrix (Fin 2) (Fin 2) ℝ := Solutions.iterR ((p : ℝ) / (q : ℝ)) lam E q x with hAr
  have hpow : iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x = A ^ m := by
    rw [show m * q = q * m from Nat.mul_comm m q, hA]
    exact Solutions.iterC_qpow p q hq lam E m x
  have hmap : Ar.map Complex.ofRealHom = A := by
    rw [hAr, hA]
    exact (Solutions.iterC_eq_map ((p : ℝ) / (q : ℝ)) lam E q x).symm
  have hdet : Ar.det = 1 := by
    have h := det_map_two Ar
    rw [hmap] at h
    have h2 : (Ar.det : ℂ) = 1 := by
      rw [← h]
      exact det_iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x
    exact_mod_cast h2
  have hb := frob_pow_le_map Ar hdet m hm
  rw [← trace_map_two Ar] at hb
  rw [hmap] at hb
  have hpos : 0 < frob (A ^ m) := by
    refine lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
      (Cocycle.frob_sqrt_two_le_of_det_one ?_)
    rw [Matrix.det_pow, hA, det_iterC]
    norm_num
  rw [hpow]
  have h1 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h2 : frob A + Real.sqrt 2 ≠ 0 := by
    have h := frob_nonneg A
    have h' := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith
  have h3 : rhoSL (A.trace).re ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (rhoSL_one_le _))
  have hlog : Real.log ((m : ℝ) * (frob A + Real.sqrt 2) * (rhoSL (A.trace).re) ^ m)
      = Real.log (m : ℝ) + Real.log (frob A + Real.sqrt 2)
        + (m : ℝ) * Real.log (rhoSL (A.trace).re) := by
    rw [Real.log_mul (mul_ne_zero h1 h2) (pow_ne_zero m h3),
      Real.log_mul h1 h2, Real.log_pow]
  have hmain : Real.log (frob (A ^ m)) ≤ (m : ℝ) * Real.log (rhoSL (A.trace).re)
      + (Real.log (m : ℝ) + Real.log (frob A + Real.sqrt 2)) := by
    have hle := Real.log_le_log hpos hb
    rw [hlog] at hle
    linarith
  exact hmain


/-! ## The main theorem (assembly) -/

theorem rat_excess_decay_of_hyperbolic (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (E : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m →
      lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) - lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
        ≤ K * (1 + Real.log ((m : ℝ) * (q : ℝ))) / ((m : ℝ) * (q : ℝ)) := by
  set I₀ : ℝ := ∫ x in (0 : ℝ)..1,
    Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2) with hI₀
  refine ⟨|I₀| + 1, by positivity, ?_⟩
  intro m hm
  -- continuity of the three integrands
  have hc1 : Continuous fun x : ℝ =>
      Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)) :=
    Lyap.continuous_log_frob_iterC _ _ _ _
  have hc2 : Continuous fun x : ℝ =>
      Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re) :=
    continuous_log_rhoSL_iterC' _ _ _ _
  have hc3 : Continuous fun x : ℝ =>
      Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2) := by
    have hc : Continuous fun x : ℝ => frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) :=
      Lyap.continuous_frob.comp (continuous_iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q)
    refine (hc.add continuous_const).log (fun x => ?_)
    have h : (0 : ℝ) < frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2 := by
      have h1 := frob_nonneg (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x)
      have h2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
      linarith
    simpa only [Pi.add_apply] using ne_of_gt h
  have hi1 : IntervalIntegrable (fun x : ℝ =>
      Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x))) volume (0 : ℝ) 1 :=
    hc1.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x : ℝ =>
      Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)) volume (0 : ℝ) 1 :=
    hc2.intervalIntegrable 0 1
  have hi3 : IntervalIntegrable (fun x : ℝ =>
      Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2)) volume (0 : ℝ) 1 :=
    hc3.intervalIntegrable 0 1
  -- the integral comparison
  have hmono : (∫ x in (0 : ℝ)..1,
        Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
      ≤ (m : ℝ) * (∫ x in (0 : ℝ)..1,
          Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))
        + (Real.log (m : ℝ) + I₀) := by
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x))
          ≤ (m : ℝ) * Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)
            + (Real.log (m : ℝ)
                + Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2)) := by
      intro x _
      exact log_iterC_mul_qpow_le p q hq lam E m hm x
    have hG : IntervalIntegrable (fun x : ℝ =>
        (m : ℝ) * Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)
          + (Real.log (m : ℝ)
              + Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2)))
        volume (0 : ℝ) 1 :=
      (hi2.const_mul (m : ℝ)).add (intervalIntegrable_const.add hi3)
    have hm0 := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi1 hG hpt
    have hb1 : IntervalIntegrable (fun x : ℝ =>
        (m : ℝ) * Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))
        volume (0 : ℝ) 1 := hi2.const_mul (m : ℝ)
    have hb2 : IntervalIntegrable (fun x : ℝ =>
        Real.log (m : ℝ)
          + Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) + Real.sqrt 2))
        volume (0 : ℝ) 1 := intervalIntegrable_const.add hi3
    rw [intervalIntegral.integral_add hb1 hb2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const hi3,
      intervalIntegral.integral_const] at hm0
    simpa [hI₀] using hm0
  -- substitute `lyapAvg` and `lyap`
  have hLA : lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
      = (∫ x in (0 : ℝ)..1, Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
        / ((m : ℝ) * (q : ℝ)) := by
    rw [lyapAvg, Nat.cast_mul]
  have hL : lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
      = (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1,
          Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)) :=
    Solutions.lyap_periodic p q hq lam E
  rw [hLA, hL]
  have hmq : (0 : ℝ) < (m : ℝ) * (q : ℝ) := by
    have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have h2 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    positivity
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : q ≠ 0)
  have hmqne : (m : ℝ) * (q : ℝ) ≠ 0 := ne_of_gt hmq
  -- step 1: rewrite the difference as a single quotient
  have hstep : (∫ x in (0 : ℝ)..1,
          Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
        / ((m : ℝ) * (q : ℝ))
        - (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1,
            Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))
      ≤ (Real.log (m : ℝ) + I₀) / ((m : ℝ) * (q : ℝ)) := by
    have heq : (∫ x in (0 : ℝ)..1,
            Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
          / ((m : ℝ) * (q : ℝ))
          - (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1,
              Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))
        = ((∫ x in (0 : ℝ)..1,
            Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
          - (m : ℝ) * (∫ x in (0 : ℝ)..1,
              Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)))
          / ((m : ℝ) * (q : ℝ)) := by
      field_simp
    have hfin : (∫ x in (0 : ℝ)..1,
            Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
          - (m : ℝ) * (∫ x in (0 : ℝ)..1,
              Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))
        ≤ Real.log (m : ℝ) + I₀ := by linarith [hmono]
    rw [heq]
    exact div_le_div_of_nonneg_right hfin (le_of_lt hmq)
  refine le_trans hstep ?_
  -- step 2: the logarithmic arithmetic
  have hK : Real.log (m : ℝ) + I₀ ≤ (|I₀| + 1) * (1 + Real.log ((m : ℝ) * (q : ℝ))) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hmq1 : (1 : ℝ) ≤ (m : ℝ) * (q : ℝ) := by nlinarith
    have hlognn : 0 ≤ Real.log ((m : ℝ) * (q : ℝ)) := Real.log_nonneg hmq1
    have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) * (q : ℝ)) := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith
    have hexp : (|I₀| + 1) * (1 + Real.log ((m : ℝ) * (q : ℝ)))
        = |I₀| + |I₀| * Real.log ((m : ℝ) * (q : ℝ)) + 1 + Real.log ((m : ℝ) * (q : ℝ)) := by
      ring
    rw [hexp]
    nlinarith [le_abs_self I₀, abs_nonneg I₀, hlognn, hlogm]
  calc (Real.log (m : ℝ) + I₀) / ((m : ℝ) * (q : ℝ))
      ≤ ((|I₀| + 1) * (1 + Real.log ((m : ℝ) * (q : ℝ)))) / ((m : ℝ) * (q : ℝ)) :=
        div_le_div_of_nonneg_right hK (le_of_lt hmq)

end Work.TMC7Core.Scale
