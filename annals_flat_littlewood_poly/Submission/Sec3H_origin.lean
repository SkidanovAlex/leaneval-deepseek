import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv
import Submission.Sec3Values

/-! Lemma 3.7 of the paper (H is large near `x = 0` and `x = Tπ`):

For odd `t`, `Re H(x) ≥ 1/2` whenever `|x| ≤ 1/8` or `|x − T·π| ≤ 1/8`.

PROOF (paper §3): for odd `t`, `P_t(1) = Q_t(-1) = 2^((t+1)/2)`,
`P_t(-1) = Q_t(1) = 0` (Sec3Values), and `T = 2^(t+10)` is even, hence

    H(0)   = scale·(P_t(1) + Q_t(1))·(e^{i0}=1) = 1
    H(Tπ)  = e^{iTπ}·scale·P_t(e^{iπ}) + e^{2iTπ}·scale·Q_t(e^{iπ})
           = (−1)^T·scale·P_t(−1) + 1·scale·Q_t(−1) = 1

(using `(−1)^T = 1` for even `T`).  With `‖H'‖ ≤ 4` (`H_deriv_norm_le_four`)
the mean value inequality gives `‖H(x) − H(0)‖ ≤ 4·|x|` (and similarly from
`Tπ`), so `Re H(x) ≥ 1 − 4|x| ≥ 1/2` for `|x| ≤ 1/8`. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3H

/-! Helpers for endpoint values of `H`. -/

/-- `e^{i(a+b)} = e^{ia} e^{ib}`. -/
lemma eθ_add (a b : ℝ) : Sec3.eθ (a + b) = Sec3.eθ a * Sec3.eθ b := by
  have harg : (((a + b : ℝ) : ℂ) * Complex.I) =
      (((a : ℝ) : ℂ) * Complex.I) + (((b : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_add]
    ring
  unfold Sec3.eθ
  rw [harg, Complex.exp_add]

/-- `e^{iπ} = -1`. -/
lemma eθ_pi : Sec3.eθ Real.pi = (-1 : ℂ) := by
  unfold Sec3.eθ
  exact Complex.exp_pi_mul_I

/-- `e^{i·n·π} = (-1)^n`. -/
lemma eθ_nat_mul_pi (n : ℕ) : Sec3.eθ ((n : ℝ) * Real.pi) = (-1 : ℂ) ^ n := by
  induction n with
  | zero =>
      simp [Sec3.eθ]
  | succ n ih =>
      calc
        Sec3.eθ (((n + 1 : ℕ) : ℝ) * Real.pi)
            = Sec3.eθ ((n : ℝ) * Real.pi + Real.pi) := by
                congr 1
                rw [Nat.cast_add, Nat.cast_one]
                ring
        _ = Sec3.eθ ((n : ℝ) * Real.pi) * Sec3.eθ Real.pi := eθ_add _ _
        _ = (-1 : ℂ) ^ n * (-1 : ℂ) := by rw [ih, eθ_pi]
        _ = (-1 : ℂ) ^ (n + 1) := by rw [← pow_succ]

/-- `T t = 2^(t+10)` is even. -/
lemma T_even (t : ℕ) : Even (T t) := by
  unfold T
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t + 10 ≠ 0)
  rw [hu, pow_succ, mul_comm]
  exact even_two_mul (2 ^ u)

/-- For odd `t`, `scale t · 2^((t+1)/2) = 1` (in `ℂ`). -/
lemma scale_mul_of_odd (t : ℕ) (ht : Odd t) :
    (scale t : ℂ) * (2 : ℂ) ^ ((t + 1) / 2) = 1 := by
  rcases ht with ⟨k, hk⟩
  have hdiv : (t + 1) / 2 = k + 1 := by
    rw [hk]
    rw [show (2 * k + 1 + 1) = 2 * (k + 1) by omega]
    exact Nat.mul_div_right (k + 1) (by norm_num)
  have hmain : (scale t : ℝ) * (2 : ℝ) ^ ((t + 1) / 2) = 1 := by
    rw [hdiv]
    have hs : Real.sqrt ((2 : ℝ) ^ (t + 1)) = (2 : ℝ) ^ (k + 1) := by
      rw [hk]
      rw [show (2 * k + 1 + 1) = 2 * (k + 1) by omega]
      have hsq : (2 : ℝ) ^ (2 * (k + 1)) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hsq]
      exact Real.sqrt_sq (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (k + 1))
    unfold scale
    rw [hs]
    field_simp [show (2 : ℝ) ^ (k + 1) ≠ 0 by positivity]
  exact_mod_cast hmain

/-- `H(0) = 1` for odd `t`. -/
lemma H_zero (t : ℕ) (ht : Odd t) : H t 0 = 1 := by
  have halpha : alpha t 0 = 1 := by
    unfold alpha
    have hP : ((RudinShapiro.P t).eval (Sec3.eθ (0 / (T t : ℝ)))) = (2 : ℂ) ^ ((t + 1) / 2) := by
      have hzero : Sec3.eθ (0 / (T t : ℝ)) = 1 := by simp [Sec3.eθ]
      rw [hzero]
      exact RudinShapiro.P_eval_one_of_odd ht
    rw [hP]
    exact scale_mul_of_odd t ht
  have hbeta : beta t 0 = 0 := by
    unfold beta
    have hQ : ((RudinShapiro.Q t).eval (Sec3.eθ (0 / (T t : ℝ)))) = 0 := by
      have hzero : Sec3.eθ (0 / (T t : ℝ)) = 1 := by simp [Sec3.eθ]
      rw [hzero]
      exact RudinShapiro.Q_eval_one_of_odd ht
    rw [hQ]
    simp
  calc
    H t 0 = Sec3.eθ (0 : ℝ) * alpha t 0 + Sec3.eθ (2 * (0 : ℝ)) * beta t 0 := rfl
    _ = 1 := by rw [halpha, hbeta]; simp [Sec3.eθ]

/-- `H(Tπ) = 1` for odd `t`. -/
lemma H_Tpi (t : ℕ) (ht : Odd t) : H t ((T t : ℝ) * Real.pi) = 1 := by
  let x0 : ℝ := (T t : ℝ) * Real.pi
  have he1 : Sec3.eθ x0 = (1 : ℂ) := by
    dsimp [x0]
    rw [eθ_nat_mul_pi (T t)]
    exact Even.neg_one_pow (T_even t)
  have hcast2 : 2 * ((T t : ℝ) * Real.pi) = (((2 * T t : ℕ) : ℝ) * Real.pi) := by
    rw [Nat.cast_mul]
    norm_num
    ring
  have he2 : Sec3.eθ (2 * x0) = (1 : ℂ) := by
    dsimp [x0]
    rw [hcast2]
    rw [eθ_nat_mul_pi (2 * T t)]
    exact Even.neg_one_pow (even_two_mul (T t))
  have hT0 : (T t : ℝ) ≠ 0 := by
    unfold T
    positivity
  have hdiv : x0 / (T t : ℝ) = Real.pi := by
    dsimp [x0]
    field_simp [hT0]
  have hz : Sec3.eθ (x0 / (T t : ℝ)) = (-1 : ℂ) := by
    rw [hdiv]
    exact eθ_pi
  have halpha : alpha t x0 = 0 := by
    unfold alpha
    rw [hz]
    rw [RudinShapiro.P_eval_neg_one_of_odd ht]
    simp
  have hbeta : beta t x0 = 1 := by
    unfold beta
    rw [hz]
    rw [RudinShapiro.Q_eval_neg_one_of_odd ht]
    exact scale_mul_of_odd t ht
  calc
    H t x0 = Sec3.eθ x0 * alpha t x0 + Sec3.eθ (2 * x0) * beta t x0 := rfl
    _ = 1 := by rw [he1, halpha, he2, hbeta]; norm_num

/-- `H t` is smooth. -/
lemma contDiff_H {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (H t) := by
  have hcA : ContDiff ℝ n (fun u : ℝ => Sec3.eθ u * alpha t u) :=
    (contDiff_eθ (n := n)).mul (contDiff_alpha (n := n) t)
  have hcB : ContDiff ℝ n (fun u : ℝ => Sec3.eθ (2 * u) * beta t u) :=
    (contDiff_eθ_mul (n := n) 2).mul (contDiff_beta (n := n) t)
  have hc : ContDiff ℝ n (fun u : ℝ => Sec3.eθ u * alpha t u + Sec3.eθ (2 * u) * beta t u) :=
    hcA.add hcB
  convert hc using 1
  funext u
  rfl


/-- First-derivative bound `‖H'(x)‖ ≤ 4` (proved directly for `k = 1`, avoiding
the general `H_iter_deriv_norm_le` arithmetic which is not needed here). -/
lemma H_deriv_one_bound (t : ℕ) (x : ℝ) : ‖deriv (H t) x‖ ≤ 4 := by
  let T1 : ℂ := Complex.I ^ 1 * Sec3.eθ x * alpha t x
  let T2 : ℂ := ((2 : ℂ) * Complex.I) ^ 1 * Sec3.eθ (2 * x) * beta t x
  have hk1 : (1 : ℕ) ≤ 1 := le_rfl
  have hk4 : (1 : ℕ) ≤ 4 := by norm_num
  have hdiff : ‖iteratedDeriv 1 (H t) x - (T1 + T2)‖ ≤ 1 / 8 := by
    have hFA : ContDiffAt ℝ 1 (FA t) x := by
      unfold FA
      exact ((contDiff_eθ (n := 1)).contDiffAt.mul (contDiff_alpha (n := 1) t).contDiffAt)
    have hFB : ContDiffAt ℝ 1 (FB t) x := by
      unfold FB
      exact ((contDiff_eθ_mul (n := 1) 2).contDiffAt.mul (contDiff_beta (n := 1) t).contDiffAt)
    rw [H_eq_FA_add_FB]
    have hadd := iteratedDeriv_add (n := 1) (f := FA t) (g := FB t) hFA hFB
    rw [hadd]
    have htarget : (iteratedDeriv 1 (FA t) x + iteratedDeriv 1 (FB t) x) -
        ((Complex.I ^ 1 * Sec3.eθ x * alpha t x) + (((2 : ℂ) * Complex.I) ^ 1 * Sec3.eθ (2 * x) * beta t x))
        = (iteratedDeriv 1 (FA t) x - (Complex.I ^ 1 * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv 1 (FB t) x - (((2 : ℂ) * Complex.I) ^ 1 * Sec3.eθ (2 * x) * beta t x)) := by ring
    rw [htarget]
    have h1 := norm_FA_sub_target_le t (k := 1) hk1 hk4 x
    have h2 := norm_FB_sub_target_le t (k := 1) hk1 hk4 x
    have hsumA : (∑ i ∈ Finset.range 1, ((Nat.choose 1 i : ℝ) * (1 / (2 : ℝ) ^ (9 * (1 - i))))) =
        1 / (2 : ℝ) ^ 9 := by
      norm_num [Finset.sum_range_succ]
    have hsumB : (∑ i ∈ Finset.range 1, ((Nat.choose 1 i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (1 - i))))) =
        1 / (2 : ℝ) ^ 9 := by
      norm_num [Finset.sum_range_succ]
    calc
      ‖(iteratedDeriv 1 (FA t) x - (Complex.I ^ 1 * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv 1 (FB t) x - (((2 : ℂ) * Complex.I) ^ 1 * Sec3.eθ (2 * x) * beta t x))‖
          ≤ ‖iteratedDeriv 1 (FA t) x - (Complex.I ^ 1 * Sec3.eθ x * alpha t x)‖ +
              ‖iteratedDeriv 1 (FB t) x - (((2 : ℂ) * Complex.I) ^ 1 * Sec3.eθ (2 * x) * beta t x)‖ := norm_add_le _ _
      _ ≤ (∑ i ∈ Finset.range 1, ((Nat.choose 1 i : ℝ) * (1 / (2 : ℝ) ^ (9 * (1 - i))))) +
            (∑ i ∈ Finset.range 1, ((Nat.choose 1 i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (1 - i))))) := by
            exact add_le_add h1 h2
      _ = 1 / (2 : ℝ) ^ 9 + 1 / (2 : ℝ) ^ 9 := by rw [hsumA, hsumB]
      _ ≤ 1 / 8 := by norm_num
  have hT1 : ‖T1‖ ≤ 1 := by
    unfold T1
    rw [norm_mul]
    rw [norm_eθ_I_pow 1 x]
    have hα : ‖alpha t x‖ ≤ 1 := norm_alpha_le t x
    nlinarith
  have hT2 : ‖T2‖ ≤ (2 : ℝ) ^ 1 := by
    unfold T2
    rw [norm_mul]
    rw [norm_eθ_2I_pow 1 x]
    have hβ : ‖beta t x‖ ≤ 1 := norm_beta_le t x
    have hp : 0 ≤ (2 : ℝ) ^ 1 := pow_nonneg (by norm_num) 1
    have hle : (2 : ℝ) ^ 1 * ‖beta t x‖ ≤ (2 : ℝ) ^ 1 * 1 := mul_le_mul_of_nonneg_left hβ hp
    nlinarith
  have hTsum1 : ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le T1 T2
  have hb : ‖iteratedDeriv 1 (H t) x‖ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := by
    calc
      ‖iteratedDeriv 1 (H t) x‖ = ‖(iteratedDeriv 1 (H t) x - (T1 + T2)) + (T1 + T2)‖ := by ring_nf
      _ ≤ ‖iteratedDeriv 1 (H t) x - (T1 + T2)‖ + ‖T1 + T2‖ := norm_add_le _ _
      _ ≤ 1 / 8 + ‖T1 + T2‖ := by nlinarith [hdiff]
      _ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := by nlinarith [hTsum1]
  have hT2' : ‖T2‖ ≤ 2 := by simpa using hT2
  have hfin : ‖iteratedDeriv 1 (H t) x‖ ≤ 4 := by
    calc
      ‖iteratedDeriv 1 (H t) x‖ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := hb
      _ ≤ 4 := by nlinarith [hT1, hT2']
  rw [iteratedDeriv_one] at hfin
  exact hfin

/-- Mean-value estimate `‖H(x) − H(y)‖ ≤ 4|x−y|` (from `‖H'‖ ≤ 4`). -/
lemma H_lipschitz (t : ℕ) (x y : ℝ) : ‖H t x - H t y‖ ≤ 4 * |x - y| := by
  have hH : ContDiff ℝ 1 (H t) := contDiff_H (n := 1) t
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (H t) z := by
    intro z hz
    exact hH.contDiffAt.differentiableAt_one
  have hbnd : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv (H t) z‖ ≤ 4 := by
    intro z hz
    exact H_deriv_one_bound t z
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℂ) (f := H t)
    (s := (Set.univ : Set ℝ)) (C := 4) hdiff hbnd convex_univ (Set.mem_univ x) (Set.mem_univ y)
  calc
    ‖H t x - H t y‖ = ‖H t y - H t x‖ := by rw [norm_sub_rev]
    _ ≤ 4 * ‖y - x‖ := hmvt
    _ = 4 * |x - y| := by rw [Real.norm_eq_abs, abs_sub_comm]

/-- `Re H(x) ≥ 1/2` near `x = 0`. -/
lemma H_re_ge_half_near_zero (t : ℕ) (ht : Odd t) (x : ℝ) (hx : |x| ≤ 1 / 8) :
    (1 / 2 : ℝ) ≤ (H t x).re := by
  have hd : -(‖H t x - H t 0‖) ≤ (H t x - H t 0).re := by
    exact (abs_le.mp (Complex.abs_re_le_norm (H t x - H t 0))).1
  have hnorm : ‖H t x - H t 0‖ ≤ 1 / 2 := by
    have hL := H_lipschitz t x 0
    have hx0 : |x - 0| ≤ 1 / 8 := by simpa using hx
    have h4 : 4 * |x - 0| ≤ 4 * (1 / 8) := by
      exact mul_le_mul_of_nonneg_left hx0 (by norm_num)
    linarith
  have hz : H t 0 = 1 := H_zero t ht
  have hsub : H t 0 + (H t x - H t 0) = H t x := by ring
  have hmain : 1 - ‖H t x - H t 0‖ ≤ (H t x).re := by
    calc
      1 - ‖H t x - H t 0‖ = (H t 0).re - ‖H t x - H t 0‖ := by rw [hz]; norm_num
      _ ≤ (H t 0).re + (H t x - H t 0).re := by linarith
      _ = (H t x).re := by
        rw [← Complex.add_re]
        rw [hsub]
  calc
    (1 / 2 : ℝ) ≤ 1 - ‖H t x - H t 0‖ := by linarith
    _ ≤ (H t x).re := hmain

/-- `Re H(x) ≥ 1/2` near `x = Tπ`. -/
lemma H_re_ge_half_near_Tpi (t : ℕ) (ht : Odd t) (x : ℝ)
    (hx : |x - (T t : ℝ) * Real.pi| ≤ 1 / 8) :
    (1 / 2 : ℝ) ≤ (H t x).re := by
  let x0 : ℝ := (T t : ℝ) * Real.pi
  have hd : -(‖H t x - H t x0‖) ≤ (H t x - H t x0).re := by
    exact (abs_le.mp (Complex.abs_re_le_norm (H t x - H t x0))).1
  have hnorm : ‖H t x - H t x0‖ ≤ 1 / 2 := by
    have hL := H_lipschitz t x x0
    have hx0 : |x - x0| ≤ 1 / 8 := by simpa [x0] using hx
    have h4 : 4 * |x - x0| ≤ 4 * (1 / 8) := by
      exact mul_le_mul_of_nonneg_left hx0 (by norm_num)
    linarith
  have hx0v : H t x0 = 1 := by
    simpa [x0] using (H_Tpi t ht)
  have hsub : H t x0 + (H t x - H t x0) = H t x := by ring
  have hmain : 1 - ‖H t x - H t x0‖ ≤ (H t x).re := by
    calc
      1 - ‖H t x - H t x0‖ = (H t x0).re - ‖H t x - H t x0‖ := by rw [hx0v]; norm_num
      _ ≤ (H t x0).re + (H t x - H t x0).re := by linarith
      _ = (H t x).re := by
        rw [← Complex.add_re]
        rw [hsub]
  calc
    (1 / 2 : ℝ) ≤ 1 - ‖H t x - H t x0‖ := by linarith
    _ ≤ (H t x).re := hmain

end Sec3H
end Submission
