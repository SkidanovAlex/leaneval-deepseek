import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_aux
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds
import Submission.Work.Asymptotics.Compact.kminus_tail_main
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelJAtoms


set_option maxHeartbeats 1000000

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)

namespace Work.Asymptotics

noncomputable section


/-! ## Elementary comparisons of exponentials and `scale`-powers -/

/-- For `k ≥ 1` and `Im τ ≤ t`, `e^{-kπt} ≤ e^{-π(t - Im τ)}`. -/
private lemma exp_decay_le (k : ℝ) (hk : 1 ≤ k) {τ : ℍ} {t : ℝ} (ht : τ.im ≤ t) :
    Real.exp (-(k * Real.pi * t)) ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
  apply Real.exp_le_exp.mpr
  have ht0 : 0 ≤ t := le_trans (le_of_lt τ.im_pos) ht
  have hk0 : 0 ≤ k - 1 := by linarith
  have ha : 0 ≤ (k - 1) * t * Real.pi := mul_nonneg (mul_nonneg hk0 ht0) Real.pi_pos.le
  have hb : 0 ≤ τ.im * Real.pi := mul_nonneg (le_of_lt τ.im_pos) Real.pi_pos.le
  have h := add_nonneg ha hb
  linarith

/-- For `k ≥ 1`, `a ≥ 0`: `e^{-kπt - aπ Im τ} ≤ e^{-π(t - Im τ)}`. -/
private lemma exp_decay_gen (k a : ℝ) (hk : 1 ≤ k) (ha : 0 ≤ a) {τ : ℍ} {t : ℝ}
    (ht : τ.im ≤ t) :
    Real.exp (-(k * Real.pi * t) - a * Real.pi * τ.im)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
  rw [show -(k * Real.pi * t) - a * Real.pi * τ.im
      = (-(a * Real.pi * τ.im)) + (-(k * Real.pi * t)) by ring, Real.exp_add]
  have h1 : Real.exp (-(a * Real.pi * τ.im)) * Real.exp (-(k * Real.pi * t))
      ≤ 1 * Real.exp (-(k * Real.pi * t)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ a * Real.pi * τ.im := by positivity
    linarith
  calc Real.exp (-(a * Real.pi * τ.im)) * Real.exp (-(k * Real.pi * t))
      ≤ 1 * Real.exp (-(k * Real.pi * t)) := h1
    _ = Real.exp (-(k * Real.pi * t)) := one_mul _
    _ ≤ Real.exp (-(Real.pi * (t - τ.im))) := exp_decay_le k hk ht

/-- `e^{-2π(t - Im τ)} ≤ e^{-π(t - Im τ)}`. -/
private lemma exp_two_decay {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    Real.exp (-(2 * Real.pi * t) + 2 * Real.pi * τ.im)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
  apply Real.exp_le_exp.mpr
  have h1 : τ.im * Real.pi ≤ t * Real.pi :=
    mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
  nlinarith [h1]

/-- `e^{-4π(t - Im τ)} ≤ e^{-π(t - Im τ)}`. -/
private lemma exp_four_decay {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    Real.exp (-(4 * Real.pi * t) + 4 * Real.pi * τ.im)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
  apply Real.exp_le_exp.mpr
  have h1 : τ.im * Real.pi ≤ t * Real.pi :=
    mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
  nlinarith [h1]

/-- `e^{-4πt + 2π Im τ} ≤ e^{-π(t - Im τ)}`. -/
private lemma exp_four_two_decay {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    Real.exp (-(4 * Real.pi * t) + 2 * Real.pi * τ.im)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
  apply Real.exp_le_exp.mpr
  have h2 : τ.im ≤ 3 * t := by linarith [τ.im_pos, ht]
  have h1 : τ.im * Real.pi ≤ 3 * (t * Real.pi) := by
    calc τ.im * Real.pi ≤ (3 * t) * Real.pi := mul_le_mul_of_nonneg_right h2 Real.pi_pos.le
      _ = 3 * (t * Real.pi) := by ring
  nlinarith [h1]

/-- `(scale τ)^N ≥ 0`. -/
private lemma scale_rpow_nonneg (τ : ℍ) (N : ℝ) : (0:ℝ) ≤ scale τ ^ N :=
  Real.rpow_nonneg (le_of_lt (scale_pos τ)) N

/-- `(scale τ)^N ≤ (scale τ)^M` for `N ≤ M`. -/
private lemma scale_rpow_mono {τ : ℍ} {N M : ℝ} (h : N ≤ M) :
    scale τ ^ N ≤ scale τ ^ M :=
  Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) h

/-- `1 ≤ (scale τ)^N` for `0 ≤ N`. -/
private lemma one_le_scale_rpow {τ : ℍ} {N : ℝ} (h : 0 ≤ N) : 1 ≤ scale τ ^ N :=
  Real.one_le_rpow (Work.Kernels.one_le_scale τ) h

/-- Inflate the exponent of a `scale`-power bound. -/
private lemma scale_inflate {X : ℂ} {C N d : ℝ} {τ : ℍ} (h : ‖X‖ ≤ C * scale τ ^ N)
    (hC : 0 ≤ C) (hd : N ≤ d) : ‖X‖ ≤ C * scale τ ^ d :=
  le_trans h (mul_le_mul_of_nonneg_left (scale_rpow_mono hd) hC)

/-- `‖Ept z‖ = e^{-π t}` on the contour `z = i t`. -/
private lemma norm_Ept_axis {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Ept z‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept, ft_im_of_coe hz]

/-- `‖q(z)‖ = ‖Ept z‖²`. -/
private lemma norm_q_eq (z : ℍ) : ‖qParamFun z‖ = ‖Ept z‖ ^ 2 := by
  rw [qParamFun_eq_Ept_sq, norm_pow]

/-- `‖q(z)‖ ≤ 1` for `1 ≤ Im z`. -/
private lemma norm_q_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖qParamFun z‖ ≤ 1 := by
  rw [norm_q_eq]
  exact pow_le_one₀ (norm_nonneg _) (KF24.norm_Ept_le_one' hz)

/-- `q ^ 3 ≤ q ^ 2` for `0 ≤ q ≤ 1`. -/
private lemma q3_le_q2 {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : q ^ 3 ≤ q ^ 2 := by
  calc q ^ 3 = q ^ 2 * q := by ring
    _ ≤ q ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg h0 2)
    _ = q ^ 2 := by ring

/-- `q ^ 4 ≤ q ^ 2` for `0 ≤ q ≤ 1`. -/
private lemma q4_le_q2 {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : q ^ 4 ≤ q ^ 2 := by
  calc q ^ 4 = q ^ 2 * q ^ 2 := by ring
    _ ≤ q ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (pow_nonneg h0 2)
    _ = q ^ 2 := by ring

/-- `(e^x)^n = e^{n x}`. -/
private lemma exp_pow_eq (x : ℝ) (n : ℕ) : Real.exp x ^ n = Real.exp ((n : ℝ) * x) :=
  (Real.exp_nat_mul x n).symm

/-- `x * y * z ≤ x * y * w` for `x, y ≥ 0`, `z ≤ w`. -/
private lemma mul3_le_mul3 {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : z ≤ w) :
    x * y * z ≤ x * y * w :=
  mul_le_mul_of_nonneg_left h (mul_nonneg hx hy)

/-- `c₁ * x + c₂ * x ≤ C * x` for `c₁ + c₂ ≤ C` and `0 ≤ x`. -/
private lemma add_mul_le_mul {c₁ c₂ C x : ℝ} (h : c₁ + c₂ ≤ C) (h0 : 0 ≤ x) :
    c₁ * x + c₂ * x ≤ C * x := by
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right h h0

/-- Nonnegativity of `a * scale τ ^ N`. -/
private lemma pos_f2 {τ : ℍ} {N : ℝ} {a : ℝ} (ha : 0 ≤ a) :
    (0:ℝ) ≤ a * (scale τ) ^ N :=
  mul_nonneg ha (scale_rpow_nonneg τ N)
/-- Nonnegativity of `a * scale τ ^ N * b`. -/
private lemma pos_f3 {τ : ℍ} {N : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (0:ℝ) ≤ a * (scale τ) ^ N * b :=
  mul_nonneg (mul_nonneg ha (scale_rpow_nonneg τ N)) hb
/-- Nonnegativity of `a * scale τ ^ N * b * c`. -/
private lemma pos_f4 {τ : ℍ} {N : ℝ} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : (0:ℝ) ≤ a * (scale τ) ^ N * b * c :=
  mul_nonneg (mul_nonneg (mul_nonneg ha (scale_rpow_nonneg τ N)) hb) hc
/-- Nonnegativity of `a * scale τ ^ N * b * c * d`. -/
private lemma pos_f5 {τ : ℍ} {N : ℝ} {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) : (0:ℝ) ≤ a * (scale τ) ^ N * b * c * d :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha (scale_rpow_nonneg τ N)) hb) hc) hd
/-- Nonnegativity of `scale τ ^ N * b`. -/
private lemma pos_f1b {τ : ℍ} {N : ℝ} {b : ℝ} (hb : 0 ≤ b) :
    (0:ℝ) ≤ (scale τ) ^ N * b :=
  mul_nonneg (scale_rpow_nonneg τ N) hb

/-- Exponent comparison `A1` for `Dev3`. -/
private lemma exp_arg_A1 {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    -(4 * Real.pi * t) + 2 * Real.pi * t ≤ -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im := by
  have ht0 : (0:ℝ) < t := by linarith [τ.im_pos, ht]
  have h1 : -(4 * Real.pi * t) + 2 * Real.pi * t = -(2 * (Real.pi * t)) := by ring
  have h2 : -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im
      = -(Real.pi * t) + 3 * (Real.pi * τ.im) := by ring
  rw [h1, h2]
  nlinarith [Real.pi_pos, τ.im_pos, mul_pos Real.pi_pos τ.im_pos,
    mul_pos Real.pi_pos ht0]
/-- Exponent comparison `A2` for `Dev3`. -/
private lemma exp_arg_A2 {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    -(4 * Real.pi * t) + 4 * Real.pi * τ.im + 2 * Real.pi * t
      ≤ -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im := by
  have h1 : -(4 * Real.pi * t) + 4 * Real.pi * τ.im + 2 * Real.pi * t
      = -(2 * (Real.pi * t)) + 4 * (Real.pi * τ.im) := by ring
  have h2 : -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im
      = -(Real.pi * t) + 3 * (Real.pi * τ.im) := by ring
  rw [h1, h2]
  have ht0 : (0:ℝ) < t := by linarith [τ.im_pos, ht]
  have hle : τ.im ≤ t := by linarith
  have hptb : Real.pi * τ.im ≤ Real.pi * t := mul_le_mul_of_nonneg_left hle Real.pi_pos.le
  nlinarith [hptb, mul_pos Real.pi_pos ht0, Real.pi_pos, τ.im_pos]
/-- Exponent comparison `A3` for `Dev3`. -/
private lemma exp_arg_A3 {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    -(4 * Real.pi * t) ≤ -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im := by
  have ht0 : (0:ℝ) < t := by linarith [τ.im_pos, ht]
  have h2 : -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im
      = -(Real.pi * t) + 3 * (Real.pi * τ.im) := by ring
  rw [h2]
  nlinarith [Real.pi_pos, τ.im_pos, mul_pos Real.pi_pos τ.im_pos,
    mul_pos Real.pi_pos ht0]
/-- Exponent comparison `A4` for `Dev3`. -/
private lemma exp_arg_A4 {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) :
    -(4 * Real.pi * t) + 4 * Real.pi * τ.im
      ≤ -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im := by
  have h1 : -(4 * Real.pi * t) + 4 * Real.pi * τ.im
      = -(4 * (Real.pi * t)) + 4 * (Real.pi * τ.im) := by ring
  have h2 : -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im
      = -(Real.pi * t) + 3 * (Real.pi * τ.im) := by ring
  rw [h1, h2]
  have ht0 : (0:ℝ) < t := by linarith [τ.im_pos, ht]
  have hle : τ.im ≤ t := by linarith
  have hptb : Real.pi * τ.im ≤ Real.pi * t := mul_le_mul_of_nonneg_left hle Real.pi_pos.le
  nlinarith [hptb, mul_pos Real.pi_pos ht0, Real.pi_pos, τ.im_pos]

/-- The triangle inequality for two terms. -/
private lemma tri2 {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a + b‖ ≤ A + B := by
  linarith [norm_add_le a b]
private lemma tri2s {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a - b‖ ≤ A + B := by
  linarith [norm_sub_le a b]
private lemma tri3 {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) :
    ‖a + b + c‖ ≤ A + B + C := by
  linarith [norm_add_le (a + b) c, norm_add_le a b]
private lemma tri3s {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) :
    ‖a + b - c‖ ≤ A + B + C := by
  linarith [norm_sub_le (a + b) c, norm_add_le a b]
private lemma tri3sa {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) :
    ‖a - b + c‖ ≤ A + B + C := by
  linarith [norm_add_le (a - b) c, norm_sub_le a b]
private lemma tri4 {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) : ‖a + b + c + d‖ ≤ A + B + C + D := by
  linarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]
private lemma tri4s {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) : ‖a + b + c - d‖ ≤ A + B + C + D := by
  linarith [norm_sub_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]
private lemma tri4m {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) : ‖a + b - c - d‖ ≤ A + B + C + D := by
  linarith [norm_sub_le (a + b - c) d, norm_sub_le (a + b) c, norm_add_le a b]
private lemma tri5 {a b c d e : ℂ} {A B C D E : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) :
    ‖a + b + c + d + e‖ ≤ A + B + C + D + E := by
  linarith [norm_add_le (a + b + c + d) e, norm_add_le (a + b + c) d, norm_add_le (a + b) c,
    norm_add_le a b]
private lemma tri5m {a b c d e : ℂ} {A B C D E : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) :
    ‖a + b + c + d - e‖ ≤ A + B + C + D + E := by
  linarith [norm_sub_le (a + b + c + d) e, norm_add_le (a + b + c) d, norm_add_le (a + b) c,
    norm_add_le a b]
private lemma tri5m2 {a b c d e : ℂ} {A B C D E : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) :
    ‖a + b + c - d - e‖ ≤ A + B + C + D + E := by
  linarith [norm_sub_le (a + b + c - d) e, norm_sub_le (a + b + c) d, norm_add_le (a + b) c,
    norm_add_le a b]
private lemma tri6 {a b c d e f : ℂ} {A B C D E F : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) (hf : ‖f‖ ≤ F) :
    ‖a + b + c + d + e + f‖ ≤ A + B + C + D + E + F := by
  linarith [norm_add_le (a + b + c + d + e) f, norm_add_le (a + b + c + d) e,
    norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]
private lemma tri6m {a b c d e f : ℂ} {A B C D E F : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) (hf : ‖f‖ ≤ F) :
    ‖a + b + c + d + e - f‖ ≤ A + B + C + D + E + F := by
  linarith [norm_sub_le (a + b + c + d + e) f, norm_add_le (a + b + c + d) e,
    norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]
private lemma tri7s {a b c d e f g : ℂ} {A B C D E F G : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) (hf : ‖f‖ ≤ F)
    (hg : ‖g‖ ≤ G) : ‖a + b + c + d + e + f - g‖ ≤ A + B + C + D + E + F + G := by
  linarith [norm_sub_le (a + b + c + d + e + f) g, norm_add_le (a + b + c + d + e) f,
    norm_add_le (a + b + c + d) e, norm_add_le (a + b + c) d, norm_add_le (a + b) c,
    norm_add_le a b]

/-- `e^a e^b ≤ e^c e^d` from `a + b ≤ c + d`. -/
private lemma exp_mul_le_exp_mul {a b c d : ℝ} (h : a + b ≤ c + d) :
    Real.exp a * Real.exp b ≤ Real.exp c * Real.exp d := by
  simp only [← Real.exp_add]
  exact Real.exp_le_exp.mpr h
private lemma exp1_le_exp_mul {a c d : ℝ} (h : a ≤ c + d) :
    Real.exp a ≤ Real.exp c * Real.exp d := by
  simp only [← Real.exp_add]
  exact Real.exp_le_exp.mpr h
private lemma exp3_le_exp2 {a b c d e : ℝ} (h : a + b + c ≤ d + e) :
    Real.exp a * Real.exp b * Real.exp c ≤ Real.exp d * Real.exp e := by
  simp only [← Real.exp_add]
  exact Real.exp_le_exp.mpr h

/-- Inflate the exponent `N` of a `scale`-power, keeping an extra factor `K`. -/
private lemma scale_inflate_mul {X : ℂ} {C N d K : ℝ} {τ : ℍ}
    (h : ‖X‖ ≤ C * (scale τ) ^ N * K) (hC : 0 ≤ C) (hd : N ≤ d) (hK : 0 ≤ K) :
    ‖X‖ ≤ C * (scale τ) ^ d * K := by
  have h1 : (scale τ) ^ N ≤ (scale τ) ^ d := scale_rpow_mono hd
  have h2 : C * (scale τ) ^ N ≤ C * (scale τ) ^ d := mul_le_mul_of_nonneg_left h1 hC
  exact le_trans h (mul_le_mul_of_nonneg_right h2 hK)

/-- `‖1 - c * Ept z ^ 2‖ ≤ 1 + c` for `1 ≤ Im z` and `c ≥ 0`. -/
private lemma norm_one_sub_const_Ept_sq (c : ℝ) (hc : 0 ≤ c) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖(1:ℂ) - (c:ℂ) * Ept z ^ 2‖ ≤ 1 + c := by
  have he : ‖Ept z‖ ≤ 1 := KF24.norm_Ept_le_one' hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  calc ‖(1:ℂ) - (c:ℂ) * Ept z ^ 2‖ ≤ 1 + ‖(c:ℂ) * Ept z ^ 2‖ := by
        have hh := norm_sub_le (1:ℂ) ((c:ℂ) * Ept z ^ 2)
        simpa only [norm_one] using hh
    _ = 1 + c * ‖(Ept z) ^ 2‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ 1 + c := by
        have h2 : c * ‖(Ept z) ^ 2‖ ≤ c * 1 := mul_le_mul_of_nonneg_left he2 hc
        linarith

/-- `‖D2ref z‖ ≤ 161` for `1 ≤ Im z`. -/
private lemma norm_D2ref_le {z : ℍ} (hz : 1 ≤ z.im) : ‖Compact.D2ref z‖ ≤ 161 := by
  rw [Compact.D2ref]
  have he : ‖Ept z‖ ≤ 1 := KF24.norm_Ept_le_one' hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  calc ‖(1:ℂ) + 16 * Ept z - 144 * Ept z ^ 2‖
      ≤ ‖(1:ℂ) + 16 * Ept z‖ + ‖(144:ℂ) * Ept z ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 16 * ‖Ept z‖) + 144 * ‖Ept z‖ ^ 2 := by
        have hb := norm_add_le (1:ℂ) ((16:ℂ) * Ept z)
        have h16 : ‖(16:ℂ) * Ept z‖ = 16 * ‖Ept z‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
        have h144 : ‖(144:ℂ) * Ept z ^ 2‖ = 144 * ‖Ept z‖ ^ 2 := by
          simp only [norm_mul, norm_pow, Complex.norm_ofNat]
        have hb1 : ‖(1:ℂ) + 16 * Ept z‖ ≤ 1 + 16 * ‖Ept z‖ := by
          calc ‖(1:ℂ) + 16 * Ept z‖ ≤ ‖(1:ℂ)‖ + ‖(16:ℂ) * Ept z‖ := hb
            _ = 1 + 16 * ‖Ept z‖ := by rw [h16, norm_one]
        rw [h144]; linarith
    _ ≤ 161 := by
        have he2' : ‖Ept z‖ ^ 2 ≤ 1 := by
          rw [norm_pow] at he2
          exact he2
        nlinarith [he, he2', norm_nonneg (Ept z)]

/-! ## Monomial norm helpers -/

/-! ## Second-order expansion of `E₄³` and of the `z`-atoms -/

/-- `‖E₄(z)³ - 1 - 720 q(z)‖ ≤ C ‖q(z)‖²` for `1 ≤ Im z`. -/
private lemma E4cube_second : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖E4Fun z ^ 3 - 1 - 720 * qParamFun z‖ ≤ C * ‖qParamFun z‖ ^ 2 := by
  obtain ⟨Cδ, hCδ, hδ⟩ := E4Fun_two_term
  refine ⟨3 * Cδ + 3 * (240 + Cδ) ^ 2 + (240 + Cδ) ^ 3, by positivity, fun z hz => ?_⟩
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_q_le_one hz
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  set q := qParamFun z with hq
  set δ := E4Fun z - 1 - 240 * q with hδd
  have hδb : ‖δ‖ ≤ Cδ * ‖q‖ ^ 2 := by rw [hδd, hq]; exact hδ z hz
  have hE4 : E4Fun z = 1 + 240 * q + δ := by rw [hδd]; ring
  have hx : ‖240 * q + δ‖ ≤ (240 + Cδ) * ‖q‖ := by
    have h1 : ‖(240:ℂ) * q‖ = 240 * ‖q‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
    calc ‖240 * q + δ‖ ≤ ‖(240:ℂ) * q‖ + ‖δ‖ := norm_add_le _ _
      _ = 240 * ‖q‖ + ‖δ‖ := by rw [h1]
      _ ≤ 240 * ‖q‖ + Cδ * ‖q‖ ^ 2 := by linarith
      _ ≤ (240 + Cδ) * ‖q‖ := by
          have h2 : Cδ * ‖q‖ ^ 2 ≤ Cδ * ‖q‖ :=
            mul_le_mul_of_nonneg_left (by nlinarith [hq0, hq1]) hCδ.le
          linarith
  have hid : E4Fun z ^ 3 - 1 - 720 * q
      = 3 * δ + 3 * (240 * q + δ) ^ 2 + (240 * q + δ) ^ 3 := by
    rw [hE4]; ring
  rw [hid]
  have h243 : (0:ℝ) ≤ 240 + Cδ := by linarith
  have hq2 : ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 := by nlinarith [hq0, hq1]
  have htri : ‖3 * δ + 3 * (240 * q + δ) ^ 2 + (240 * q + δ) ^ 3‖
      ≤ 3 * ‖δ‖ + 3 * ‖240 * q + δ‖ ^ 2 + ‖240 * q + δ‖ ^ 3 := by
    have ha : ‖3 * δ + 3 * (240 * q + δ) ^ 2‖ ≤ 3 * ‖δ‖ + 3 * ‖240 * q + δ‖ ^ 2 := by
      have h1 : ‖(3:ℂ) * δ‖ = 3 * ‖δ‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
      have h2 : ‖(3:ℂ) * (240 * q + δ) ^ 2‖ = 3 * ‖240 * q + δ‖ ^ 2 := by
        rw [norm_mul, Complex.norm_ofNat, norm_pow]
      calc ‖3 * δ + 3 * (240 * q + δ) ^ 2‖
          ≤ ‖(3:ℂ) * δ‖ + ‖(3:ℂ) * (240 * q + δ) ^ 2‖ := norm_add_le _ _
        _ = 3 * ‖δ‖ + 3 * ‖240 * q + δ‖ ^ 2 := by rw [h1, h2]
    have h3 : ‖((240 * q + δ)) ^ 3‖ = ‖240 * q + δ‖ ^ 3 := norm_pow _ 3
    calc ‖3 * δ + 3 * (240 * q + δ) ^ 2 + (240 * q + δ) ^ 3‖
        ≤ ‖3 * δ + 3 * (240 * q + δ) ^ 2‖ + ‖((240 * q + δ)) ^ 3‖ := norm_add_le _ _
      _ ≤ (3 * ‖δ‖ + 3 * ‖240 * q + δ‖ ^ 2) + ‖240 * q + δ‖ ^ 3 := by
          rw [h3]; linarith [ha]
  refine le_trans htri ?_
  have hsq : ‖240 * q + δ‖ ^ 2 ≤ ((240 + Cδ) * ‖q‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hcu : ‖240 * q + δ‖ ^ 3 ≤ ((240 + Cδ) * ‖q‖) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hx 3
  have e2 : 3 * ((240 + Cδ) * ‖q‖) ^ 2 = 3 * (240 + Cδ) ^ 2 * ‖q‖ ^ 2 := by ring
  have e3 : ((240 + Cδ) * ‖q‖) ^ 3 = (240 + Cδ) ^ 3 * ‖q‖ ^ 3 := by ring
  have e4 : (240 + Cδ) ^ 3 * ‖q‖ ^ 3 ≤ (240 + Cδ) ^ 3 * ‖q‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hq2 (pow_nonneg h243 3)
  nlinarith [hδb, hsq, hcu, e2, e3, e4, hq0, h243]

/-- `E₁₄(z) = 1 - 24 q(z) + O(‖q(z)‖²)`: `dE14 = O(‖q‖²)`. -/
private lemma dE14_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dE14 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨Cδ, hCδ, hδ⟩ := E4Fun_two_term
  obtain ⟨Cε, hCε, hε⟩ := E6Fun_two_term
  set A := Cε + 2 * Cδ + (240 + Cδ) ^ 2 with hA
  set B := 1008 * (240 + Cδ) + 2 * (240 + Cδ) * Cε + 504 * (240 + Cδ) ^ 2
      + (240 + Cδ) ^ 2 * Cε with hB
  refine ⟨A + B + 1, by positivity, fun z hz => ?_⟩
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_q_le_one hz
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have hq3 : ‖qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hq4 : ‖qParamFun z‖ ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
  set q := qParamFun z with hq
  set δ := E4Fun z - 1 - 240 * q with hδd
  set ε := E6Fun z - 1 + 504 * q with hεd
  set X := 240 * q + δ with hXd
  have hδb : ‖δ‖ ≤ Cδ * ‖q‖ ^ 2 := by rw [hδd, hq]; exact hδ z hz
  have hεb : ‖ε‖ ≤ Cε * ‖q‖ ^ 2 := by rw [hεd, hq]; exact hε z hz
  have hE4 : E4Fun z = 1 + X := by rw [hXd, hδd]; ring
  have hE6 : E6Fun z = 1 - 504 * q + ε := by rw [hεd]; ring
  have hX0 : (0:ℝ) ≤ ‖X‖ := norm_nonneg _
  have hXb : ‖X‖ ≤ (240 + Cδ) * ‖q‖ := by
    have h1 : ‖(240:ℂ) * q‖ = 240 * ‖q‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
    have a := norm_add_le ((240:ℂ) * q) δ
    rw [h1] at a
    have h2 : Cδ * ‖q‖ ^ 2 ≤ Cδ * ‖q‖ :=
      mul_le_mul_of_nonneg_left (by nlinarith [hq0, hq1]) hCδ.le
    linarith [a, hδb, h2]
  have hX2 : ‖X‖ ^ 2 ≤ ((240 + Cδ) * ‖q‖) ^ 2 := pow_le_pow_left₀ hX0 hXb 2
  have hid : Compact.dE14 z
      = (ε + 2 * δ + X ^ 2) + (-1008 * q * X + 2 * X * ε - 504 * q * X ^ 2 + X ^ 2 * ε) := by
    have hE14 : E14Fun z = E4Fun z ^ 2 * E6Fun z := rfl
    have href : Compact.E14ref z = 1 - 24 * q := by
      rw [Compact.E14ref, hq, qParamFun_eq_Ept_sq]
    rw [Compact.dE14, href, hE14, hE4, hE6, hXd]
    ring
  have h243 : (0:ℝ) ≤ 240 + Cδ := by linarith
  have hqE : ‖q‖ ^ 2 = ‖Ept z‖ ^ 4 := by rw [hq, norm_q_eq]; ring
  have g1 : ‖ε + 2 * δ + X ^ 2‖ ≤ A * ‖q‖ ^ 2 := by
    have b1 : ‖ε + 2 * δ‖ ≤ Cε * ‖q‖ ^ 2 + 2 * Cδ * ‖q‖ ^ 2 := by
      have a := norm_add_le ε ((2:ℂ) * δ)
      have h2 : ‖(2:ℂ) * δ‖ = 2 * ‖δ‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
      rw [h2] at a
      have h3 : 2 * ‖δ‖ ≤ 2 * (Cδ * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left hδb (by norm_num)
      have h4 : 2 * (Cδ * ‖q‖ ^ 2) = 2 * Cδ * ‖q‖ ^ 2 := by ring
      linarith [a, hεb, h3, h4]
    have b2 : ‖X ^ 2‖ ≤ (240 + Cδ) ^ 2 * ‖q‖ ^ 2 := by
      rw [norm_pow]
      calc ‖X‖ ^ 2 ≤ ((240 + Cδ) * ‖q‖) ^ 2 := hX2
        _ = (240 + Cδ) ^ 2 * ‖q‖ ^ 2 := by ring
    have a := norm_add_le (ε + 2 * δ) (X ^ 2)
    have hAe : A * ‖q‖ ^ 2 = (Cε + 2 * Cδ + (240 + Cδ) ^ 2) * ‖q‖ ^ 2 := by rw [hA]
    rw [hAe]
    have hq0' : (0:ℝ) ≤ ‖q‖ ^ 2 := by positivity
    have h3 : Cε * ‖q‖ ^ 2 + (2 * Cδ * ‖q‖ ^ 2 + (240 + Cδ) ^ 2 * ‖q‖ ^ 2)
        ≤ (Cε + 2 * Cδ + (240 + Cδ) ^ 2) * ‖q‖ ^ 2 := by
      have h4 : Cε * ‖q‖ ^ 2 + (2 * Cδ) * ‖q‖ ^ 2
          + (240 + Cδ) ^ 2 * ‖q‖ ^ 2 = (Cε + 2 * Cδ + (240 + Cδ) ^ 2) * ‖q‖ ^ 2 := by ring
      nlinarith [h4]
    have h5 : ‖X ^ 2‖ ≤ (240 + Cδ) ^ 2 * ‖q‖ ^ 2 := b2
    linarith [a, b1, h3, h5]
  have g2 : ‖-1008 * q * X + 2 * X * ε - 504 * q * X ^ 2 + X ^ 2 * ε‖ ≤ B * ‖q‖ ^ 2 := by
    have b1 : ‖(-1008 : ℂ) * q * X‖ ≤ 1008 * (240 + Cδ) * ‖q‖ ^ 2 := by
      calc ‖(-1008 : ℂ) * q * X‖ = 1008 * ‖q‖ * ‖X‖ := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
        _ ≤ 1008 * ‖q‖ * ((240 + Cδ) * ‖q‖) := by gcongr
        _ ≤ 1008 * (240 + Cδ) * ‖q‖ ^ 2 := by
            rw [show 1008 * ‖q‖ * ((240 + Cδ) * ‖q‖) = 1008 * (240 + Cδ) * ‖q‖ ^ 2 by ring]
    have b2 : ‖(2 : ℂ) * X * ε‖ ≤ 2 * (240 + Cδ) * Cε * ‖q‖ ^ 2 := by
      calc ‖(2 : ℂ) * X * ε‖ = 2 * ‖X‖ * ‖ε‖ := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * ((240 + Cδ) * ‖q‖) * (Cε * ‖q‖ ^ 2) := by gcongr
        _ ≤ 2 * (240 + Cδ) * Cε * ‖q‖ ^ 2 := by
            rw [show 2 * ((240 + Cδ) * ‖q‖) * (Cε * ‖q‖ ^ 2)
                = 2 * (240 + Cδ) * Cε * ‖q‖ ^ 3 by ring]
            exact mul3_le_mul3 (by positivity : (0:ℝ) ≤ 2 * (240 + Cδ)) hCε.le
              (q3_le_q2 hq0 hq1)
    have b3 : ‖(504 : ℂ) * q * X ^ 2‖ ≤ 504 * (240 + Cδ) ^ 2 * ‖q‖ ^ 2 := by
      calc ‖(504 : ℂ) * q * X ^ 2‖ = 504 * ‖q‖ * ‖X‖ ^ 2 := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
        _ ≤ 504 * ‖q‖ * ((240 + Cδ) * ‖q‖) ^ 2 := by gcongr
        _ ≤ 504 * (240 + Cδ) ^ 2 * ‖q‖ ^ 2 := by
            rw [show 504 * ‖q‖ * ((240 + Cδ) * ‖q‖) ^ 2
                = 504 * (240 + Cδ) ^ 2 * ‖q‖ ^ 3 by ring]
            exact mul3_le_mul3 (by norm_num : (0:ℝ) ≤ 504) (pow_nonneg h243 2)
              (q3_le_q2 hq0 hq1)
    have b4 : ‖X ^ 2 * ε‖ ≤ (240 + Cδ) ^ 2 * Cε * ‖q‖ ^ 2 := by
      calc ‖X ^ 2 * ε‖ = ‖X‖ ^ 2 * ‖ε‖ := by rw [norm_mul, norm_pow]
        _ ≤ ((240 + Cδ) * ‖q‖) ^ 2 * (Cε * ‖q‖ ^ 2) := by gcongr
        _ ≤ (240 + Cδ) ^ 2 * Cε * ‖q‖ ^ 2 := by
            rw [show ((240 + Cδ) * ‖q‖) ^ 2 * (Cε * ‖q‖ ^ 2)
                = (240 + Cδ) ^ 2 * Cε * ‖q‖ ^ 4 by ring]
            exact mul3_le_mul3 (pow_nonneg h243 2) hCε.le (q4_le_q2 hq0 hq1)
    have a1 := norm_add_le ((-1008 : ℂ) * q * X + (2 : ℂ) * X * ε - (504 : ℂ) * q * X ^ 2)
      (X ^ 2 * ε)
    have a2 := norm_sub_le ((-1008 : ℂ) * q * X + (2 : ℂ) * X * ε) ((504 : ℂ) * q * X ^ 2)
    have a3 := norm_add_le ((-1008 : ℂ) * q * X) ((2 : ℂ) * X * ε)
    have hBmax : B * ‖q‖ ^ 2 = (1008 * (240 + Cδ) + 2 * (240 + Cδ) * Cε
        + 504 * (240 + Cδ) ^ 2 + (240 + Cδ) ^ 2 * Cε) * ‖q‖ ^ 2 := by rw [hB]
    rw [hBmax]
    nlinarith [a1, a2, a3, b1, b2, b3, b4, hq0, hq2, h243]
  calc ‖Compact.dE14 z‖
      = ‖(ε + 2 * δ + X ^ 2) + (-1008 * q * X + 2 * X * ε - 504 * q * X ^ 2 + X ^ 2 * ε)‖ := by
        rw [hid]
    _ ≤ ‖ε + 2 * δ + X ^ 2‖ + ‖-1008 * q * X + 2 * X * ε - 504 * q * X ^ 2 + X ^ 2 * ε‖ :=
        norm_add_le _ _
    _ ≤ A * ‖q‖ ^ 2 + B * ‖q‖ ^ 2 := add_le_add g1 g2
    _ ≤ (A + B + 1) * ‖Ept z‖ ^ 4 := by
        have hq4 : ‖Ept z‖ ^ 4 = ‖q‖ ^ 2 := hqE.symm
        rw [hq4]
        have h0 : (0:ℝ) ≤ ‖q‖ ^ 2 := by positivity
        nlinarith [h0]

/-- `E₁₀(z) = 1 - 264 q(z) + O(‖q(z)‖²)`: `dE10 = O(‖q‖²)`. -/
private lemma dE10_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dE10 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨Cδ, hCδ, hδ⟩ := E4Fun_two_term
  obtain ⟨Cε, hCε, hε⟩ := E6Fun_two_term
  set A := Cε + Cδ with hA
  set B := 120960 + 240 * Cε + 504 * Cδ + Cδ * Cε with hB
  refine ⟨A + B + 1, by positivity, fun z hz => ?_⟩
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_q_le_one hz
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have hq3 : ‖qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hq4 : ‖qParamFun z‖ ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
  set q := qParamFun z with hq
  set δ := E4Fun z - 1 - 240 * q with hδd
  set ε := E6Fun z - 1 + 504 * q with hεd
  have hδb : ‖δ‖ ≤ Cδ * ‖q‖ ^ 2 := by rw [hδd, hq]; exact hδ z hz
  have hεb : ‖ε‖ ≤ Cε * ‖q‖ ^ 2 := by rw [hεd, hq]; exact hε z hz
  have hE4 : E4Fun z = 1 + 240 * q + δ := by rw [hδd]; ring
  have hE6 : E6Fun z = 1 - 504 * q + ε := by rw [hεd]; ring
  have hid : Compact.dE10 z
      = (ε + δ) + (-(120960 : ℂ) * q ^ 2 + (240 : ℂ) * q * ε - (504 : ℂ) * q * δ + δ * ε) := by
    have hE10 : E10Fun z = E4Fun z * E6Fun z := rfl
    have href : Compact.E10ref z = 1 - 264 * q := by
      rw [Compact.E10ref, hq, qParamFun_eq_Ept_sq]
    rw [Compact.dE10, href, hE10, hE4, hE6]
    ring
  have hqE : ‖q‖ ^ 2 = ‖Ept z‖ ^ 4 := by rw [hq, norm_q_eq]; ring
  have g1 : ‖ε + δ‖ ≤ A * ‖q‖ ^ 2 := by
    have a := norm_add_le ε δ
    have h2 : ‖ε + δ‖ ≤ (Cε + Cδ) * ‖q‖ ^ 2 := by
      have h3 := add_mul_le_mul (le_refl (Cε + Cδ)) (by positivity : (0:ℝ) ≤ ‖q‖ ^ 2)
      linarith [a, hεb, hδb, h3]
    have hAe : A * ‖q‖ ^ 2 = (Cε + Cδ) * ‖q‖ ^ 2 := by rw [hA]
    rw [hAe]
    exact h2
  have g2 : ‖-(120960 : ℂ) * q ^ 2 + (240 : ℂ) * q * ε - (504 : ℂ) * q * δ + δ * ε‖
      ≤ B * ‖q‖ ^ 2 := by
    have b1 : ‖(-(120960 : ℂ) * q ^ 2)‖ ≤ 120960 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
    have b2 : ‖(240 : ℂ) * q * ε‖ ≤ 240 * Cε * ‖q‖ ^ 2 := by
      calc ‖(240 : ℂ) * q * ε‖ = 240 * ‖q‖ * ‖ε‖ := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 240 * ‖q‖ * (Cε * ‖q‖ ^ 2) := by gcongr
        _ ≤ 240 * Cε * ‖q‖ ^ 2 := by
            rw [show 240 * ‖q‖ * (Cε * ‖q‖ ^ 2) = 240 * Cε * ‖q‖ ^ 3 by ring]
            exact mul3_le_mul3 (by norm_num : (0:ℝ) ≤ 240) hCε.le (q3_le_q2 hq0 hq1)
    have b3 : ‖(504 : ℂ) * q * δ‖ ≤ 504 * Cδ * ‖q‖ ^ 2 := by
      calc ‖(504 : ℂ) * q * δ‖ = 504 * ‖q‖ * ‖δ‖ := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 504 * ‖q‖ * (Cδ * ‖q‖ ^ 2) := by gcongr
        _ ≤ 504 * Cδ * ‖q‖ ^ 2 := by
            rw [show 504 * ‖q‖ * (Cδ * ‖q‖ ^ 2) = 504 * Cδ * ‖q‖ ^ 3 by ring]
            exact mul3_le_mul3 (by norm_num : (0:ℝ) ≤ 504) hCδ.le (q3_le_q2 hq0 hq1)
    have b4 : ‖δ * ε‖ ≤ Cδ * Cε * ‖q‖ ^ 2 := by
      calc ‖δ * ε‖ = ‖δ‖ * ‖ε‖ := by rw [norm_mul]
        _ ≤ (Cδ * ‖q‖ ^ 2) * (Cε * ‖q‖ ^ 2) := by gcongr
        _ ≤ Cδ * Cε * ‖q‖ ^ 2 := by
            rw [show (Cδ * ‖q‖ ^ 2) * (Cε * ‖q‖ ^ 2) = Cδ * Cε * ‖q‖ ^ 4 by ring]
            exact mul3_le_mul3 hCδ.le hCε.le (q4_le_q2 hq0 hq1)
    have a1 := norm_add_le (-(120960 : ℂ) * q ^ 2 + (240 : ℂ) * q * ε - (504 : ℂ) * q * δ) (δ * ε)
    have a2 := norm_sub_le (-(120960 : ℂ) * q ^ 2 + (240 : ℂ) * q * ε) ((504 : ℂ) * q * δ)
    have a3 := norm_add_le (-(120960 : ℂ) * q ^ 2) ((240 : ℂ) * q * ε)
    have hBmax : B * ‖q‖ ^ 2 = (120960 + 240 * Cε + 504 * Cδ + Cδ * Cε) * ‖q‖ ^ 2 := by rw [hB]
    rw [hBmax]
    nlinarith [a1, a2, a3, b1, b2, b3, b4, hq0, hq2]
  calc ‖Compact.dE10 z‖
      = ‖(ε + δ) + (-(120960 : ℂ) * q ^ 2 + (240 : ℂ) * q * ε - (504 : ℂ) * q * δ + δ * ε)‖ := by
        rw [hid]
    _ ≤ ‖ε + δ‖ + ‖-(120960 : ℂ) * q ^ 2 + (240 : ℂ) * q * ε - (504 : ℂ) * q * δ + δ * ε‖ :=
        norm_add_le _ _
    _ ≤ A * ‖q‖ ^ 2 + B * ‖q‖ ^ 2 := add_le_add g1 g2
    _ ≤ (A + B + 1) * ‖Ept z‖ ^ 4 := by
        rw [hqE]
        have h0 : (0:ℝ) ≤ ‖q‖ ^ 2 := by positivity
        nlinarith [h0]

/-! ## Boundedness of the `z`-atoms -/

/-- `‖E₁₄(z)‖ ≤ C` for `1 ≤ Im z`. -/
private lemma E14_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖E14Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := dE14_bound
  refine ⟨C + 25, by positivity, fun z hz => ?_⟩
  have he1 : ‖Ept z‖ ≤ 1 := KF24.norm_Ept_le_one' hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
  have he4 : ‖Ept z‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
  have h1 : ‖Compact.dE14 z‖ ≤ C := by
    have hh := h z hz
    have h2 : C * ‖Ept z‖ ^ 4 ≤ C := mul_le_of_le_one_right hC.le he4
    linarith [hh, h2]
  have h2 : ‖Compact.E14ref z‖ ≤ 25 := by
    rw [Compact.E14ref]
    calc ‖(1:ℂ) - 24 * Ept z ^ 2‖ ≤ 1 + ‖(24:ℂ) * Ept z ^ 2‖ := by
          have hh := norm_sub_le (1:ℂ) ((24:ℂ) * Ept z ^ 2)
          simpa only [norm_one] using hh
      _ = 1 + 24 * ‖(Ept z) ^ 2‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
      _ ≤ 1 + 24 := by
          have h3 : ‖(Ept z) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact he2
          linarith
      _ ≤ 25 := by norm_num
  have hsplit : E14Fun z = Compact.dE14 z + Compact.E14ref z := by rw [Compact.dE14]; ring
  rw [hsplit]
  have hsum := norm_add_le (Compact.dE14 z) (Compact.E14ref z)
  linarith [hsum, h1, h2]

/-- `‖E₁₀(z)‖ ≤ C` for `1 ≤ Im z`. -/
private lemma E10_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖E10Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := dE10_bound
  refine ⟨C + 265, by positivity, fun z hz => ?_⟩
  have he1 : ‖Ept z‖ ≤ 1 := KF24.norm_Ept_le_one' hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
  have he4 : ‖Ept z‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
  have h1 : ‖Compact.dE10 z‖ ≤ C := by
    have hh := h z hz
    have h2 : C * ‖Ept z‖ ^ 4 ≤ C := mul_le_of_le_one_right hC.le he4
    linarith [hh, h2]
  have h2 : ‖Compact.E10ref z‖ ≤ 265 := by
    rw [Compact.E10ref]
    calc ‖(1:ℂ) - 264 * Ept z ^ 2‖ ≤ 1 + ‖(264:ℂ) * Ept z ^ 2‖ := by
          have hh := norm_sub_le (1:ℂ) ((264:ℂ) * Ept z ^ 2)
          simpa only [norm_one] using hh
      _ = 1 + 264 * ‖(Ept z) ^ 2‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
      _ ≤ 1 + 264 := by
          have h3 : ‖(Ept z) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact he2
          linarith
      _ ≤ 265 := by norm_num
  have hsplit : E10Fun z = Compact.dE10 z + Compact.E10ref z := by rw [Compact.dE10]; ring
  rw [hsplit]
  have hsum := norm_add_le (Compact.dE10 z) (Compact.E10ref z)
  linarith [hsum, h1, h2]

/-- `‖Sinvref τ z‖ ≤ C` on the funnel tail. -/
private lemma Sinvref_bound : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.Sinvref τ z‖ ≤ C := by
  refine ⟨1 + 27 / 4 + 720, by norm_num, fun τ z t hτ ht hz => ?_⟩
  have ht3 : (3:ℝ) ≤ t := by linarith [hτ.2]
  have he : ‖Ept z‖ ≤ 1 := by
    rw [norm_Ept_axis hz]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, ht3])
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have hj := KF24.norm_j_funnel τ hτ
  have h1 : ‖jInvariantFun τ - 720‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) + 720 := by
    have a := norm_sub_le (jInvariantFun τ) (720 : ℂ)
    rw [show ‖(720:ℂ)‖ = 720 by norm_num] at a
    linarith
  have h2 : Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) := by
    rw [norm_Ept_axis hz, show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, ht]
  have hkey : ‖jInvariantFun τ - 720‖ * ‖Ept z‖ ^ 2 ≤ 27 / 4 + 720 := by
    calc ‖jInvariantFun τ - 720‖ * ‖Ept z‖ ^ 2
        ≤ ((27 / 4) * Real.exp (2 * Real.pi * τ.im) + 720) * ‖Ept z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (27 / 4) * (Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2)
            + 720 * ‖Ept z‖ ^ 2 := by ring
      _ ≤ (27 / 4) * Real.exp (-(2 * Real.pi)) + 720 * 1 := by
          have h3 : (0:ℝ) ≤ 27 / 4 := by norm_num
          nlinarith [h2, he2, h3]
      _ ≤ 27 / 4 + 720 := by
          have h4 : Real.exp (-(2 * Real.pi)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
          nlinarith [h4]
  rw [Compact.Sinvref]
  calc ‖(1:ℂ) + (jInvariantFun τ - 720) * Ept z ^ 2‖
      ≤ 1 + ‖(jInvariantFun τ - 720) * Ept z ^ 2‖ := by
        have hh := norm_add_le (1:ℂ) ((jInvariantFun τ - 720) * Ept z ^ 2)
        simpa only [norm_one] using hh
    _ = 1 + ‖jInvariantFun τ - 720‖ * ‖Ept z‖ ^ 2 := by rw [norm_mul, norm_pow]
    _ ≤ 1 + (27 / 4 + 720) := by linarith [hkey]
    _ = 1 + 27 / 4 + 720 := by norm_num

/-- `‖Dref z‖ ≤ (‖Ept z‖²)⁻¹ + 24`. -/
private lemma Dref_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.Dref z‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 := by
  refine ⟨25, by norm_num, fun z hz => ?_⟩
  rw [Compact.Dref, Compact.einv2]
  calc ‖(Ept z)⁻¹ ^ 2 + 24‖ ≤ ‖(Ept z)⁻¹ ^ 2‖ + ‖(24:ℂ)‖ := norm_add_le _ _
    _ = (‖Ept z‖ ^ 2)⁻¹ + 24 := by
        rw [norm_pow, norm_inv, inv_pow, show ‖(24:ℂ)‖ = 24 by norm_num]

/-- `‖(Δ z)⁻¹‖ ≤ (‖Ept z‖²)⁻¹ + K`. -/
private lemma invDelta_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖(DeltaFun z)⁻¹‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + K := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_invDelta
  refine ⟨24 + C, by positivity, fun z hz => ?_⟩
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (KF24.norm_Ept_le_one' hz)
  have h1 : ‖Compact.dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 := by
    have hh := h z hz
    have hgoal : Compact.dDelta z = (DeltaFun z)⁻¹ - ((Ept z)⁻¹ ^ 2 + 24) := by
      rw [Compact.dDelta, Compact.Dref, Compact.einv2]
    rw [hgoal]
    exact hh
  have hd : ‖Compact.dDelta z‖ ≤ C := by
    have hX : C * ‖Ept z‖ ^ 2 ≤ C := mul_le_of_le_one_right hC.le he2
    linarith [h1, hX]
  have hD : (DeltaFun z)⁻¹ = Compact.Dref z + Compact.dDelta z := by rw [Compact.dDelta]; ring
  obtain ⟨-, -, hDrf⟩ := Dref_bound
  have hDr : ‖Compact.Dref z‖ ≤ (‖Ept z‖ ^ 2)⁻¹ + 24 := hDrf z hz
  rw [hD]
  have := norm_add_le (Compact.Dref z) (Compact.dDelta z)
  linarith [this, hDr, hd]

/-- `‖W(z)‖ ≤ C` for `1 ≤ Im z`. -/
private lemma W_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖WFun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_W_second
  refine ⟨C + 33, by positivity, fun z hz => ?_⟩
  have he := KF24.norm_Ept_le_one' hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have h1 : ‖WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2)‖ ≤ C := by
    have hh := h z hz
    have h2 : C * ‖Ept z‖ ^ 3 ≤ C := mul_le_of_le_one_right hC.le he3
    linarith [hh, h2]
  have hWref : ‖(1:ℂ) - 8 * Ept z + 24 * (Ept z) ^ 2‖ ≤ 33 := by
    calc ‖(1:ℂ) - 8 * Ept z + 24 * (Ept z) ^ 2‖
        ≤ ‖(1:ℂ) - 8 * Ept z‖ + ‖(24:ℂ) * (Ept z) ^ 2‖ := norm_add_le _ _
      _ ≤ (1 + 8 * ‖Ept z‖) + 24 * ‖Ept z‖ ^ 2 := by
          have b := norm_sub_le (1:ℂ) ((8:ℂ) * Ept z)
          have h8 : ‖(8:ℂ) * Ept z‖ = 8 * ‖Ept z‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
          have h24 : ‖(24:ℂ) * (Ept z) ^ 2‖ = 24 * ‖Ept z‖ ^ 2 := by
            simp only [norm_mul, norm_pow, Complex.norm_ofNat]
          have hb1 : ‖(1:ℂ) - 8 * Ept z‖ ≤ 1 + 8 * ‖Ept z‖ := by
            rw [h8] at b
            simpa only [norm_one] using b
          rw [h24]
          linarith [hb1]
      _ ≤ 33 := by nlinarith [he, he2]
  have hsplit : WFun z = (WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2))
      + (1 - 8 * Ept z + 24 * (Ept z) ^ 2) := by ring
  rw [hsplit]
  have hsum := norm_add_le (WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2))
    (1 - 8 * Ept z + 24 * (Ept z) ^ 2)
  linarith [hsum, h1, hWref]

/-- `‖U(z)² - V(z)²‖ ≤ C` for `1 ≤ Im z`. -/
private lemma D2_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_D_second
  refine ⟨C + 161, by positivity, fun z hz => ?_⟩
  have he := KF24.norm_Ept_le_one' hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have h1 : ‖UFun z ^ 2 - VFun z ^ 2 - (1 + 16 * Ept z - 144 * (Ept z) ^ 2)‖ ≤ C := by
    have hh := h z hz
    have h2 : C * ‖Ept z‖ ^ 3 ≤ C := mul_le_of_le_one_right hC.le he3
    linarith [hh, h2]
  have hD2ref : ‖(1:ℂ) + 16 * Ept z - 144 * (Ept z) ^ 2‖ ≤ 161 := by
    calc ‖(1:ℂ) + 16 * Ept z - 144 * (Ept z) ^ 2‖
        ≤ ‖(1:ℂ) + 16 * Ept z‖ + ‖(144:ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
      _ ≤ (1 + 16 * ‖Ept z‖) + 144 * ‖Ept z‖ ^ 2 := by
          have b := norm_add_le (1:ℂ) ((16:ℂ) * Ept z)
          have h16 : ‖(16:ℂ) * Ept z‖ = 16 * ‖Ept z‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
          have h144 : ‖(144:ℂ) * (Ept z) ^ 2‖ = 144 * ‖Ept z‖ ^ 2 := by
            simp only [norm_mul, norm_pow, Complex.norm_ofNat]
          have hb1 : ‖(1:ℂ) + 16 * Ept z‖ ≤ 1 + 16 * ‖Ept z‖ := by
            rw [h16] at b
            simpa only [norm_one] using b
          rw [h144]
          linarith [hb1]
      _ ≤ 161 := by nlinarith [he, he2]
  have hsplit : UFun z ^ 2 - VFun z ^ 2 = (UFun z ^ 2 - VFun z ^ 2
      - (1 + 16 * Ept z - 144 * (Ept z) ^ 2)) + (1 + 16 * Ept z - 144 * (Ept z) ^ 2) := by ring
  rw [hsplit]
  have hsum := norm_add_le (UFun z ^ 2 - VFun z ^ 2 - (1 + 16 * Ept z - 144 * (Ept z) ^ 2))
    (1 + 16 * Ept z - 144 * (Ept z) ^ 2)
  linarith [hsum, h1, hD2ref]

private lemma dDelta_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_invDelta
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  have heq : Compact.dDelta z = (DeltaFun z)⁻¹ - ((Ept z)⁻¹ ^ 2 + 24) := by
    rw [Compact.dDelta, Compact.Dref, Compact.einv2]
  rw [heq]
  exact hh

/-- `‖dW z‖ ≤ C ‖Ept z‖³`. -/
private lemma dW_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dW z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_W_second
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  have heq : Compact.dW z = WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2) := by
    rw [Compact.dW, Compact.Wref]
  rw [heq]
  exact hh

/-- `‖dD2 z‖ ≤ C ‖Ept z‖³`. -/
private lemma dD2_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dD2 z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_D_second
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  have heq : Compact.dD2 z = UFun z ^ 2 - VFun z ^ 2
      - (1 + 16 * Ept z - 144 * (Ept z) ^ 2) := by
    rw [Compact.dD2, Compact.D2ref]
  rw [heq]
  exact hh

/-- `‖dL z‖ ≤ C ‖Ept z‖³`. -/
private lemma dL_bound (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dL ℓ z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Compact.cuspC_spec ℓ
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  have heq : Compact.dL ℓ z = ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ
      - 8 * Ept z + 12 * (Ept z) ^ 2) := by
    rw [Compact.dL, Compact.Lref, Compact.Xc]
  rw [heq]
  exact hh

/-- `‖L(z)‖ ≤ C (1 + ‖z‖)` for `1 ≤ Im z`. -/
private lemma L_bound (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨C, hC, h⟩ := (Work.Residues.LogLambdaBound ℓ).1
  refine ⟨C + Real.pi, by positivity, fun z hz => ?_⟩
  have hh := h z hz
  have h1 : ‖ℓ.L z‖ ≤ C + Real.pi * ‖(z : ℂ)‖ := by
    have h2 := norm_add_le (ℓ.L z - (Real.pi : ℂ) * Complex.I * (z : ℂ))
      ((Real.pi : ℂ) * Complex.I * (z : ℂ))
    have h3 : ℓ.L z - (Real.pi : ℂ) * Complex.I * (z : ℂ) + (Real.pi : ℂ) * Complex.I * (z : ℂ)
        = ℓ.L z := by ring
    rw [h3] at h2
    have h4 : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ = Real.pi * ‖(z : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_I, mul_one]
    linarith [h2, hh, h4]
  calc ‖ℓ.L z‖ ≤ C + Real.pi * ‖(z : ℂ)‖ := h1
    _ ≤ (C + Real.pi) * (1 + ‖(z : ℂ)‖) := by
        have h5 : (0:ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
        nlinarith [Real.pi_pos, hC.le]

/-- `‖Lref z‖ ≤ C (1 + ‖z‖)` for `1 ≤ Im z`. -/
private lemma Lref_bound (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.Lref ℓ z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  refine ⟨Real.pi + ‖Compact.cuspC ℓ‖ + 21, by positivity, fun z hz => ?_⟩
  have he := KF24.norm_Ept_le_one' hz
  have hX := Compact.kaux_norm_Xc_le ℓ z
  rw [Compact.Lref]
  calc ‖Compact.Xc ℓ z - 8 * Ept z + 12 * Ept z ^ 2‖
      ≤ ‖Compact.Xc ℓ z - 8 * Ept z‖ + ‖(12:ℂ) * Ept z ^ 2‖ := norm_add_le _ _
    _ ≤ (‖Compact.Xc ℓ z‖ + 8) + 12 := by
        have b := norm_sub_le (Compact.Xc ℓ z) ((8:ℂ) * Ept z)
        have h8 : ‖(8:ℂ) * Ept z‖ = 8 * ‖Ept z‖ := by simp only [norm_mul, Complex.norm_ofNat, norm_neg]
        have h12 : ‖(12:ℂ) * Ept z ^ 2‖ = 12 * ‖Ept z‖ ^ 2 := by
          simp only [norm_mul, norm_pow, Complex.norm_ofNat]
        rw [h8] at b
        rw [h12]
        have he2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
        linarith
    _ ≤ (Real.pi + ‖Compact.cuspC ℓ‖ + 21) * (1 + ‖(z : ℂ)‖) := by
        have h0 : (0:ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
        have h1 : (1:ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith
        have h2 : ‖Compact.Xc ℓ z‖ ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := hX
        nlinarith [h2, Real.pi_pos, norm_nonneg (Compact.cuspC ℓ), h0, h1]

/-! ## The deviation `dSinv` on the funnel -/

/-- `‖dSinv τ z‖ ≤ C (e^{-4πt} + e^{-4π(t - Im τ)})` uniformly on the funnel. -/
private lemma dSinv_bound :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.dSinv τ z‖ ≤ C * (scale τ) ^ N
        * (Real.exp (-(4 * Real.pi * t))
            + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)) := by
  obtain ⟨Cμ, hCμ, hμ⟩ := Work.Residues.DeltaExpansion
  obtain ⟨Cν, hCν, hν⟩ := E4cube_second
  set Kc : ℝ := 27 / 4 + 720 with hKc
  set CL := Cν + Cμ * Kc + Kc * (720 + Cν) + (1 + Cμ) * Kc ^ 2 with hCL
  refine ⟨48 * CL, 0, by positivity, le_refl 0, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have ht3 : (3:ℝ) ≤ t := by linarith [hτ.2]
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_q_le_one hz1
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  set q := qParamFun z with hq
  set μ := DeltaFun z - q with hμd
  set ν := E4Fun z ^ 3 - 1 - 720 * q with hνd
  have hqe : q = Ept z ^ 2 := by rw [hq]; exact qParamFun_eq_Ept_sq z
  have hμb : ‖μ‖ ≤ Cμ * ‖q‖ ^ 2 := by
    have h1 : ‖DeltaFun z - q‖ ≤ Cμ * ‖q‖ ^ 2 := by
      have h8 : ‖DeltaFun z - Ept z ^ 2‖ ≤ Cμ * ‖Ept z‖ ^ 4 := hμ z hz1
      have h9 : ‖Ept z‖ ^ 4 = ‖q‖ ^ 2 := by rw [hqe, norm_pow]; ring
      rw [h9] at h8
      rw [← hqe] at h8
      exact h8
    rw [hμd]
    exact h1
  have hνb : ‖ν‖ ≤ Cν * ‖q‖ ^ 2 := by rw [hνd, hq]; exact hν z hz1
  have hj := KF24.norm_j_funnel τ hτ
  set M := Real.exp (2 * Real.pi * τ.im) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hM1 : (1:ℝ) ≤ M := by
    rw [hM, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hJM : (27 / 4) * M ≤ Kc * M := by
    rw [hKc]; nlinarith [hM0]
  have hJ'M : (27 / 4) * M + 720 ≤ Kc * M := by
    rw [hKc]
    nlinarith [hM1, hM0]
  have hJ : ‖jInvariantFun τ‖ ≤ Kc * M := le_trans hj hJM
  have hJ' : ‖jInvariantFun τ - 720‖ ≤ Kc * M := by
    have a := norm_sub_le (jInvariantFun τ) (720 : ℂ)
    rw [show ‖(720:ℂ)‖ = 720 by norm_num] at a
    rw [hKc]
    nlinarith [a, hj, hM1, hM0]
  have hShne : Compact.Sh τ z ≠ 0 := by
    have h := funnel_Sh_ge τ z t hτ ht hz
    intro h0
    rw [h0, norm_zero] at h
    norm_num at h
  have hSh16 : (1 / 16 : ℝ) ≤ ‖Compact.Sh τ z‖ := funnel_Sh_ge τ z t hτ ht hz
  have hid : 1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z
      = -ν + μ * jInvariantFun τ - (jInvariantFun τ - 720) * q * (720 * q + ν)
        + (jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ
        + (jInvariantFun τ - 720) * q * μ * jInvariantFun τ := by
    have hSh : Compact.Sh τ z = E4Fun z ^ 3 - DeltaFun z * jInvariantFun τ := rfl
    have hE4c : E4Fun z ^ 3 = 1 + 720 * q + ν := by rw [hνd]; ring
    have hΔ : DeltaFun z = q + μ := by rw [hμd]; ring
    rw [hSh, hE4c, hΔ]; ring
  have hkey : Compact.dSinv τ z
      = (1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z) / Compact.Sh τ z := by
    rw [Compact.dSinv, Compact.Sinvref, show q = Ept z ^ 2 from hqe]
    field_simp
    ring
  -- monomial bounds
  have hKc0 : (0:ℝ) ≤ Kc := by rw [hKc]; norm_num
  have b1 : ‖ν‖ ≤ Cν * ‖q‖ ^ 2 := hνb
  have b2 : ‖μ * jInvariantFun τ‖ ≤ Cμ * Kc * M * ‖q‖ ^ 2 := by
    rw [norm_mul]
    calc ‖μ‖ * ‖jInvariantFun τ‖ ≤ (Cμ * ‖q‖ ^ 2) * (Kc * M) :=
          mul_le_mul hμb hJ (norm_nonneg _) (by positivity)
      _ = Cμ * Kc * M * ‖q‖ ^ 2 := by ring
  have b3 : ‖(jInvariantFun τ - 720) * q * (720 * q + ν)‖ ≤ Kc * M * (720 + Cν) * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_mul]
    have h1 : ‖(720:ℂ) * q + ν‖ ≤ 720 * ‖q‖ + Cν * ‖q‖ ^ 2 := by
      have a := norm_add_le ((720:ℂ) * q) ν
      rw [norm_mul, Complex.norm_ofNat] at a
      linarith [a, hνb]
    calc ‖jInvariantFun τ - 720‖ * ‖q‖ * ‖(720:ℂ) * q + ν‖
        ≤ (Kc * M) * ‖q‖ * (720 * ‖q‖ + Cν * ‖q‖ ^ 2) :=
          mul_le_mul (mul_le_mul hJ' (le_refl _) (norm_nonneg _) (by positivity)) h1 (by positivity)
            (by positivity)
      _ = Kc * M * 720 * ‖q‖ ^ 2 + Kc * M * Cν * ‖q‖ ^ 3 := by ring
      _ ≤ Kc * M * 720 * ‖q‖ ^ 2 + Kc * M * Cν * ‖q‖ ^ 2 := by
          have hq32 : ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 := q3_le_q2 hq0 hq1
          have h1 : Kc * M * Cν * ‖q‖ ^ 3 ≤ Kc * M * Cν * ‖q‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hq32 (by positivity)
          linarith [h1]
      _ = Kc * M * (720 + Cν) * ‖q‖ ^ 2 := by ring
  have b4 : ‖(jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ‖ ≤ Kc ^ 2 * M ^ 2 * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖jInvariantFun τ - 720‖ * ‖q‖ ^ 2 * ‖jInvariantFun τ‖
        ≤ (Kc * M) * ‖q‖ ^ 2 * (Kc * M) :=
          mul_le_mul (mul_le_mul hJ' (le_refl _) (by positivity) (by positivity)) hJ (by positivity)
            (by positivity)
      _ = Kc ^ 2 * M ^ 2 * ‖q‖ ^ 2 := by ring
  have b5 : ‖(jInvariantFun τ - 720) * q * μ * jInvariantFun τ‖
      ≤ Cμ * Kc ^ 2 * M ^ 2 * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖jInvariantFun τ - 720‖ * ‖q‖ * ‖μ‖ * ‖jInvariantFun τ‖
        ≤ (Kc * M) * ‖q‖ * (Cμ * ‖q‖ ^ 2) * (Kc * M) :=
          mul_le_mul (mul_le_mul (mul_le_mul hJ' (le_refl _) (norm_nonneg _) (by positivity)) hμb
              (by positivity) (by positivity)) hJ (by positivity) (by positivity)
      _ = Cμ * Kc ^ 2 * M ^ 2 * ‖q‖ ^ 3 := by ring
      _ ≤ Cμ * Kc ^ 2 * M ^ 2 * ‖q‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (q3_le_q2 hq0 hq1) (by positivity)
  have hnum : ‖1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z‖
      ≤ 3 * CL * (1 + M ^ 2) * ‖q‖ ^ 2 := by
    have hsum : ‖1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z‖
        ≤ ‖ν‖ + ‖μ * jInvariantFun τ‖ + ‖(jInvariantFun τ - 720) * q * (720 * q + ν)‖
          + ‖(jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ‖
          + ‖(jInvariantFun τ - 720) * q * μ * jInvariantFun τ‖ := by
      rw [hid]
      have t1 := norm_sub_le (-ν + μ * jInvariantFun τ)
        ((jInvariantFun τ - 720) * q * (720 * q + ν))
      have t2 := norm_add_le ((-ν + μ * jInvariantFun τ)
        - (jInvariantFun τ - 720) * q * (720 * q + ν))
        ((jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ)
      have t3 := norm_add_le ((-ν + μ * jInvariantFun τ)
        - (jInvariantFun τ - 720) * q * (720 * q + ν)
        + (jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ)
        ((jInvariantFun τ - 720) * q * μ * jInvariantFun τ)
      have t4 := norm_add_le (-ν) (μ * jInvariantFun τ)
      rw [norm_neg] at t4
      linarith [t1, t2, t3, t4]
    have hmid : ‖ν‖ + ‖μ * jInvariantFun τ‖ + ‖(jInvariantFun τ - 720) * q * (720 * q + ν)‖
          + ‖(jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ‖
          + ‖(jInvariantFun τ - 720) * q * μ * jInvariantFun τ‖
        ≤ CL * (1 + M + M ^ 2) * ‖q‖ ^ 2 := by
      have hr : ‖ν‖ + ‖μ * jInvariantFun τ‖ + ‖(jInvariantFun τ - 720) * q * (720 * q + ν)‖
            + ‖(jInvariantFun τ - 720) * q ^ 2 * jInvariantFun τ‖
            + ‖(jInvariantFun τ - 720) * q * μ * jInvariantFun τ‖
          ≤ Cν * ‖q‖ ^ 2 + (Cμ * Kc * M) * ‖q‖ ^ 2
            + (Kc * M * (720 + Cν)) * ‖q‖ ^ 2 + (Kc ^ 2 * M ^ 2) * ‖q‖ ^ 2
            + (Cμ * Kc ^ 2 * M ^ 2) * ‖q‖ ^ 2 := by
        have h := add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5
        have hr' : Cν * ‖q‖ ^ 2 + (Cμ * Kc * M) * ‖q‖ ^ 2
            + (Kc * M * (720 + Cν)) * ‖q‖ ^ 2 + (Kc ^ 2 * M ^ 2) * ‖q‖ ^ 2
            + (Cμ * Kc ^ 2 * M ^ 2) * ‖q‖ ^ 2
            = (Cν + Cμ * Kc * M + Kc * M * (720 + Cν) + Kc ^ 2 * M ^ 2
                + Cμ * Kc ^ 2 * M ^ 2) * ‖q‖ ^ 2 := by ring
        linarith [h, hr']
      refine le_trans hr ?_
      have h1M : (1:ℝ) ≤ 1 + M + M ^ 2 := by nlinarith [hM0, sq_nonneg M]
      have hMle : M ≤ 1 + M + M ^ 2 := by nlinarith [hM0, sq_nonneg M]
      have hM2le : M ^ 2 ≤ 1 + M + M ^ 2 := by nlinarith [hM0]
      have hA : Cν ≤ Cν * (1 + M + M ^ 2) := le_mul_of_one_le_right hCν.le h1M
      have hB : Cμ * Kc * M ≤ Cμ * Kc * (1 + M + M ^ 2) :=
        mul_le_mul_of_nonneg_left hMle (by positivity)
      have hC : Kc * (720 + Cν) * M ≤ Kc * (720 + Cν) * (1 + M + M ^ 2) :=
        mul_le_mul_of_nonneg_left hMle (by positivity)
      have hD : (1 + Cμ) * Kc ^ 2 * M ^ 2 ≤ (1 + Cμ) * Kc ^ 2 * (1 + M + M ^ 2) :=
        mul_le_mul_of_nonneg_left hM2le (by positivity)
      have hCLexp : CL * (1 + M + M ^ 2)
          = Cν * (1 + M + M ^ 2) + Cμ * Kc * (1 + M + M ^ 2)
            + Kc * (720 + Cν) * (1 + M + M ^ 2)
            + (1 + Cμ) * Kc ^ 2 * (1 + M + M ^ 2) := by rw [hCL]; ring
      have hq0' : (0:ℝ) ≤ ‖q‖ ^ 2 := by positivity
      have i1 := mul_le_mul_of_nonneg_right hA hq0'
      have i2 := mul_le_mul_of_nonneg_right hB hq0'
      have i3 := mul_le_mul_of_nonneg_right hC hq0'
      have i4 := mul_le_mul_of_nonneg_right hD hq0'
      rw [hCLexp]
      nlinarith [i1, i2, i3, i4, hq0']
    have h3 : (1 + M + M ^ 2) ≤ 3 * (1 + M ^ 2) := by nlinarith [hM0, sq_nonneg M]
    have hCL0 : (0:ℝ) ≤ CL := by rw [hCL]; positivity
    have hq0' : (0:ℝ) ≤ ‖q‖ ^ 2 := by positivity
    have h4 : CL * (1 + M + M ^ 2) * ‖q‖ ^ 2 ≤ CL * (3 * (1 + M ^ 2)) * ‖q‖ ^ 2 := by
      have h5 : CL * (1 + M + M ^ 2) ≤ CL * (3 * (1 + M ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hCL0
      exact mul_le_mul_of_nonneg_right h5 hq0'
    linarith [hsum, hmid, h4]
  have hq2 : ‖q‖ ^ 2 = Real.exp (-(4 * Real.pi * t)) := by
    rw [hq, norm_q_eq, norm_Ept_axis hz]
    rw [show (Real.exp (-(Real.pi * t)) ^ 2) ^ 2 = Real.exp (-(Real.pi * t)) ^ 4 by ring,
      exp_pow_eq]
    congr 1
    ring
  have hMsq : M ^ 2 = Real.exp (4 * Real.pi * τ.im) := by
    rw [hM, sq, ← Real.exp_add]; congr 1; ring
  rw [hkey]
  have hnum' : ‖1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z‖
      ≤ 3 * CL * (1 + Real.exp (4 * Real.pi * τ.im)) * Real.exp (-(4 * Real.pi * t)) := by
    have h := hnum
    rw [hq2, hMsq] at h
    exact h
  have hdiv : ‖(1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z) / Compact.Sh τ z‖
      ≤ 16 * (3 * CL * (1 + Real.exp (4 * Real.pi * τ.im)) * Real.exp (-(4 * Real.pi * t))) := by
    rw [norm_div]
    have hpos : 0 < ‖Compact.Sh τ z‖ := lt_of_lt_of_le (by norm_num) hSh16
    have h1 : (‖Compact.Sh τ z‖)⁻¹ ≤ 16 := by
      rw [inv_le_iff_one_le_mul₀ hpos]; linarith
    calc ‖1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z‖ / ‖Compact.Sh τ z‖
        = ‖1 - Compact.Sh τ z - (jInvariantFun τ - 720) * q * Compact.Sh τ z‖
            * (‖Compact.Sh τ z‖)⁻¹ := by ring
      _ ≤ (3 * CL * (1 + Real.exp (4 * Real.pi * τ.im)) * Real.exp (-(4 * Real.pi * t))) * 16 :=
          mul_le_mul hnum' h1 (by positivity) (by positivity)
      _ = 16 * (3 * CL * (1 + Real.exp (4 * Real.pi * τ.im)) * Real.exp (-(4 * Real.pi * t))) := by
          ring
  refine le_trans hdiv ?_
  have hE : (0:ℝ) ≤ Real.exp (-(4 * Real.pi * t)) := (Real.exp_pos _).le
  have hF : (0:ℝ) ≤ Real.exp (4 * Real.pi * τ.im) := (Real.exp_pos _).le
  have hgoal : 16 * (3 * CL * (1 + Real.exp (4 * Real.pi * τ.im)) * Real.exp (-(4 * Real.pi * t)))
      = 48 * CL * (Real.exp (-(4 * Real.pi * t))
          + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)) := by ring
  rw [hgoal]
  have hsz : (scale τ) ^ (0:ℝ) = 1 := Real.rpow_zero _
  rw [hsz, mul_one]

/-! ## The coefficients of `R24` -/

/-- `‖R24_p0‖ ≤ C (scale τ)^N` on the funnel. -/
private lemma R24_p0_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Compact.R24_p0 ℓ τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨CP4, NP4, hCP4, hNP4, hP4⟩ := KF24.psi4E8_funnel ℓ
  obtain ⟨CP2, NP2, hCP2, hNP2, hP2⟩ := KF24.psi2E10_funnel ℓ
  obtain ⟨Cjs, Njs, hCjs, hNjs, hjs⟩ := KF24.j_psi_sub_funnel ℓ
  set N := max (max NP4 NP2) Njs with hN
  refine ⟨29568 * CP4 + 15744 * CP2 + 20570112 * 2 + 24 * Cjs + 27648 * (27 / 8), N,
    by positivity, by positivity, fun τ hτ => ?_⟩
  have hs4 : (scale τ) ^ NP4 ≤ (scale τ) ^ N :=
    scale_rpow_mono (le_trans (le_max_left _ _) (le_max_left _ _))
  have hs2 : (scale τ) ^ NP2 ≤ (scale τ) ^ N :=
    scale_rpow_mono (le_trans (le_max_right _ _) (le_max_left _ _))
  have hsj : (scale τ) ^ Njs ≤ (scale τ) ^ N := scale_rpow_mono (le_max_right _ _)
  have hN0 : (0:ℝ) ≤ N := by
    rw [hN]; exact le_trans hNP4 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN1 : (1:ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow hN0
  have hid : Compact.R24_p0 ℓ τ
      = (-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (15744 : ℂ) * (psi2 ℓ τ * E10Fun τ)
        - (20570112 : ℂ) * DeltaFun τ
        + (24 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
        + (27648 : ℂ) * (jInvariantFun τ * DeltaFun τ) := by
    rw [Compact.R24_p0]; ring
  rw [hid]
  have hE := KF24.norm_Delta_funnel τ hτ
  have hE1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ.2])
  have b1 : ‖(-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 29568 * CP4 * (scale τ) ^ N := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat]
    calc 29568 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 29568 * (CP4 * (scale τ) ^ NP4) :=
          mul_le_mul_of_nonneg_left (hP4 τ hτ) (by norm_num)
      _ ≤ 29568 * (CP4 * (scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs4 hCP4.le) (by norm_num)
      _ = 29568 * CP4 * (scale τ) ^ N := by ring
  have b2 : ‖(15744 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 15744 * CP2 * (scale τ) ^ N := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 15744 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 15744 * (CP2 * (scale τ) ^ NP2) :=
          mul_le_mul_of_nonneg_left (hP2 τ hτ) (by norm_num)
      _ ≤ 15744 * (CP2 * (scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2 hCP2.le) (by norm_num)
      _ = 15744 * CP2 * (scale τ) ^ N := by ring
  have b3 : ‖(20570112 : ℂ) * DeltaFun τ‖ ≤ 20570112 * 2 * (scale τ) ^ N := by
    rw [norm_mul, Complex.norm_ofNat]
    have h2 : 20570112 * ‖DeltaFun τ‖ ≤ 20570112 * 2 := by
      nlinarith [hE, hE1, show (0:ℝ) < 20570112 by norm_num]
    calc 20570112 * ‖DeltaFun τ‖ ≤ 20570112 * 2 := h2
      _ ≤ 20570112 * 2 * (scale τ) ^ N := le_mul_of_one_le_right (by norm_num) hN1
  have b4 : ‖(24 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
      ≤ 24 * Cjs * (scale τ) ^ N := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 24 * ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        ≤ 24 * (Cjs * (scale τ) ^ Njs) := mul_le_mul_of_nonneg_left (hjs τ hτ) (by norm_num)
      _ ≤ 24 * (Cjs * (scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsj hCjs.le) (by norm_num)
      _ = 24 * Cjs * (scale τ) ^ N := by ring
  have b5 : ‖(27648 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖ ≤ 27648 * (27 / 8) := by
    rw [norm_mul, Complex.norm_ofNat]
    have h := KF24.norm_j_mul_Delta_funnel τ hτ
    nlinarith [h]
  have t1 := norm_add_le ((-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (15744 : ℂ) * (psi2 ℓ τ * E10Fun τ)
      - (20570112 : ℂ) * DeltaFun τ
      + (24 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
      ((27648 : ℂ) * (jInvariantFun τ * DeltaFun τ))
  have t2 := norm_add_le ((-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (15744 : ℂ) * (psi2 ℓ τ * E10Fun τ)
      - (20570112 : ℂ) * DeltaFun τ)
      ((24 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
  have t3 := norm_sub_le ((-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (15744 : ℂ) * (psi2 ℓ τ * E10Fun τ))
      ((20570112 : ℂ) * DeltaFun τ)
  have t4 := norm_add_le ((-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ)) ((15744 : ℂ) * (psi2 ℓ τ * E10Fun τ))
  have hb5 : ‖(27648 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖ ≤ 27648 * (27 / 8) * (scale τ) ^ N :=
    le_trans b5 (le_mul_of_one_le_right (by norm_num) hN1)
  have hcomb : 29568 * CP4 * (scale τ) ^ N + 15744 * CP2 * (scale τ) ^ N
      + 20570112 * 2 * (scale τ) ^ N + 24 * Cjs * (scale τ) ^ N + 27648 * (27 / 8)
      ≤ (29568 * CP4 + 15744 * CP2 + 20570112 * 2 + 24 * Cjs + 27648 * (27 / 8))
        * (scale τ) ^ N := by
    have h : 27648 * (27 / 8) ≤ 27648 * (27 / 8) * (scale τ) ^ N :=
      le_mul_of_one_le_right (by norm_num) hN1
    have h2 : 29568 * CP4 * (scale τ) ^ N + 15744 * CP2 * (scale τ) ^ N
        + 20570112 * 2 * (scale τ) ^ N + 24 * Cjs * (scale τ) ^ N
        = (29568 * CP4 + 15744 * CP2 + 20570112 * 2 + 24 * Cjs) * (scale τ) ^ N := by ring
    linarith [h, h2]
  linarith [t1, t2, t3, t4, b1, b2, b3, b4, hb5, hcomb]

/-- The `k ≥ 1` coefficients of `R24` are `O((scale τ)^N e^{2π Im τ})`. -/
private lemma R24_hi_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)
        + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
        + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
        + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
        + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖)
        ≤ C * (scale τ) ^ N * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨CP4, NP4, hCP4, hNP4, hP4⟩ := KF24.psi4E8_funnel ℓ
  obtain ⟨CP2, NP2, hCP2, hNP2, hP2⟩ := KF24.psi2E10_funnel ℓ
  obtain ⟨Cj4, Nj4, hCj4, hNj4, hj4⟩ := KF24.j_psi4E8_funnel ℓ
  obtain ⟨Cj2, Nj2, hCj2, hNj2, hj2⟩ := KF24.j_psi2E10_funnel ℓ
  obtain ⟨Cjs, Njs, hCjs, hNjs, hjs⟩ := KF24.j_psi_sub_funnel ℓ
  obtain ⟨Cj2s, Nj2s, hCj2s, hNj2s, hj2s⟩ := KF24.j2_psi_sub_funnel ℓ
  set N := NP4 + NP2 + Nj4 + Nj2 + Nj2s + Njs with hN
  set A1 := (896832 * CP4 + 305856 * CP2 + 31850496 * 2 + 2040 * Cj4 + 312 * Cj2
      + 41472 * (27 / 8) + Cj2s + 1990656 * 2) with hA1
  set A2 := (12616704 * CP4 + 2663424 * CP2 + 15925248 * 2 + 23424 * Cj4 + 9600 * Cj2
      + 8 * Cj2s) with hA2
  set A3 := (49268736 * CP4 + 19408896 * CP2 + 23887872 * 2 + 86976 * Cj4 + 45504 * Cj2
      + 24 * Cj2s + 1433272320 * 2 + 1990656 * (27 / 8)) with hA3
  set A4 := (72990720 * CP4 + 72990720 * CP2 + 11466178560 * 2 + 101376 * Cjs
      + 15925248 * (27 / 8)) with hA4
  set A5 := (656916480 * CP4 + 656916480 * CP2 + 17199267840 * 2 + 912384 * Cjs
      + 23887872 * (27 / 8)) with hA5
  refine ⟨1990656 * 2 + A1 + A2 + ((1433272320 * 2 + 1990656 * (27 / 8)) + A3) + A4 + A5, N,
    by positivity, by positivity, fun τ hτ => ?_⟩
  have hN0 : (0:ℝ) ≤ N := by rw [hN]; linarith
  have hN1 : (1:ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow hN0
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  set E := Real.exp (2 * Real.pi * τ.im) with hE
  have hE1 : (1:ℝ) ≤ E := by
    rw [hE, ← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have eP4 : NP4 ≤ N := by rw [hN]; linarith
  have eP2 : NP2 ≤ N := by rw [hN]; linarith
  have ej4 : Nj4 ≤ N := by rw [hN]; linarith
  have ej2 : Nj2 ≤ N := by rw [hN]; linarith
  have ejs : Njs ≤ N := by rw [hN]; linarith
  have ej2s : Nj2s ≤ N := by rw [hN]; linarith
  have mP4 : ‖psi4 ℓ τ * E8Fun τ‖ ≤ CP4 * (scale τ) ^ N * E := by
    have h := scale_inflate (τ := τ) (hP4 τ hτ) hCP4.le eP4
    calc ‖psi4 ℓ τ * E8Fun τ‖ ≤ CP4 * (scale τ) ^ N := h
      _ = CP4 * (scale τ) ^ N * 1 := by ring
      _ ≤ CP4 * (scale τ) ^ N * E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  have mP2 : ‖psi2 ℓ τ * E10Fun τ‖ ≤ CP2 * (scale τ) ^ N * E := by
    have h := scale_inflate (τ := τ) (hP2 τ hτ) hCP2.le eP2
    calc ‖psi2 ℓ τ * E10Fun τ‖ ≤ CP2 * (scale τ) ^ N := h
      _ = CP2 * (scale τ) ^ N * 1 := by ring
      _ ≤ CP2 * (scale τ) ^ N * E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  have mD : ‖DeltaFun τ‖ ≤ 2 * (scale τ) ^ N * E := by
    have h := KF24.norm_Delta_funnel τ hτ
    have h3 : Real.exp (-(2 * Real.pi * τ.im)) ≤ E := by
      rw [hE]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, τ.im_pos])
    calc ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) := h
      _ ≤ 2 * E := by linarith
      _ = 2 * E * 1 := by ring
      _ ≤ 2 * E * (scale τ) ^ N := mul_le_mul_of_nonneg_left hN1 (by positivity)
      _ = 2 * (scale τ) ^ N * E := by ring
  have mjD : ‖jInvariantFun τ * DeltaFun τ‖ ≤ (27 / 8) * (scale τ) ^ N * E := by
    have h := KF24.norm_j_mul_Delta_funnel τ hτ
    calc ‖jInvariantFun τ * DeltaFun τ‖ ≤ 27 / 8 := h
      _ = 27 / 8 * 1 := by ring
      _ ≤ 27 / 8 * (scale τ) ^ N := mul_le_mul_of_nonneg_left hN1 (by norm_num)
      _ = 27 / 8 * (scale τ) ^ N * 1 := by ring
      _ ≤ 27 / 8 * (scale τ) ^ N * E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  have mj4 : ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖ ≤ Cj4 * (scale τ) ^ N * E := by
    exact scale_inflate_mul (τ := τ) (hj4 τ hτ) hCj4.le ej4 (Real.exp_pos _).le
  have mj2 : ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖ ≤ Cj2 * (scale τ) ^ N * E := by
    exact scale_inflate_mul (τ := τ) (hj2 τ hτ) hCj2.le ej2 (Real.exp_pos _).le
  have mjs : ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ Cjs * (scale τ) ^ N * E := by
    have h := scale_inflate (τ := τ) (hjs τ hτ) hCjs.le ejs
    calc ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖ ≤ Cjs * (scale τ) ^ N := h
      _ = Cjs * (scale τ) ^ N * 1 := by ring
      _ ≤ Cjs * (scale τ) ^ N * E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  have mj2s : ‖jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ Cj2s * (scale τ) ^ N * E := by
    exact scale_inflate_mul (τ := τ) (hj2s τ hτ) hCj2s.le ej2s (Real.exp_pos _).le
  -- the `Xc`-free coefficient bounds
  have hq1 : ‖Compact.R24_q1 ℓ τ‖ ≤ 1990656 * 2 * (scale τ) ^ N * E := by
    have hid : Compact.R24_q1 ℓ τ = (1990656 : ℂ) * DeltaFun τ := rfl
    rw [hid, norm_mul, Complex.norm_ofNat]
    calc 1990656 * ‖DeltaFun τ‖ ≤ 1990656 * (2 * (scale τ) ^ N * E) :=
          mul_le_mul_of_nonneg_left mD (by norm_num)
      _ = 1990656 * 2 * (scale τ) ^ N * E := by ring
  have hp1 : ‖Compact.R24_p1 ℓ τ‖ ≤ A1 * (scale τ) ^ N * E := by
    have hid : Compact.R24_p1 ℓ τ
        = (-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (31850496 : ℂ) * DeltaFun τ + (2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ)
          - jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) := by
      rw [Compact.R24_p1]; ring
    rw [hid]
    have c1 : ‖(-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 896832 * CP4 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 896832 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 896832 * (CP4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP4 (by norm_num)
        _ = 896832 * CP4 * (scale τ) ^ N * E := by ring
    have c2 : ‖(-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 305856 * CP2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 305856 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 305856 * (CP2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP2 (by norm_num)
        _ = 305856 * CP2 * (scale τ) ^ N * E := by ring
    have c3 : ‖(31850496 : ℂ) * DeltaFun τ‖ ≤ 31850496 * 2 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 31850496 * ‖DeltaFun τ‖ ≤ 31850496 * (2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mD (by norm_num)
        _ = 31850496 * 2 * (scale τ) ^ N * E := by ring
    have c4 : ‖(2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖
        ≤ 2040 * Cj4 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 2040 * ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖ ≤ 2040 * (Cj4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mj4 (by norm_num)
        _ = 2040 * Cj4 * (scale τ) ^ N * E := by ring
    have c5 : ‖(-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖
        ≤ 312 * Cj2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 312 * ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖ ≤ 312 * (Cj2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mj2 (by norm_num)
        _ = 312 * Cj2 * (scale τ) ^ N * E := by ring
    have c6 : ‖(-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖
        ≤ 41472 * (27 / 8) * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 41472 * ‖jInvariantFun τ * DeltaFun τ‖ ≤ 41472 * ((27 / 8) * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mjD (by norm_num)
        _ = 41472 * (27 / 8) * (scale τ) ^ N * E := by ring
    have c7 : ‖jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        ≤ Cj2s * (scale τ) ^ N * E := mj2s
    have t1 := norm_sub_le ((-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (31850496 : ℂ) * DeltaFun τ
        + (2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
        + (-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
        + (-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ))
      (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
    have t2 := norm_add_le ((-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (31850496 : ℂ) * DeltaFun τ
        + (2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)))
      ((-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
        + (-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ))
    have t3 := norm_add_le ((-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (31850496 : ℂ) * DeltaFun τ)
      ((2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)))
    have t4 := norm_add_le ((-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ)) ((31850496 : ℂ) * DeltaFun τ)
    have t5 := norm_add_le ((-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ))
      ((-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ))
    have t6 := norm_add_le ((-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)))
      ((-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ))
    rw [hA1]
    refine le_trans (tri7s c1 c2 c3 c4 c5 c6 c7) ?_
    have h0 : (0:ℝ) ≤ (scale τ) ^ N * E := pos_f1b (Real.exp_pos _).le
    have hc : (0:ℝ) ≤ 1990656 * 2 := by norm_num
    nlinarith [h0, hc, mul_nonneg hc h0]
  have hq3 : ‖Compact.R24_q3 ℓ τ‖ ≤ (1433272320 * 2 + 1990656 * (27 / 8)) * (scale τ) ^ N * E := by
    have hid : Compact.R24_q3 ℓ τ
        = (-1433272320 : ℂ) * DeltaFun τ + (1990656 : ℂ) * (jInvariantFun τ * DeltaFun τ) := by
      rw [Compact.R24_q3]
    rw [hid]
    have c1 : ‖(-1433272320 : ℂ) * DeltaFun τ‖ ≤ 1433272320 * 2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 1433272320 * ‖DeltaFun τ‖ ≤ 1433272320 * (2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mD (by norm_num)
        _ = 1433272320 * 2 * (scale τ) ^ N * E := by ring
    have c2 : ‖(1990656 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖
        ≤ 1990656 * (27 / 8) * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 1990656 * ‖jInvariantFun τ * DeltaFun τ‖
          ≤ 1990656 * ((27 / 8) * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mjD (by norm_num)
        _ = 1990656 * (27 / 8) * (scale τ) ^ N * E := by ring
    exact le_trans (tri2 c1 c2) (le_of_eq (by ring))
  have hp2 : ‖Compact.R24_p2 ℓ τ‖ ≤ A2 * (scale τ) ^ N * E := by
    have hid : Compact.R24_p2 ℓ τ
        = (12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (-15925248 : ℂ) * DeltaFun τ
          + (-23424 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (9600 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (8 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) := by
      rw [Compact.R24_p2]; ring
    rw [hid]
    have c1 : ‖(12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 12616704 * CP4 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 12616704 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 12616704 * (CP4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP4 (by norm_num)
        _ = 12616704 * CP4 * (scale τ) ^ N * E := by ring
    have c2 : ‖(-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 2663424 * CP2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 2663424 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 2663424 * (CP2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP2 (by norm_num)
        _ = 2663424 * CP2 * (scale τ) ^ N * E := by ring
    have c3 : ‖(-15925248 : ℂ) * DeltaFun τ‖ ≤ 15925248 * 2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 15925248 * ‖DeltaFun τ‖ ≤ 15925248 * (2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mD (by norm_num)
        _ = 15925248 * 2 * (scale τ) ^ N * E := by ring
    have c4 : ‖(-23424 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖
        ≤ 23424 * Cj4 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 23424 * ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖ ≤ 23424 * (Cj4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mj4 (by norm_num)
        _ = 23424 * Cj4 * (scale τ) ^ N * E := by ring
    have c5 : ‖(9600 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖
        ≤ 9600 * Cj2 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 9600 * ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖ ≤ 9600 * (Cj2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mj2 (by norm_num)
        _ = 9600 * Cj2 * (scale τ) ^ N * E := by ring
    have c6 : ‖(8 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
        ≤ 8 * Cj2s * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 8 * ‖jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          ≤ 8 * (Cj2s * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mj2s (by norm_num)
        _ = 8 * Cj2s * (scale τ) ^ N * E := by ring
    have t1 := norm_add_le ((12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (-15925248 : ℂ) * DeltaFun τ
        + (-23424 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)))
      ((9600 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
        + (8 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
    have t2 := norm_add_le ((12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (-15925248 : ℂ) * DeltaFun τ)
      ((-23424 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)))
    have t3 := norm_add_le ((12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ)) ((-15925248 : ℂ) * DeltaFun τ)
    have t4 := norm_add_le ((12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ))
      ((-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ))
    have t5 := norm_add_le ((9600 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)))
      ((8 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
    rw [hA2]
    exact le_trans (tri6 c1 c2 c3 c4 c5 c6) (le_of_eq (by ring))
  have hp3 : ‖Compact.R24_p3 ℓ τ‖ ≤ A3 * (scale τ) ^ N * E := by
    have hid : Compact.R24_p3 ℓ τ
        = (-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (23887872 : ℂ) * DeltaFun τ
          + (86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          - (24 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) := by
      rw [Compact.R24_p3]; ring
    rw [hid]
    have c1 : ‖(-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 49268736 * CP4 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 49268736 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 49268736 * (CP4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP4 (by norm_num)
        _ = 49268736 * CP4 * (scale τ) ^ N * E := by ring
    have c2 : ‖(19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 19408896 * CP2 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 19408896 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 19408896 * (CP2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP2 (by norm_num)
        _ = 19408896 * CP2 * (scale τ) ^ N * E := by ring
    have c3 : ‖(23887872 : ℂ) * DeltaFun τ‖ ≤ 23887872 * 2 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 23887872 * ‖DeltaFun τ‖ ≤ 23887872 * (2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mD (by norm_num)
        _ = 23887872 * 2 * (scale τ) ^ N * E := by ring
    have c4 : ‖(86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖
        ≤ 86976 * Cj4 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 86976 * ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖ ≤ 86976 * (Cj4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mj4 (by norm_num)
        _ = 86976 * Cj4 * (scale τ) ^ N * E := by ring
    have c5 : ‖(-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖
        ≤ 45504 * Cj2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 45504 * ‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖ ≤ 45504 * (Cj2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mj2 (by norm_num)
        _ = 45504 * Cj2 * (scale τ) ^ N * E := by ring
    have c6 : ‖(24 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
        ≤ 24 * Cj2s * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 24 * ‖jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          ≤ 24 * (Cj2s * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mj2s (by norm_num)
        _ = 24 * Cj2s * (scale τ) ^ N * E := by ring
    have t1 := norm_sub_le ((-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (23887872 : ℂ) * DeltaFun τ
        + (86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
        + (-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)))
      ((24 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
    have t2 := norm_add_le ((-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (23887872 : ℂ) * DeltaFun τ)
      ((86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
        + (-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)))
    have t3 := norm_add_le ((-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ)) ((23887872 : ℂ) * DeltaFun τ)
    have t4 := norm_add_le ((-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ))
      ((19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ))
    have t5 := norm_add_le ((86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)))
      ((-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)))
    rw [hA3]
    refine le_trans (tri6m c1 c2 c3 c4 c5 c6) ?_
    have h0 : (0:ℝ) ≤ (scale τ) ^ N * E := pos_f1b (Real.exp_pos _).le
    have hc : (0:ℝ) ≤ 1433272320 * 2 + 1990656 * (27 / 8) := by norm_num
    nlinarith [h0, hc, mul_nonneg hc h0]
  have hp4 : ‖Compact.R24_p4 ℓ τ‖ ≤ A4 * (scale τ) ^ N * E := by
    have hid : Compact.R24_p4 ℓ τ
        = (72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (11466178560 : ℂ) * DeltaFun τ
          - (101376 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
          - (15925248 : ℂ) * (jInvariantFun τ * DeltaFun τ) := by
      rw [Compact.R24_p4]; ring
    rw [hid]
    have c1 : ‖(72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 72990720 * CP4 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 72990720 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 72990720 * (CP4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP4 (by norm_num)
        _ = 72990720 * CP4 * (scale τ) ^ N * E := by ring
    have c2 : ‖(-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 72990720 * CP2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 72990720 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 72990720 * (CP2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP2 (by norm_num)
        _ = 72990720 * CP2 * (scale τ) ^ N * E := by ring
    have c3 : ‖(11466178560 : ℂ) * DeltaFun τ‖ ≤ 11466178560 * 2 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 11466178560 * ‖DeltaFun τ‖ ≤ 11466178560 * (2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mD (by norm_num)
        _ = 11466178560 * 2 * (scale τ) ^ N * E := by ring
    have c4 : ‖(101376 : ℂ) * (jInvariantFun τ
          * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
        ≤ 101376 * Cjs * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 101376 * ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          ≤ 101376 * (Cjs * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mjs (by norm_num)
        _ = 101376 * Cjs * (scale τ) ^ N * E := by ring
    have c5 : ‖(15925248 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖
        ≤ 15925248 * (27 / 8) * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 15925248 * ‖jInvariantFun τ * DeltaFun τ‖
          ≤ 15925248 * ((27 / 8) * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mjD (by norm_num)
        _ = 15925248 * (27 / 8) * (scale τ) ^ N * E := by ring
    have t1 := norm_sub_le ((72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (11466178560 : ℂ) * DeltaFun τ
        - (101376 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
      ((15925248 : ℂ) * (jInvariantFun τ * DeltaFun τ))
    have t2 := norm_sub_le ((72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (11466178560 : ℂ) * DeltaFun τ)
      ((101376 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
    have t3 := norm_add_le ((72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ)) ((11466178560 : ℂ) * DeltaFun τ)
    have t4 := norm_add_le ((72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ))
      ((-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ))
    rw [hA4]
    exact le_trans (tri5m2 c1 c2 c3 c4 c5) (le_of_eq (by ring))
  have hp5 : ‖Compact.R24_p5 ℓ τ‖ ≤ A5 * (scale τ) ^ N * E := by
    have hid : Compact.R24_p5 ℓ τ
        = (-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (-17199267840 : ℂ) * DeltaFun τ
          + (912384 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
          + (23887872 : ℂ) * (jInvariantFun τ * DeltaFun τ) := by
      rw [Compact.R24_p5]; ring
    rw [hid]
    have c1 : ‖(-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 656916480 * CP4 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 656916480 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 656916480 * (CP4 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP4 (by norm_num)
        _ = 656916480 * CP4 * (scale τ) ^ N * E := by ring
    have c2 : ‖(656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 656916480 * CP2 * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 656916480 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 656916480 * (CP2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mP2 (by norm_num)
        _ = 656916480 * CP2 * (scale τ) ^ N * E := by ring
    have c3 : ‖(-17199267840 : ℂ) * DeltaFun τ‖ ≤ 17199267840 * 2 * (scale τ) ^ N * E := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      calc 17199267840 * ‖DeltaFun τ‖ ≤ 17199267840 * (2 * (scale τ) ^ N * E) :=
            mul_le_mul_of_nonneg_left mD (by norm_num)
        _ = 17199267840 * 2 * (scale τ) ^ N * E := by ring
    have c4 : ‖(912384 : ℂ) * (jInvariantFun τ
          * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
        ≤ 912384 * Cjs * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 912384 * ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          ≤ 912384 * (Cjs * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mjs (by norm_num)
        _ = 912384 * Cjs * (scale τ) ^ N * E := by ring
    have c5 : ‖(23887872 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖
        ≤ 23887872 * (27 / 8) * (scale τ) ^ N * E := by
      rw [norm_mul, Complex.norm_ofNat]
      calc 23887872 * ‖jInvariantFun τ * DeltaFun τ‖
          ≤ 23887872 * ((27 / 8) * (scale τ) ^ N * E) := mul_le_mul_of_nonneg_left mjD (by norm_num)
        _ = 23887872 * (27 / 8) * (scale τ) ^ N * E := by ring
    have t1 := norm_add_le ((-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (-17199267840 : ℂ) * DeltaFun τ
        + (912384 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
      ((23887872 : ℂ) * (jInvariantFun τ * DeltaFun τ))
    have t2 := norm_add_le ((-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ) + (-17199267840 : ℂ) * DeltaFun τ)
      ((912384 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
    have t3 := norm_add_le ((-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ)) ((-17199267840 : ℂ) * DeltaFun τ)
    have t4 := norm_add_le ((-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ))
      ((656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ))
    rw [hA5]
    exact le_trans (tri5 c1 c2 c3 c4 c5) (le_of_eq (by ring))
  have hq2 : ‖Compact.R24_q2 ℓ τ‖ ≤ 0 := by
    rw [show Compact.R24_q2 ℓ τ = 0 from rfl, norm_zero]
  have hq4 : ‖Compact.R24_q4 ℓ τ‖ ≤ 0 := by
    rw [show Compact.R24_q4 ℓ τ = 0 from rfl, norm_zero]
  have hq5 : ‖Compact.R24_q5 ℓ τ‖ ≤ 0 := by
    rw [show Compact.R24_q5 ℓ τ = 0 from rfl, norm_zero]
  have hw1 := add_le_add hq1 hp1
  have hw2 := add_le_add hq2 hp2
  have hw3 := add_le_add hq3 hp3
  have hw4 := add_le_add hq4 hp4
  have hw5 := add_le_add hq5 hp5
  have hv1 := add_le_add hw2 hw3
  have hv2 := add_le_add hw4 hw5
  have hv3 := add_le_add hv1 hv2
  have hv4 := add_le_add hw1 hv3
  have hcomb : (1990656 * 2 + A1) * (scale τ) ^ N * E + A2 * (scale τ) ^ N * E
      + ((1433272320 * 2 + 1990656 * (27 / 8)) + A3) * (scale τ) ^ N * E
      + A4 * (scale τ) ^ N * E + A5 * (scale τ) ^ N * E
      = (1990656 * 2 + A1 + A2 + ((1433272320 * 2 + 1990656 * (27 / 8)) + A3) + A4 + A5)
        * (scale τ) ^ N * E := by ring
  have hgoal : (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)
      + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
      + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
      + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
      + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖)
      ≤ (1990656 * 2 + A1 + A2 + ((1433272320 * 2 + 1990656 * (27 / 8)) + A3) + A4 + A5)
        * (scale τ) ^ N * E := by
    linarith [hv4, hcomb]
  exact hgoal


/-! ## The atoms `A24`, `A24ref`, `A24 - A24ref`, `C24`, `B24` -/

/-- Sharp bound for `A24`: `O((scale τ)^N (1+t) e^{-2π Im τ})`. -/
private lemma A24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.A24 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C14, hC14, h14⟩ := E14_bound
  obtain ⟨CL, hCL, hL⟩ := L_bound ℓ
  obtain ⟨CPs, NPs, hCPs, hNPs, hPs⟩ := KF24.psi_sub_funnel ℓ
  obtain ⟨C10, hC10, h10⟩ := E10_bound
  obtain ⟨CD2, hCD2, hD2⟩ := D2_bound
  refine ⟨3456 * 2 * C14 * CL + CPs * C10 * CD2 + 1, NPs, by positivity, hNPs,
    fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hzn : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have hs1 : (1:ℝ) ≤ (scale τ) ^ NPs := one_le_scale_rpow hNPs
  have hE := KF24.norm_Delta_funnel τ hτ
  have h14b := h14 z hz1
  have hLb := hL z hz1
  have hPsb := hPs τ hτ
  have h10b := h10 z hz1
  have hD2b := hD2 z hz1
  have hPs' : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
      ≤ CPs * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ
        = -(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) by ring, norm_neg]
    exact hPsb
  have hA24 : Compact.A24 ℓ τ z
      = -3456 * DeltaFun τ * E14Fun z * ℓ.L z
        - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
          * (UFun z ^ 2 - VFun z ^ 2) := rfl
  rw [hA24]
  have e1 : ‖(-3456:ℂ) * DeltaFun τ * E14Fun z * ℓ.L z‖
      ≤ 3456 * 2 * C14 * CL * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show (-3456:ℂ) * DeltaFun τ * E14Fun z * ℓ.L z
        = -((3456:ℂ) * (DeltaFun τ * (E14Fun z * ℓ.L z))) by ring, norm_neg]
    rw [norm_mul, Complex.norm_ofNat]
    have hinner : ‖DeltaFun τ * (E14Fun z * ℓ.L z)‖
        ≤ (2 * Real.exp (-(2 * Real.pi * τ.im))) * (C14 * (CL * (1 + t))) := by
      rw [norm_mul]
      have h14L : ‖E14Fun z * ℓ.L z‖ ≤ C14 * (CL * (1 + ‖(z : ℂ)‖)) := by
        rw [norm_mul]
        exact mul_le_mul h14b hLb (norm_nonneg _) hC14.le
      calc ‖DeltaFun τ‖ * ‖E14Fun z * ℓ.L z‖
          ≤ (2 * Real.exp (-(2 * Real.pi * τ.im))) * (C14 * (CL * (1 + ‖(z : ℂ)‖))) :=
            mul_le_mul hE h14L (norm_nonneg _) (by positivity)
        _ = (2 * Real.exp (-(2 * Real.pi * τ.im))) * (C14 * (CL * (1 + t))) := by rw [hzn]
    calc 3456 * ‖DeltaFun τ * (E14Fun z * ℓ.L z)‖
        ≤ 3456 * ((2 * Real.exp (-(2 * Real.pi * τ.im))) * (C14 * (CL * (1 + t)))) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 3456 * 2 * C14 * CL * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by ring_nf
      _ = (3456 * 2 * C14 * CL * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) * 1 := by ring
      _ ≤ (3456 * 2 * C14 * CL * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) * (scale τ) ^ NPs :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 3456 * 2 * C14 * CL * (scale τ) ^ NPs * (1 + t)
            * Real.exp (-(2 * Real.pi * τ.im)) := by ring_nf
  have e2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z * (UFun z ^ 2 - VFun z ^ 2)‖
      ≤ CPs * C10 * CD2 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [norm_mul, norm_mul]
    calc ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖ * ‖E10Fun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖
        ≤ (CPs * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im))) * C10 * CD2 := by
          exact mul_le_mul (mul_le_mul hPs' h10b (norm_nonneg _) (by positivity)) hD2b
            (norm_nonneg _) (by positivity)
      _ = CPs * C10 * CD2 * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ = (CPs * C10 * CD2 * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im))) * 1 := by ring
      _ ≤ (CPs * C10 * CD2 * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im))) * (1 + t) :=
          mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1 + t) (by positivity)
      _ = CPs * C10 * CD2 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by ring
  have hsum := norm_sub_le ((-3456:ℂ) * DeltaFun τ * E14Fun z * ℓ.L z)
    ((psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z * (UFun z ^ 2 - VFun z ^ 2))
  have hcomb : 3456 * 2 * C14 * CL * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
      + CPs * C10 * CD2 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
      ≤ (3456 * 2 * C14 * CL + CPs * C10 * CD2 + 1) * (scale τ) ^ NPs * (1 + t)
        * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h0 : (0:ℝ) ≤ (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
    have h3 : 3456 * 2 * C14 * CL * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
        + CPs * C10 * CD2 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
        = (3456 * 2 * C14 * CL + CPs * C10 * CD2)
          * ((scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) := by ring
    have h4 : (3456 * 2 * C14 * CL + CPs * C10 * CD2)
        ≤ 3456 * 2 * C14 * CL + CPs * C10 * CD2 + 1 := by linarith
    have h5 := mul_le_mul_of_nonneg_right h4 h0
    have h6 : (3456 * 2 * C14 * CL + CPs * C10 * CD2 + 1)
          * ((scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)))
        = (3456 * 2 * C14 * CL + CPs * C10 * CD2 + 1) * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) := by ring
    linarith [h3, h5, h6]
  exact le_trans hsum (le_trans (add_le_add e1 e2) hcomb)

/-- Sharp bound for `A24ref`. -/
private lemma A24ref_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.A24ref ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨CLr, hCLr, hLr⟩ := Lref_bound ℓ
  obtain ⟨CPs, NPs, hCPs, hNPs, hPs⟩ := KF24.psi_sub_funnel ℓ
  refine ⟨3456 * 2 * 25 * CLr + CPs * 265 * 161 + 1, NPs, by positivity, hNPs,
    fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hzn : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have hs1 : (1:ℝ) ≤ (scale τ) ^ NPs := one_le_scale_rpow hNPs
  have hE := KF24.norm_Delta_funnel τ hτ
  have hLrb := hLr z hz1
  have hPsb := hPs τ hτ
  have hPs' : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
      ≤ CPs * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ
        = -(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) by ring, norm_neg]
    exact hPsb
  have hE14r : ‖Compact.E14ref z‖ ≤ 25 :=
    le_trans (norm_one_sub_const_Ept_sq 24 (by norm_num) hz1) (by norm_num)
  have hE10r : ‖Compact.E10ref z‖ ≤ 265 :=
    le_trans (norm_one_sub_const_Ept_sq 264 (by norm_num) hz1) (by norm_num)
  have hD2r : ‖Compact.D2ref z‖ ≤ 161 := norm_D2ref_le hz1
  have hA24 : Compact.A24ref ℓ τ z
      = -3456 * DeltaFun τ * Compact.E14ref z * Compact.Lref ℓ z
        - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * Compact.E10ref z
          * Compact.D2ref z := rfl
  rw [hA24]
  have e1 : ‖(-3456:ℂ) * DeltaFun τ * Compact.E14ref z * Compact.Lref ℓ z‖
      ≤ 3456 * 2 * 25 * CLr * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show (-3456:ℂ) * DeltaFun τ * Compact.E14ref z * Compact.Lref ℓ z
        = -((3456:ℂ) * (DeltaFun τ * (Compact.E14ref z * Compact.Lref ℓ z))) by ring,
      norm_neg]
    rw [norm_mul, Complex.norm_ofNat]
    have hinner : ‖DeltaFun τ * (Compact.E14ref z * Compact.Lref ℓ z)‖
        ≤ (2 * Real.exp (-(2 * Real.pi * τ.im))) * (25 * (CLr * (1 + t))) := by
      rw [norm_mul]
      have h14L : ‖Compact.E14ref z * Compact.Lref ℓ z‖ ≤ 25 * (CLr * (1 + ‖(z : ℂ)‖)) := by
        rw [norm_mul]
        exact mul_le_mul hE14r hLrb (norm_nonneg _) (by norm_num)
      calc ‖DeltaFun τ‖ * ‖Compact.E14ref z * Compact.Lref ℓ z‖
          ≤ (2 * Real.exp (-(2 * Real.pi * τ.im))) * (25 * (CLr * (1 + ‖(z : ℂ)‖))) :=
            mul_le_mul hE h14L (norm_nonneg _) (by positivity)
        _ = (2 * Real.exp (-(2 * Real.pi * τ.im))) * (25 * (CLr * (1 + t))) := by rw [hzn]
    calc 3456 * ‖DeltaFun τ * (Compact.E14ref z * Compact.Lref ℓ z)‖
        ≤ 3456 * ((2 * Real.exp (-(2 * Real.pi * τ.im))) * (25 * (CLr * (1 + t)))) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 3456 * 2 * 25 * CLr * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by ring_nf
      _ = (3456 * 2 * 25 * CLr * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) * 1 := by ring
      _ ≤ (3456 * 2 * 25 * CLr * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) * (scale τ) ^ NPs :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 3456 * 2 * 25 * CLr * (scale τ) ^ NPs * (1 + t)
            * Real.exp (-(2 * Real.pi * τ.im)) := by ring_nf
  have e2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * Compact.E10ref z * Compact.D2ref z‖
      ≤ CPs * 265 * 161 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [norm_mul, norm_mul]
    calc ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖ * ‖Compact.E10ref z‖ * ‖Compact.D2ref z‖
        ≤ (CPs * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im))) * 265 * 161 := by
          exact mul_le_mul (mul_le_mul hPs' hE10r (norm_nonneg _)
            (pos_f3 hCPs.le (Real.exp_pos _).le)) hD2r (norm_nonneg _) (by positivity)
      _ = CPs * 265 * 161 * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ = (CPs * 265 * 161 * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im))) * 1 := by ring
      _ ≤ (CPs * 265 * 161 * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im))) * (1 + t) :=
          mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1 + t) (by positivity)
      _ = CPs * 265 * 161 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by ring
  have hsum := norm_sub_le ((-3456:ℂ) * DeltaFun τ * Compact.E14ref z * Compact.Lref ℓ z)
    ((psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * Compact.E10ref z * Compact.D2ref z)
  have hcomb : 3456 * 2 * 25 * CLr * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
      + CPs * 265 * 161 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
      ≤ (3456 * 2 * 25 * CLr + CPs * 265 * 161 + 1) * (scale τ) ^ NPs * (1 + t)
        * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h0 : (0:ℝ) ≤ (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
    have h3 : 3456 * 2 * 25 * CLr * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
        + CPs * 265 * 161 * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
        = (3456 * 2 * 25 * CLr + CPs * 265 * 161)
          * ((scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) := by ring
    have h4 : (3456 * 2 * 25 * CLr + CPs * 265 * 161)
        ≤ 3456 * 2 * 25 * CLr + CPs * 265 * 161 + 1 := by linarith
    have h5 := mul_le_mul_of_nonneg_right h4 h0
    have h6 : (3456 * 2 * 25 * CLr + CPs * 265 * 161 + 1)
          * ((scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)))
        = (3456 * 2 * 25 * CLr + CPs * 265 * 161 + 1) * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) := by ring
    linarith [h3, h5, h6]
  exact le_trans hsum (le_trans (add_le_add e1 e2) hcomb)

/-- Sharp bound for `A24 - A24ref`. -/
private lemma A24diff_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z‖
        ≤ C * (scale τ) ^ N * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by
  obtain ⟨CPs, NPs, hCPs, hNPs, hPs⟩ := KF24.psi_sub_funnel ℓ
  obtain ⟨C14, hC14, h14⟩ := E14_bound
  obtain ⟨CLr, hCLr, hLr⟩ := Lref_bound ℓ
  obtain ⟨CdL, hCdL, hdL⟩ := dL_bound ℓ
  obtain ⟨CdE14, hCdE14, hdE14⟩ := dE14_bound
  obtain ⟨C10, hC10, h10⟩ := E10_bound
  obtain ⟨CdD2, hCdD2, hdD2⟩ := dD2_bound
  obtain ⟨CdE10, hCdE10, hdE10⟩ := dE10_bound
  refine ⟨3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161) + 1, NPs,
    by positivity, hNPs, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hzn : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have hs1 : (1:ℝ) ≤ (scale τ) ^ NPs := one_le_scale_rpow hNPs
  have hE := KF24.norm_Delta_funnel τ hτ
  have hPsb := hPs τ hτ
  have hPs' : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
      ≤ CPs * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ
        = -(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) by ring, norm_neg]
    exact hPsb
  have h14b := h14 z hz1
  have h10b := h10 z hz1
  have hLrb := hLr z hz1
  have hD2r : ‖Compact.D2ref z‖ ≤ 161 := norm_D2ref_le hz1
  have hE3 : ‖Ept z‖ ^ 4 ≤ ‖Ept z‖ ^ 3 := by
    have he := KF24.norm_Ept_le_one' hz1
    have h0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
    calc ‖Ept z‖ ^ 4 = ‖Ept z‖ ^ 3 * ‖Ept z‖ := by ring
      _ ≤ ‖Ept z‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left he (pow_nonneg h0 3)
      _ = ‖Ept z‖ ^ 3 := by ring
  have hid : Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z
      = -3456 * DeltaFun τ * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z)
        - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
          * (E10Fun z * Compact.dD2 z + Compact.dE10 z * Compact.D2ref z) := by
    have hA24 : Compact.A24 ℓ τ z
        = -3456 * DeltaFun τ * E14Fun z * ℓ.L z
          - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
            * (UFun z ^ 2 - VFun z ^ 2) := rfl
    have hA24r : Compact.A24ref ℓ τ z
        = -3456 * DeltaFun τ * Compact.E14ref z * Compact.Lref ℓ z
          - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * Compact.E10ref z
            * Compact.D2ref z := rfl
    rw [hA24, hA24r]
    simp only [Compact.dL, Compact.dE14, Compact.dD2, Compact.dE10]
    ring
  rw [hid]
  have e1 : ‖(-3456:ℂ) * DeltaFun τ
        * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z)‖
      ≤ 3456 * 2 * (C14 * CdL + CdE14 * CLr) * (scale τ) ^ NPs * (1 + t)
        * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by
    rw [show (-3456:ℂ) * DeltaFun τ
          * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z)
        = -((3456:ℂ) * (DeltaFun τ
          * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z))) by ring,
      norm_neg]
    rw [norm_mul, Complex.norm_ofNat]
    have hinner : ‖DeltaFun τ * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z)‖
        ≤ (2 * Real.exp (-(2 * Real.pi * τ.im)))
          * ((C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3) := by
      rw [norm_mul]
      have hinner2 : ‖E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z‖
          ≤ (C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3 := by
        have a1 : ‖E14Fun z * Compact.dL ℓ z‖ ≤ C14 * CdL * ‖Ept z‖ ^ 3 := by
          rw [norm_mul]
          calc ‖E14Fun z‖ * ‖Compact.dL ℓ z‖ ≤ C14 * (CdL * ‖Ept z‖ ^ 3) :=
                mul_le_mul h14b (hdL z hz1) (norm_nonneg _) hC14.le
            _ = C14 * CdL * ‖Ept z‖ ^ 3 := by ring
        have a2 : ‖Compact.dE14 z * Compact.Lref ℓ z‖ ≤ CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3 := by
          rw [norm_mul]
          calc ‖Compact.dE14 z‖ * ‖Compact.Lref ℓ z‖
              ≤ (CdE14 * ‖Ept z‖ ^ 4) * (CLr * (1 + ‖(z : ℂ)‖)) :=
                mul_le_mul (hdE14 z hz1) hLrb (norm_nonneg _) (by positivity)
            _ ≤ (CdE14 * ‖Ept z‖ ^ 3) * (CLr * (1 + t)) := by
                rw [hzn]
                exact mul_le_mul (mul_le_mul_of_nonneg_left hE3 hCdE14.le) (le_refl _)
                  (by positivity) (by positivity)
            _ = CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3 := by ring
        have hsum := norm_add_le (E14Fun z * Compact.dL ℓ z) (Compact.dE14 z * Compact.Lref ℓ z)
        have hkey : C14 * CdL * ‖Ept z‖ ^ 3 + CdE14 * CLr * (1 + t) * ‖Ept z‖ ^ 3
            ≤ (C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3 := by
          have h0 : (0:ℝ) ≤ ‖Ept z‖ ^ 3 := by positivity
          have h1t : (1:ℝ) ≤ 1 + t := by linarith
          have h2 : C14 * CdL * ‖Ept z‖ ^ 3 ≤ C14 * CdL * (1 + t) * ‖Ept z‖ ^ 3 := by
            have h3 : C14 * CdL * ‖Ept z‖ ^ 3 = (C14 * CdL) * ‖Ept z‖ ^ 3 := by ring
            have h4 : (C14 * CdL) * ‖Ept z‖ ^ 3 ≤ (C14 * CdL) * (1 + t) * ‖Ept z‖ ^ 3 := by
              have h5 : (C14 * CdL) * 1 ≤ (C14 * CdL) * (1 + t) :=
                mul_le_mul_of_nonneg_left h1t (by positivity)
              linarith [h5, mul_le_mul_of_nonneg_right h5 h0]
            linarith [h3, h4]
          linarith [h2]
        linarith [hsum, a1, a2, hkey]
      exact mul_le_mul hE hinner2 (norm_nonneg _) (by positivity)
    calc 3456 * ‖DeltaFun τ * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z)‖
        ≤ 3456 * ((2 * Real.exp (-(2 * Real.pi * τ.im)))
            * ((C14 * CdL + CdE14 * CLr) * (1 + t) * ‖Ept z‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 3456 * 2 * (C14 * CdL + CdE14 * CLr) * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
            * ‖Ept z‖ ^ 3 := by ring_nf
      _ = (3456 * 2 * (C14 * CdL + CdE14 * CLr) * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
            * ‖Ept z‖ ^ 3) * 1 := by ring
      _ ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr) * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
            * ‖Ept z‖ ^ 3) * (scale τ) ^ NPs :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 3456 * 2 * (C14 * CdL + CdE14 * CLr) * (scale τ) ^ NPs * (1 + t)
            * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by ring_nf
  have e2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
        * (E10Fun z * Compact.dD2 z + Compact.dE10 z * Compact.D2ref z)‖
      ≤ CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by
    rw [norm_mul]
    have hinner : ‖E10Fun z * Compact.dD2 z + Compact.dE10 z * Compact.D2ref z‖
        ≤ (C10 * CdD2 + CdE10 * 161) * ‖Ept z‖ ^ 3 := by
      have a1 : ‖E10Fun z * Compact.dD2 z‖ ≤ C10 * CdD2 * ‖Ept z‖ ^ 3 := by
        rw [norm_mul]
        calc ‖E10Fun z‖ * ‖Compact.dD2 z‖ ≤ C10 * (CdD2 * ‖Ept z‖ ^ 3) :=
              mul_le_mul h10b (hdD2 z hz1) (norm_nonneg _) hC10.le
          _ = C10 * CdD2 * ‖Ept z‖ ^ 3 := by ring
      have a2 : ‖Compact.dE10 z * Compact.D2ref z‖ ≤ CdE10 * 161 * ‖Ept z‖ ^ 3 := by
        rw [norm_mul]
        calc ‖Compact.dE10 z‖ * ‖Compact.D2ref z‖ ≤ (CdE10 * ‖Ept z‖ ^ 4) * 161 :=
              mul_le_mul (hdE10 z hz1) hD2r (norm_nonneg _) (by positivity)
          _ ≤ (CdE10 * ‖Ept z‖ ^ 3) * 161 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE3 hCdE10.le) (by norm_num)
          _ = CdE10 * 161 * ‖Ept z‖ ^ 3 := by ring
      have hsum := norm_add_le (E10Fun z * Compact.dD2 z) (Compact.dE10 z * Compact.D2ref z)
      linarith [hsum, a1, a2]
    calc ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
          * ‖E10Fun z * Compact.dD2 z + Compact.dE10 z * Compact.D2ref z‖
        ≤ (CPs * (scale τ) ^ NPs * Real.exp (-(2 * Real.pi * τ.im)))
            * ((C10 * CdD2 + CdE10 * 161) * ‖Ept z‖ ^ 3) :=
          mul_le_mul hPs' hinner (norm_nonneg _) (by positivity)
      _ = CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs
            * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by ring
      _ ≤ CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs * (1 + t)
            * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by
          have h0 : (0:ℝ) ≤ CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs
              * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by positivity
          have h1t : (1:ℝ) ≤ 1 + t := by linarith
          calc CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs
                * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3
              = (CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs
                * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3) * 1 := by ring
            _ ≤ (CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs
                * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3) * (1 + t) :=
                mul_le_mul_of_nonneg_left h1t h0
            _ = CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs * (1 + t)
                * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by ring
  have hsum := norm_sub_le ((-3456:ℂ) * DeltaFun τ
      * (E14Fun z * Compact.dL ℓ z + Compact.dE14 z * Compact.Lref ℓ z))
    ((psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
      * (E10Fun z * Compact.dD2 z + Compact.dE10 z * Compact.D2ref z))
  have hcomb : 3456 * 2 * (C14 * CdL + CdE14 * CLr) * (scale τ) ^ NPs * (1 + t)
        * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3
      + CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs * (1 + t)
        * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3
      ≤ (3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161) + 1)
        * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by
    set base := (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3
      with hbase
    have hbase0 : (0:ℝ) ≤ base := by rw [hbase]; positivity
    have h3 : 3456 * 2 * (C14 * CdL + CdE14 * CLr) * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3
        + CPs * (C10 * CdD2 + CdE10 * 161) * (scale τ) ^ NPs * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3
        = (3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161)) * base := by
      rw [hbase]; ring
    have h4 : (3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161))
        ≤ 3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161) + 1 := by
      linarith
    have h5 := mul_le_mul_of_nonneg_right h4 hbase0
    have h6 : (3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161) + 1) * base
        = (3456 * 2 * (C14 * CdL + CdE14 * CLr) + CPs * (C10 * CdD2 + CdE10 * 161) + 1)
          * (scale τ) ^ NPs * (1 + t) * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3 := by
      rw [hbase]; ring
    linarith [h3, h5, h6]
  exact le_trans hsum (le_trans (add_le_add e1 e2) hcomb)

/-- `‖C24 ℓ τ‖ ≤ C (scale τ)^N` on the funnel. -/
private lemma C24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Compact.C24 ℓ τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨CP4, NP4, hCP4, hNP4, hP4⟩ := KF24.psi4E8_funnel ℓ
  obtain ⟨Cjs, Njs, hCjs, hNjs, hjs⟩ := KF24.j_psi_sub_funnel ℓ
  set N := max NP4 Njs with hN
  refine ⟨1728 * CP4 + Cjs + 1, N, by positivity, by positivity, fun τ hτ => ?_⟩
  have hN0 : (0:ℝ) ≤ N := by
    rw [hN]; exact le_trans hNP4 (le_max_left _ _)
  have hN1 : (1:ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow hN0
  have e4 : NP4 ≤ N := by rw [hN]; exact le_max_left _ _
  have ejs : Njs ≤ N := by rw [hN]; exact le_max_right _ _
  have mP4 : ‖psi4 ℓ τ * E8Fun τ‖ ≤ CP4 * (scale τ) ^ N :=
    scale_inflate (τ := τ) (hP4 τ hτ) hCP4.le e4
  have mjs : ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ Cjs * (scale τ) ^ N := scale_inflate (τ := τ) (hjs τ hτ) hCjs.le ejs
  have hC24 : Compact.C24 ℓ τ
      = (-1:ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
        + 1728 * (psi4 ℓ τ * E8Fun τ) := by
    rw [Compact.C24]; ring
  rw [hC24]
  have a1 : ‖(-1:ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
      ≤ Cjs * (scale τ) ^ N := by
    rw [show (-1:ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
        = -(jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) by ring, norm_neg]
    exact mjs
  have a2 : ‖(1728:ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 1728 * CP4 * (scale τ) ^ N := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 1728 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 1728 * (CP4 * (scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left mP4 (by norm_num)
      _ = 1728 * CP4 * (scale τ) ^ N := by ring
  have t := norm_add_le ((-1:ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)))
    ((1728:ℂ) * (psi4 ℓ τ * E8Fun τ))
  have hsum2 : ‖(-1:ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
      + (1728:ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ (Cjs + 1728 * CP4) * (scale τ) ^ N :=
    le_trans (tri2 a1 a2) (le_of_eq (by ring))
  have h0 : (0:ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg τ N
  calc ‖(-1:ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
        + (1728:ℂ) * (psi4 ℓ τ * E8Fun τ)‖
      ≤ (Cjs + 1728 * CP4) * (scale τ) ^ N := hsum2
    _ ≤ (Cjs + 1728 * CP4 + 1) * (scale τ) ^ N := by nlinarith [h0]
    _ = (1728 * CP4 + Cjs + 1) * (scale τ) ^ N := by ring

/-- `‖B24 ℓ τ‖ ≤ C (scale τ)^N` on the funnel. -/
private lemma B24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Compact.B24 ℓ τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨CP4, NP4, hCP4, hNP4, hP4⟩ := KF24.psi4E8_funnel ℓ
  obtain ⟨CP2, NP2, hCP2, hNP2, hP2⟩ := KF24.psi2E10_funnel ℓ
  set N := max NP4 NP2 with hN
  refine ⟨3456 * 2 + 2 * CP4 + 2 * CP2 + 1, N, by positivity, by positivity, fun τ hτ => ?_⟩
  have hN0 : (0:ℝ) ≤ N := by rw [hN]; exact le_trans hNP4 (le_max_left _ _)
  have hN1 : (1:ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow hN0
  have e4 : NP4 ≤ N := by rw [hN]; exact le_max_left _ _
  have e2 : NP2 ≤ N := by rw [hN]; exact le_max_right _ _
  have mP4 : ‖psi4 ℓ τ * E8Fun τ‖ ≤ CP4 * (scale τ) ^ N :=
    scale_inflate (τ := τ) (hP4 τ hτ) hCP4.le e4
  have mP2 : ‖psi2 ℓ τ * E10Fun τ‖ ≤ CP2 * (scale τ) ^ N :=
    scale_inflate (τ := τ) (hP2 τ hτ) hCP2.le e2
  have hE := KF24.norm_Delta_funnel τ hτ
  have hE1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ.2])
  have hB24 : Compact.B24 ℓ τ
      = -3456 * DeltaFun τ - 2 * (psi4 ℓ τ * E8Fun τ) + 2 * (psi2 ℓ τ * E10Fun τ) := by
    rw [Compact.B24]; ring
  rw [hB24]
  have a1 : ‖(-3456:ℂ) * DeltaFun τ‖ ≤ 3456 * 2 * (scale τ) ^ N := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat]
    have h2 : 3456 * ‖DeltaFun τ‖ ≤ 3456 * 2 := by nlinarith [hE, hE1]
    calc 3456 * ‖DeltaFun τ‖ ≤ 3456 * 2 := h2
      _ ≤ 3456 * 2 * (scale τ) ^ N := le_mul_of_one_le_right (by norm_num) hN1
  have a2 : ‖(2:ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 2 * CP4 * (scale τ) ^ N := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 2 * ‖psi4 ℓ τ * E8Fun τ‖ ≤ 2 * (CP4 * (scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left mP4 (by norm_num)
      _ = 2 * CP4 * (scale τ) ^ N := by ring
  have a3 : ‖(2:ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 2 * CP2 * (scale τ) ^ N := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 2 * ‖psi2 ℓ τ * E10Fun τ‖ ≤ 2 * (CP2 * (scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left mP2 (by norm_num)
      _ = 2 * CP2 * (scale τ) ^ N := by ring
  have t1 := norm_add_le ((-3456:ℂ) * DeltaFun τ - (2:ℂ) * (psi4 ℓ τ * E8Fun τ))
    ((2:ℂ) * (psi2 ℓ τ * E10Fun τ))
  have t2 := norm_sub_le ((-3456:ℂ) * DeltaFun τ) ((2:ℂ) * (psi4 ℓ τ * E8Fun τ))
  have hsum2 : ‖(-3456:ℂ) * DeltaFun τ - (2:ℂ) * (psi4 ℓ τ * E8Fun τ)
      + (2:ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ (3456 * 2 + 2 * CP4 + 2 * CP2) * (scale τ) ^ N :=
    le_trans (tri3sa a1 a2 a3) (le_of_eq (by ring))
  have h0 : (0:ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg τ N
  calc ‖(-3456:ℂ) * DeltaFun τ - (2:ℂ) * (psi4 ℓ τ * E8Fun τ)
        + (2:ℂ) * (psi2 ℓ τ * E10Fun τ)‖
      ≤ (3456 * 2 + 2 * CP4 + 2 * CP2) * (scale τ) ^ N := hsum2
    _ ≤ (3456 * 2 + 2 * CP4 + 2 * CP2 + 1) * (scale τ) ^ N := by nlinarith [h0]
    _ = (3456 * 2 + 2 * CP4 + 2 * CP2 + 1) * (scale τ) ^ N := by ring

/-! ## The `FunnelB` interface -/

/-- `FunnelB f`: `‖f τ z‖ ≤ C (scale τ)^N (1+t) e^{-π(t - Im τ)}` on the tail region. -/
private def FunnelB (f : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
    ‖f τ z‖ ≤ C * (scale τ) ^ N * (1 + t) * Real.exp (-(Real.pi * (t - τ.im)))

private lemma FunnelB.add {f g : ℍ → ℍ → ℂ} (hf : FunnelB f) (hg : FunnelB g) :
    FunnelB (fun τ z => f τ z + g τ z) := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hf⟩ := hf
  obtain ⟨C₂, N₂, hC₂, hN₂, hg⟩ := hg
  refine ⟨C₁ + C₂, max N₁ N₂, by positivity, le_max_of_le_left hN₁, fun τ z t hτ ht hz => ?_⟩
  have hs₁ : (scale τ) ^ N₁ ≤ (scale τ) ^ (max N₁ N₂) := scale_rpow_mono (le_max_left _ _)
  have hs₂ : (scale τ) ^ N₂ ≤ (scale τ) ^ (max N₁ N₂) := scale_rpow_mono (le_max_right _ _)
  have hE0 : (0:ℝ) ≤ Real.exp (-(Real.pi * (t - τ.im))) := (Real.exp_pos _).le
  have ht0 : (0:ℝ) ≤ 1 + t := by linarith [hτ.2]
  have hs0 : (0:ℝ) ≤ (scale τ) ^ max N₁ N₂ := scale_rpow_nonneg τ _
  have h1 := hf τ z t hτ ht hz
  have h2 := hg τ z t hτ ht hz
  have hs1' : (0:ℝ) ≤ (scale τ) ^ N₁ := scale_rpow_nonneg τ N₁
  have hs2' : (0:ℝ) ≤ (scale τ) ^ N₂ := scale_rpow_nonneg τ N₂
  have h1' : ‖f τ z‖ ≤ C₁ * (scale τ) ^ max N₁ N₂ * (1 + t)
      * Real.exp (-(Real.pi * (t - τ.im))) := by
    refine le_trans h1 ?_
    apply mul_le_mul_of_nonneg_right _ hE0
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs₁ hC₁.le) ht0
  have h2' : ‖g τ z‖ ≤ C₂ * (scale τ) ^ max N₁ N₂ * (1 + t)
      * Real.exp (-(Real.pi * (t - τ.im))) := by
    refine le_trans h2 ?_
    apply mul_le_mul_of_nonneg_right _ hE0
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs₂ hC₂.le) ht0
  refine le_trans (norm_add_le (f τ z) (g τ z))
    (le_trans (add_le_add h1' h2') (le_of_eq (by ring)))

private lemma FunnelB.congr {f g : ℍ → ℍ → ℂ} (h : FunnelB f) (hfg : ∀ τ z, f τ z = g τ z) :
    FunnelB g := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  exact ⟨C, N, hC, hN, fun τ z t hτ ht hz => by rw [← hfg τ z]; exact hf τ z t hτ ht hz⟩

/-- `‖Sh τ z‖ ≤ 4` on the funnel tail. -/
private lemma Sh_bound : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.Sh τ z‖ ≤ C := by

  obtain ⟨C4, hC4, hE4b⟩ := Work.Asymptotics.E4Fun_bound
  refine ⟨C4 ^ 3 + (27 / 2) * Real.exp (-(2 * Real.pi)), by positivity, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz3 : 3 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hE4 : ‖E4Fun z ^ 3‖ ≤ C4 ^ 3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hE4b z (by rw [hzim]; linarith [hτ.2])) 3
  have hρ : ‖DeltaFun z * jInvariantFun τ‖ ≤ (27 / 2) * Real.exp (-(2 * Real.pi)) := by
    rw [norm_mul]
    have hj := KF24.norm_j_funnel τ hτ
    have hΔ := DeltaFun_le_two_exp z (by rw [hzim]; linarith [hτ.2])
    calc ‖DeltaFun z‖ * ‖jInvariantFun τ‖
        ≤ (2 * Real.exp (-(2 * Real.pi * z.im)))
            * ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) :=
          mul_le_mul hΔ hj (norm_nonneg _) (by positivity)
      _ = (27 / 2) * (Real.exp (-(2 * Real.pi * z.im)) * Real.exp (2 * Real.pi * τ.im)) := by ring
      _ = (27 / 2) * Real.exp (-(2 * Real.pi * z.im) + 2 * Real.pi * τ.im) := by
          rw [Real.exp_add]
      _ = (27 / 2) * Real.exp (-(2 * Real.pi * t) + 2 * Real.pi * τ.im) := by rw [hzim]
      _ ≤ (27 / 2) * Real.exp (-(2 * Real.pi)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          apply Real.exp_le_exp.mpr
          nlinarith [ht, Real.pi_pos, τ.im_pos, mul_pos Real.pi_pos τ.im_pos]
  rw [show Compact.Sh τ z = E4Fun z ^ 3 - DeltaFun z * jInvariantFun τ from rfl]
  calc ‖E4Fun z ^ 3 - DeltaFun z * jInvariantFun τ‖
      ≤ ‖E4Fun z ^ 3‖ + ‖DeltaFun z * jInvariantFun τ‖ := norm_sub_le _ _
    _ ≤ C4 ^ 3 + (27 / 2) * Real.exp (-(2 * Real.pi)) := add_le_add hE4 hρ

private lemma Tref24_bound (ℓ : LogLambdaData) :
    FunnelB (fun τ z => Compact.Tref24 ℓ τ z) := by
  obtain ⟨Cp0, Np0, hCp0, hNp0, hp0⟩ := R24_p0_bound ℓ
  obtain ⟨Chi, Nhi, hChi, hNhi, hhi⟩ := R24_hi_bound ℓ
  refine ⟨Cp0 + Chi * (1 + Real.pi + ‖Compact.cuspC ℓ‖), max Np0 Nhi, by positivity,
    le_max_of_le_left hNp0, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have ht0 : (0:ℝ) ≤ t := by linarith [hτ.2]
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hzn : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have he1 : ‖Ept z‖ ≤ 1 := KF24.norm_Ept_le_one' hz1
  have he0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hXc : ‖Compact.Xc ℓ z‖ ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t) := by
    have h := Compact.kaux_norm_Xc_le ℓ z
    rwa [hzn] at h
  have hs0 : scale τ ^ Np0 ≤ scale τ ^ max Np0 Nhi := scale_rpow_mono (le_max_left _ _)
  have hsi : scale τ ^ Nhi ≤ scale τ ^ max Np0 Nhi := scale_rpow_mono (le_max_right _ _)
  set N := max Np0 Nhi with hNset
  set E := Real.exp (2 * Real.pi * τ.im) with hEset
  have hE1 : (1:ℝ) ≤ E := by
    rw [hEset, ← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have h0 : Compact.R24_q0 ℓ τ = 0 := rfl
  -- term bounds for the five higher coefficients
  have b1 : ‖Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)‖
      ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖) := by
    rw [norm_mul]
    have h1 : ‖Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ‖
        ≤ (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖) := by
      have a1 : ‖Compact.Xc ℓ z * Compact.R24_q1 ℓ τ‖ ≤ ‖Compact.Xc ℓ z‖ * ‖Compact.R24_q1 ℓ τ‖ :=
        norm_mul_le _ _
      have a2 := norm_add_le (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ) (Compact.R24_p1 ℓ τ)
      nlinarith [a1, a2, norm_nonneg (Compact.Xc ℓ z), norm_nonneg (Compact.R24_q1 ℓ τ),
        norm_nonneg (Compact.R24_p1 ℓ τ)]
    calc ‖Ept z‖ * ‖Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ‖
        ≤ ‖Ept z‖ * ((1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)) :=
          mul_le_mul_of_nonneg_left h1 he0
      _ = ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖) := by ring
  have b2 : ‖Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)‖
      ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖) := by
    rw [norm_mul, norm_pow]
    have h1 : ‖Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ‖
        ≤ (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖) := by
      have a1 : ‖Compact.Xc ℓ z * Compact.R24_q2 ℓ τ‖ ≤ ‖Compact.Xc ℓ z‖ * ‖Compact.R24_q2 ℓ τ‖ :=
        norm_mul_le _ _
      have a2 := norm_add_le (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ) (Compact.R24_p2 ℓ τ)
      nlinarith [a1, a2, norm_nonneg (Compact.Xc ℓ z), norm_nonneg (Compact.R24_q2 ℓ τ),
        norm_nonneg (Compact.R24_p2 ℓ τ)]
    have h2 : ‖Ept z‖ ^ 2 ≤ ‖Ept z‖ := by nlinarith [he1, he0, sq_nonneg ‖Ept z‖]
    calc ‖Ept z‖ ^ 2 * ‖Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ‖
        ≤ ‖Ept z‖ * ((1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)) :=
          mul_le_mul h2 h1 (by positivity) he0
      _ = ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖) := by ring
  have b3 : ‖Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)‖
      ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖) := by
    rw [norm_mul, norm_pow]
    have h1 : ‖Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ‖
        ≤ (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖) := by
      have a1 : ‖Compact.Xc ℓ z * Compact.R24_q3 ℓ τ‖ ≤ ‖Compact.Xc ℓ z‖ * ‖Compact.R24_q3 ℓ τ‖ :=
        norm_mul_le _ _
      have a2 := norm_add_le (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ) (Compact.R24_p3 ℓ τ)
      nlinarith [a1, a2, norm_nonneg (Compact.Xc ℓ z), norm_nonneg (Compact.R24_q3 ℓ τ),
        norm_nonneg (Compact.R24_p3 ℓ τ)]
    have h2 : ‖Ept z‖ ^ 3 ≤ ‖Ept z‖ := by
      have h3 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ he0 he1
      nlinarith [h3, he0, pow_nonneg he0 2]
    calc ‖Ept z‖ ^ 3 * ‖Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ‖
        ≤ ‖Ept z‖ * ((1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)) :=
          mul_le_mul h2 h1 (by positivity) he0
      _ = ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖) := by ring
  have b4 : ‖Ept z ^ 4 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ)‖
      ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖) := by
    rw [norm_mul, norm_pow]
    have h1 : ‖Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ‖
        ≤ (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖) := by
      have a1 : ‖Compact.Xc ℓ z * Compact.R24_q4 ℓ τ‖ ≤ ‖Compact.Xc ℓ z‖ * ‖Compact.R24_q4 ℓ τ‖ :=
        norm_mul_le _ _
      have a2 := norm_add_le (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ) (Compact.R24_p4 ℓ τ)
      nlinarith [a1, a2, norm_nonneg (Compact.Xc ℓ z), norm_nonneg (Compact.R24_q4 ℓ τ),
        norm_nonneg (Compact.R24_p4 ℓ τ)]
    have h2 : ‖Ept z‖ ^ 4 ≤ ‖Ept z‖ := by
      have h3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ he0 he1
      nlinarith [h3, he0, pow_nonneg he0 3]
    calc ‖Ept z‖ ^ 4 * ‖Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ‖
        ≤ ‖Ept z‖ * ((1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)) :=
          mul_le_mul h2 h1 (by positivity) he0
      _ = ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖) := by ring
  have b5 : ‖Ept z ^ 5 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ)‖
      ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖) := by
    rw [norm_mul, norm_pow]
    have h1 : ‖Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ‖
        ≤ (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖) := by
      have a1 : ‖Compact.Xc ℓ z * Compact.R24_q5 ℓ τ‖ ≤ ‖Compact.Xc ℓ z‖ * ‖Compact.R24_q5 ℓ τ‖ :=
        norm_mul_le _ _
      have a2 := norm_add_le (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ) (Compact.R24_p5 ℓ τ)
      nlinarith [a1, a2, norm_nonneg (Compact.Xc ℓ z), norm_nonneg (Compact.R24_q5 ℓ τ),
        norm_nonneg (Compact.R24_p5 ℓ τ)]
    have h2 : ‖Ept z‖ ^ 5 ≤ ‖Ept z‖ := by
      have h3 : ‖Ept z‖ ^ 4 ≤ 1 := pow_le_one₀ he0 he1
      nlinarith [h3, he0, pow_nonneg he0 4]
    calc ‖Ept z‖ ^ 5 * ‖Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ‖
        ≤ ‖Ept z‖ * ((1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖)) :=
          mul_le_mul h2 h1 (by positivity) he0
      _ = ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖) := by ring
  -- assemble `R24`
  have hR24 : ‖Compact.R24 ℓ τ z‖
      ≤ Cp0 * (scale τ) ^ N + ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (Chi * (scale τ) ^ N * E) := by
    have hfirst : ‖Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ‖
        ≤ Cp0 * (scale τ) ^ N := by
      rw [h0, mul_zero, zero_add]
      exact le_trans (hp0 τ hτ) (mul_le_mul_of_nonneg_left hs0 hCp0.le)
    have hrest := hhi τ hτ
    have hrest' : (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)
        + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
        + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
        + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
        + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖)
        ≤ Chi * (scale τ) ^ N * E := by
      refine le_trans hrest ?_
      rw [hNset]
      have hs : Chi * (scale τ) ^ Nhi ≤ Chi * (scale τ) ^ max Np0 Nhi :=
        mul_le_mul_of_nonneg_left hsi hChi.le
      exact mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
    have hB : ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) *
          ((‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)
            + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
            + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
            + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
            + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖))
        ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (Chi * (scale τ) ^ N * E) :=
      mul_le_mul_of_nonneg_left hrest' (by positivity)
    have hR24eq : Compact.R24 ℓ τ z
        = (Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ)
          + Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)
          + Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)
          + Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)
          + Ept z ^ 4 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ)
          + Ept z ^ 5 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ) := rfl
    rw [hR24eq]
    have t1 := norm_add_le ((Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ)
        + Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)
        + Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)
        + Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)
        + Ept z ^ 4 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ))
      (Ept z ^ 5 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ))
    have t2 := norm_add_le ((Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ)
        + Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)
        + Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)
        + Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ))
      (Ept z ^ 4 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ))
    have t3 := norm_add_le ((Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ)
        + Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)
        + Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ))
      (Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ))
    have t4 := norm_add_le ((Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ)
        + Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ))
      (Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ))
    have t5 := norm_add_le (Compact.Xc ℓ z * Compact.R24_q0 ℓ τ + Compact.R24_p0 ℓ τ)
      (Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ))
    have hsum5 : ‖Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)‖
        + ‖Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)‖
        + ‖Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)‖
        + ‖Ept z ^ 4 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ)‖
        + ‖Ept z ^ 5 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ)‖
        ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) *
          ((‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)
            + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
            + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
            + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
            + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖)) := by
      have hk : (0:ℝ) ≤ (‖Compact.R24_q1 ℓ τ‖ + ‖Compact.R24_p1 ℓ τ‖)
          + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
          + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
          + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
          + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hk
        (by positivity : (0:ℝ) ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖))
      have hsm : ‖Ept z * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)‖
          + ‖Ept z ^ 2 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)‖
          + ‖Ept z ^ 3 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)‖
          + ‖Ept z ^ 4 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ)‖
          + ‖Ept z ^ 5 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ)‖
          ≤ ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * ((‖Compact.R24_q1 ℓ τ‖
              + ‖Compact.R24_p1 ℓ τ‖)
            + (‖Compact.R24_q2 ℓ τ‖ + ‖Compact.R24_p2 ℓ τ‖)
            + (‖Compact.R24_q3 ℓ τ‖ + ‖Compact.R24_p3 ℓ τ‖)
            + (‖Compact.R24_q4 ℓ τ‖ + ‖Compact.R24_p4 ℓ τ‖)
            + (‖Compact.R24_q5 ℓ τ‖ + ‖Compact.R24_p5 ℓ τ‖)) := by
        nlinarith [b1, b2, b3, b4, b5, hmul]
      exact hsm
    linarith [t1, t2, t3, t4, t5, hfirst, hsum5, hB]
  rw [show (fun τ z => Compact.Tref24 ℓ τ z) τ z = Compact.Tref24 ℓ τ z from rfl,
    Compact.Tref24_eq ℓ τ z]
  have hmain := norm_mul_le (Ept z) (Compact.R24 ℓ τ z)
  have hstep : ‖Ept z‖ * ‖Compact.R24 ℓ τ z‖
      ≤ Real.exp (-(Real.pi * t)) * (Cp0 * (scale τ) ^ N
          + Real.exp (-(Real.pi * t)) * (1 + ‖Compact.Xc ℓ z‖) * (Chi * (scale τ) ^ N * E)) := by
    have h1 : ‖Ept z‖ * ‖Compact.R24 ℓ τ z‖
        ≤ ‖Ept z‖ * (Cp0 * (scale τ) ^ N
          + ‖Ept z‖ * (1 + ‖Compact.Xc ℓ z‖) * (Chi * (scale τ) ^ N * E)) :=
      mul_le_mul_of_nonneg_left hR24 he0
    rw [he] at h1
    rw [he]
    exact h1
  refine le_trans (le_trans hmain hstep) ?_
  -- final exponential bookkeeping
  have hXc' : 1 + ‖Compact.Xc ℓ z‖ ≤ 1 + (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t) := by linarith [hXc]
  have hB1 : Real.exp (-(Real.pi * t)) * Cp0 * (scale τ) ^ N
      ≤ Cp0 * (scale τ) ^ N * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
    have hle : τ.im ≤ t := by linarith [hτ.2]
    have h : Real.exp (-(Real.pi * t)) ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
      simpa using exp_decay_le (τ := τ) (t := t) 1 le_rfl hle
    have h1t : (1:ℝ) ≤ 1 + t := by linarith
    calc Real.exp (-(Real.pi * t)) * Cp0 * (scale τ) ^ N
        = Cp0 * (scale τ) ^ N * Real.exp (-(Real.pi * t)) := by ring
      _ ≤ Cp0 * (scale τ) ^ N * Real.exp (-(Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left h (pos_f2 hCp0.le)
      _ ≤ Cp0 * (scale τ) ^ N * Real.exp (-(Real.pi * (t - τ.im))) * (1 + t) :=
          le_mul_of_one_le_right (by positivity) h1t
      _ = Cp0 * (scale τ) ^ N * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by ring
  have hB2 : Real.exp (-(Real.pi * t)) * (Real.exp (-(Real.pi * t)) * (1 + ‖Compact.Xc ℓ z‖))
        * (Chi * (scale τ) ^ N * E)
      ≤ Chi * (1 + Real.pi + ‖Compact.cuspC ℓ‖) * (scale τ) ^ N * (1 + t)
        * Real.exp (-(Real.pi * (t - τ.im))) := by
    have he2 : Real.exp (-(Real.pi * t)) * (Real.exp (-(Real.pi * t)) * E)
        = Real.exp (-(2 * Real.pi * t) + 2 * Real.pi * τ.im) := by
      rw [hEset, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have hdec := exp_two_decay (τ := τ) (t := t) ht
    have hX1 : (1:ℝ) ≤ 1 + t := by linarith
    have hX2 : 1 + ‖Compact.Xc ℓ z‖ ≤ (1 + Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t) := by
      have h0 : (0:ℝ) ≤ 1 + ‖Compact.Xc ℓ z‖ := by positivity
      nlinarith [hXc', hX1, Real.pi_pos, norm_nonneg (Compact.cuspC ℓ)]
    have hchi0 : (0:ℝ) ≤ Chi := hChi.le
    have hsN0 : (0:ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg τ N
    have hgoal : Real.exp (-(Real.pi * t)) * (Real.exp (-(Real.pi * t)) * (1 + ‖Compact.Xc ℓ z‖))
        * (Chi * (scale τ) ^ N * E)
        = (Chi * (1 + ‖Compact.Xc ℓ z‖)) * ((scale τ) ^ N
            * (Real.exp (-(Real.pi * t)) * (Real.exp (-(Real.pi * t)) * E))) := by ring
    rw [hgoal]
    calc (Chi * (1 + ‖Compact.Xc ℓ z‖)) * ((scale τ) ^ N
            * (Real.exp (-(Real.pi * t)) * (Real.exp (-(Real.pi * t)) * E)))
        ≤ (Chi * ((1 + Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t))) * ((scale τ) ^ N
            * Real.exp (-(Real.pi * (t - τ.im)))) := by
          rw [he2]
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hX2 hchi0
          · exact mul_le_mul_of_nonneg_left hdec hsN0
          · positivity
          · positivity
      _ = Chi * (1 + Real.pi + ‖Compact.cuspC ℓ‖) * (scale τ) ^ N * (1 + t)
            * Real.exp (-(Real.pi * (t - τ.im))) := by ring
  have hfinal : Real.exp (-(Real.pi * t)) * (Cp0 * (scale τ) ^ N
        + Real.exp (-(Real.pi * t)) * (1 + ‖Compact.Xc ℓ z‖) * (Chi * (scale τ) ^ N * E))
      ≤ (Cp0 + Chi * (1 + Real.pi + ‖Compact.cuspC ℓ‖)) * (scale τ) ^ N * (1 + t)
        * Real.exp (-(Real.pi * (t - τ.im))) := by
    have hsplit : Real.exp (-(Real.pi * t)) * (Cp0 * (scale τ) ^ N
          + Real.exp (-(Real.pi * t)) * (1 + ‖Compact.Xc ℓ z‖) * (Chi * (scale τ) ^ N * E))
        = Real.exp (-(Real.pi * t)) * Cp0 * (scale τ) ^ N
          + Real.exp (-(Real.pi * t)) * (Real.exp (-(Real.pi * t)) * (1 + ‖Compact.Xc ℓ z‖))
            * (Chi * (scale τ) ^ N * E) := by ring
    rw [hsplit]
    refine le_trans (add_le_add hB1 hB2) (le_of_eq (by ring))
  exact le_trans hfinal (le_of_eq (by ring))

/-! ## The seven deviation terms -/

private lemma Dev1_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev1 ℓ τ z) := by
  obtain ⟨Cs, hCs, hs⟩ := Sinvref_bound
  obtain ⟨Cad, Nad, hCad, hNad, had⟩ := A24diff_bound ℓ
  obtain ⟨-, -, hDr⟩ := Dref_bound
  refine ⟨25 * Cs * Cad, Nad, by positivity, hNad, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have he1 : ‖Ept z‖ ≤ 1 := KF24.norm_Ept_le_one' hz1
  have he0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hne : ‖Ept z‖ ≠ 0 := by rw [he]; exact Real.exp_ne_zero _
  have hSb := hs τ z t hτ ht hz
  have hDb := hDr z hz1
  have hAb := had τ z t hτ ht hz
  have h3 : ‖Ept z‖ ^ 3 ≤ ‖Ept z‖ := by
    have h2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ he0 he1
    nlinarith [h2, he0, pow_nonneg he0 2]
  have hinv : (‖Ept z‖ ^ 2)⁻¹ * ‖Ept z‖ ^ 3 = ‖Ept z‖ := by
    rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hne)]; ring
  have hkey : Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [he, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, τ.im_pos]
  rw [show (fun τ z => Compact.Dev1 ℓ τ z) τ z = Compact.Dev1 ℓ τ z from rfl,
    show Compact.Dev1 ℓ τ z = Compact.Sinvref τ z * Compact.Dref z
      * (Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z) from rfl, norm_mul, norm_mul]
  have hE1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ.2])
  calc ‖Compact.Sinvref τ z‖ * ‖Compact.Dref z‖
        * ‖Compact.A24 ℓ τ z - Compact.A24ref ℓ τ z‖
      ≤ Cs * ((‖Ept z‖ ^ 2)⁻¹ + 24) * (Cad * (scale τ) ^ Nad * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 3) := by
        gcongr
    _ = Cs * Cad * (scale τ) ^ Nad * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
          * ((‖Ept z‖ ^ 2)⁻¹ * ‖Ept z‖ ^ 3 + 24 * ‖Ept z‖ ^ 3) := by ring
    _ ≤ Cs * Cad * (scale τ) ^ Nad * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
          * (‖Ept z‖ + 24 * ‖Ept z‖) := by
        have h0 : (0:ℝ) ≤ Cs * Cad * (scale τ) ^ Nad * (1 + t)
            * Real.exp (-(2 * Real.pi * τ.im)) :=
          pos_f4 (mul_nonneg hCs.le hCad.le) (by nlinarith [τ.im_pos, hτ.2])
            (Real.exp_pos _).le
        have hc : (‖Ept z‖ ^ 2)⁻¹ * ‖Ept z‖ ^ 3 + 24 * ‖Ept z‖ ^ 3
            ≤ ‖Ept z‖ + 24 * ‖Ept z‖ := by
          rw [hinv]; nlinarith [h3]
        exact mul_le_mul_of_nonneg_left hc h0
    _ = 25 * Cs * Cad * (scale τ) ^ Nad * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
          * ‖Ept z‖ := by ring
    _ ≤ 25 * Cs * Cad * (scale τ) ^ Nad * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ 25 * Cs * Cad * (scale τ) ^ Nad * (1 + t) :=
          pos_f3 (by positivity) (by nlinarith [τ.im_pos, hτ.2])
        calc 25 * Cs * Cad * (scale τ) ^ Nad * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
              * ‖Ept z‖
            = 25 * Cs * Cad * (scale τ) ^ Nad * (1 + t)
              * (Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖) := by ring
          _ ≤ 25 * Cs * Cad * (scale τ) ^ Nad * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))) := mul_le_mul_of_nonneg_left hkey h0

private lemma Dev2_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev2 ℓ τ z) := by
  obtain ⟨Cs, hCs, hs⟩ := Sinvref_bound
  obtain ⟨CdΔ, hCdΔ, hdΔ⟩ := dDelta_bound
  obtain ⟨CA, NA, hCA, hNA, hA⟩ := A24_bound ℓ
  refine ⟨Cs * CdΔ * CA, NA, by positivity, hNA, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have hSb := hs τ z t hτ ht hz
  have hdb := hdΔ z hz1
  have hAb := hA τ z t hτ ht hz
  have hkey : Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 2
      ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [he, show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, τ.im_pos, hτ.2]
  rw [show (fun τ z => Compact.Dev2 ℓ τ z) τ z = Compact.Dev2 ℓ τ z from rfl,
    show Compact.Dev2 ℓ τ z = Compact.Sinvref τ z * Compact.dDelta z * Compact.A24 ℓ τ z
      from rfl, norm_mul, norm_mul]
  calc ‖Compact.Sinvref τ z‖ * ‖Compact.dDelta z‖ * ‖Compact.A24 ℓ τ z‖
      ≤ Cs * (CdΔ * ‖Ept z‖ ^ 2) * (CA * (scale τ) ^ NA * (1 + t)
          * Real.exp (-(2 * Real.pi * τ.im))) := by
        gcongr
    _ = Cs * CdΔ * CA * (scale τ) ^ NA * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
          * ‖Ept z‖ ^ 2 := by ring
    _ ≤ Cs * CdΔ * CA * (scale τ) ^ NA * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ Cs * CdΔ * CA * (scale τ) ^ NA * (1 + t) :=
          pos_f3 (by positivity) (by nlinarith [τ.im_pos, hτ.2])
        calc Cs * CdΔ * CA * (scale τ) ^ NA * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
              * ‖Ept z‖ ^ 2
            = Cs * CdΔ * CA * (scale τ) ^ NA * (1 + t)
              * (Real.exp (-(2 * Real.pi * τ.im)) * ‖Ept z‖ ^ 2) := by ring
          _ ≤ Cs * CdΔ * CA * (scale τ) ^ NA * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))) := mul_le_mul_of_nonneg_left hkey h0

private lemma Dev3_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev3 ℓ τ z) := by
  obtain ⟨Cds, Nds, hCds, hNds, hds⟩ := dSinv_bound
  obtain ⟨K, hK, hKb⟩ := invDelta_bound
  obtain ⟨CA, NA, hCA, hNA, hA⟩ := A24_bound ℓ
  refine ⟨Cds * (2 + 2 * K) * CA, Nds + NA, by positivity, by positivity,
    fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have hdsb := hds τ z t hτ ht hz
  have hKb := hKb z hz1
  have hAb := hA τ z t hτ ht hz
  have hDelta : (‖Ept z‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * t) := by
    rw [he, show (Real.exp (-(Real.pi * t)) ^ 2)⁻¹ = Real.exp (2 * Real.pi * t) by
      rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
        rw [sq, ← Real.exp_add]; congr 1; ring, ← Real.exp_neg, neg_neg]]
  have hs : scale τ ^ Nds * scale τ ^ NA = scale τ ^ (Nds + NA) :=
    (Real.rpow_add (scale_pos τ) _ _).symm
  have ht0 : (0:ℝ) < t := by linarith [hτ.2]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpt : (0:ℝ) < Real.pi * t := mul_pos hpi ht0
  have hpb : (0:ℝ) < Real.pi * τ.im := mul_pos hpi τ.im_pos
  have hle2 : τ.im ≤ t := by linarith [hτ.2]
  have hptb : Real.pi * τ.im ≤ Real.pi * t := mul_le_mul_of_nonneg_left hle2 hpi.le
  have hnorm1 : -(Real.pi * (t - τ.im)) + 2 * Real.pi * τ.im
      = -(Real.pi * t) + 3 * (Real.pi * τ.im) := by ring
  have hA1 : Real.exp (-(4 * Real.pi * t)) * Real.exp (2 * Real.pi * t)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im) :=
    exp_mul_le_exp_mul (a := -(4 * Real.pi * t)) (b := 2 * Real.pi * t)
      (c := -(Real.pi * (t - τ.im))) (d := 2 * Real.pi * τ.im) (exp_arg_A1 ht)
  have hA3 : K * Real.exp (-(4 * Real.pi * t))
      ≤ K * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im)) :=
    mul_le_mul_of_nonneg_left
      (exp1_le_exp_mul (a := -(4 * Real.pi * t)) (c := -(Real.pi * (t - τ.im)))
        (d := 2 * Real.pi * τ.im) (exp_arg_A3 ht)) hK
  have hA2 : Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)
        * Real.exp (2 * Real.pi * t)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im) :=
    exp3_le_exp2 (a := -(4 * Real.pi * t)) (b := 4 * Real.pi * τ.im) (c := 2 * Real.pi * t)
      (d := -(Real.pi * (t - τ.im))) (e := 2 * Real.pi * τ.im) (exp_arg_A2 ht)
  have hA4 : K * (Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im))
      ≤ K * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im)) :=
    mul_le_mul_of_nonneg_left
      (exp_mul_le_exp_mul (a := -(4 * Real.pi * t)) (b := 4 * Real.pi * τ.im)
        (c := -(Real.pi * (t - τ.im))) (d := 2 * Real.pi * τ.im) (exp_arg_A4 ht)) hK
  have hbracket : (Real.exp (-(4 * Real.pi * t))
        + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im))
      * (Real.exp (2 * Real.pi * t) + K)
      ≤ (2 + 2 * K) * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im)) := by
    have hd : (Real.exp (-(4 * Real.pi * t))
          + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im))
        * (Real.exp (2 * Real.pi * t) + K)
        = (Real.exp (-(4 * Real.pi * t)) * Real.exp (2 * Real.pi * t)
            + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)
              * Real.exp (2 * Real.pi * t))
          + (K * Real.exp (-(4 * Real.pi * t))
            + K * (Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im))) := by ring
    have htgt : (2 + 2 * K) * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im))
        = (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im)
            + Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im))
          + (K * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im))
            + K * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im))) := by ring
    rw [hd, htgt]
    exact add_le_add (add_le_add hA1 hA2) (add_le_add hA3 hA4)
  have hfold : Compact.Dev3 ℓ τ z = Compact.dSinv τ z * (DeltaFun z)⁻¹ * Compact.A24 ℓ τ z := rfl
  rw [show (fun τ z => Compact.Dev3 ℓ τ z) τ z = Compact.Dev3 ℓ τ z from rfl, hfold,
    norm_mul, norm_mul]
  calc ‖Compact.dSinv τ z‖ * ‖(DeltaFun z)⁻¹‖ * ‖Compact.A24 ℓ τ z‖
      ≤ (Cds * (scale τ) ^ Nds * (Real.exp (-(4 * Real.pi * t))
            + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)))
          * ((‖Ept z‖ ^ 2)⁻¹ + K)
          * (CA * (scale τ) ^ NA * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))) := by
        gcongr
    _ = Cds * CA * (scale τ) ^ (Nds + NA) * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
          * ((Real.exp (-(4 * Real.pi * t))
              + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im))
            * ((‖Ept z‖ ^ 2)⁻¹ + K)) := by
        rw [← hs]; ring
    _ ≤ Cds * CA * (scale τ) ^ (Nds + NA) * (1 + t) * Real.exp (-(2 * Real.pi * τ.im))
          * ((2 + 2 * K) * (Real.exp (-(Real.pi * (t - τ.im))) * Real.exp (2 * Real.pi * τ.im))) := by
        rw [hDelta]
        have h0 : (0:ℝ) ≤ Cds * CA * (scale τ) ^ (Nds + NA) * (1 + t)
            * Real.exp (-(2 * Real.pi * τ.im)) :=
          pos_f4 (by positivity) (by nlinarith [τ.im_pos, hτ.2]) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hbracket h0
    _ = Cds * (2 + 2 * K) * CA * (scale τ) ^ (Nds + NA) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h1 : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
          rw [← Real.exp_add]; simp
        rw [show Cds * CA * (scale τ) ^ (Nds + NA) * (1 + t)
              * Real.exp (-(2 * Real.pi * τ.im))
              * ((2 + 2 * K) * (Real.exp (-(Real.pi * (t - τ.im)))
                * Real.exp (2 * Real.pi * τ.im)))
            = Cds * (2 + 2 * K) * CA * (scale τ) ^ (Nds + NA) * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im)))
              * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im)) by ring]
        rw [h1]; ring

private lemma Dev4_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev4 ℓ τ z) := by
  obtain ⟨Cs, hCs, hs⟩ := Sinvref_bound
  obtain ⟨C0, N0, hC0, hN0, hC0b⟩ := C24_bound ℓ
  obtain ⟨CdW, hCdW, hdW⟩ := dW_bound
  refine ⟨Cs * C0 * CdW, N0, by positivity, hN0, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have hSb := hs τ z t hτ ht hz
  have hCb := hC0b τ hτ
  have hdb := hdW z hz1
  have hkey : ‖Ept z‖ ^ 3 ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [he, show Real.exp (-(Real.pi * t)) ^ 3 = Real.exp (-(3 * Real.pi * t)) by
      rw [show (3:ℕ) = 3 from rfl, ← Real.exp_nat_mul]; congr 1; ring]
    exact exp_decay_le (τ := τ) (t := t) 3 (by norm_num) (by linarith [hτ.2])
  rw [show (fun τ z => Compact.Dev4 ℓ τ z) τ z = Compact.Dev4 ℓ τ z from rfl,
    show Compact.Dev4 ℓ τ z = Compact.Sinvref τ z * Compact.C24 ℓ τ * Compact.dW z from rfl,
    norm_mul, norm_mul]
  calc ‖Compact.Sinvref τ z‖ * ‖Compact.C24 ℓ τ‖ * ‖Compact.dW z‖
      ≤ Cs * (C0 * (scale τ) ^ N0) * (CdW * ‖Ept z‖ ^ 3) := by
        gcongr
    _ = Cs * C0 * CdW * (scale τ) ^ N0 * ‖Ept z‖ ^ 3 := by ring
    _ ≤ Cs * C0 * CdW * (scale τ) ^ N0 * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ Cs * C0 * CdW * (scale τ) ^ N0 := pos_f2 (by positivity)
        exact mul_le_mul_of_nonneg_left hkey h0
    _ ≤ Cs * C0 * CdW * (scale τ) ^ N0 * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ Cs * C0 * CdW * (scale τ) ^ N0
            * Real.exp (-(Real.pi * (t - τ.im))) := pos_f3 (by positivity) (Real.exp_pos _).le
        have h1 : (1:ℝ) ≤ 1 + t := by linarith
        calc Cs * C0 * CdW * (scale τ) ^ N0 * Real.exp (-(Real.pi * (t - τ.im)))
            = Cs * C0 * CdW * (scale τ) ^ N0 * Real.exp (-(Real.pi * (t - τ.im))) * 1 := by ring
          _ ≤ Cs * C0 * CdW * (scale τ) ^ N0 * Real.exp (-(Real.pi * (t - τ.im))) * (1 + t) :=
              mul_le_mul_of_nonneg_left h1 h0
          _ = Cs * C0 * CdW * (scale τ) ^ N0 * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by ring

private lemma Dev5_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev5 ℓ τ z) := by
  obtain ⟨Cds, Nds, hCds, hNds, hds⟩ := dSinv_bound
  obtain ⟨C0, N0, hC0, hN0, hC0b⟩ := C24_bound ℓ
  obtain ⟨CW, hCW, hW⟩ := W_bound
  refine ⟨Cds * C0 * CW * 2, Nds + N0, by positivity, by positivity, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have hdsb := hds τ z t hτ ht hz
  have hCb := hC0b τ hτ
  have hWb := hW z hz1
  have h1 : Real.exp (-(4 * Real.pi * t)) ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, τ.im_pos, mul_pos Real.pi_pos τ.im_pos]
  have h3 : Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)
      ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    have h := exp_four_decay (τ := τ) (t := t) ht
    simpa only [← Real.exp_add] using h
  have hsum : Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)
      + Real.exp (-(4 * Real.pi * t)) ≤ 2 * Real.exp (-(Real.pi * (t - τ.im))) := by
    linarith [h1, h3]
  rw [show (fun τ z => Compact.Dev5 ℓ τ z) τ z = Compact.Dev5 ℓ τ z from rfl,
    show Compact.Dev5 ℓ τ z = Compact.dSinv τ z * Compact.C24 ℓ τ * WFun z from rfl,
    norm_mul, norm_mul]
  have hs : scale τ ^ Nds * scale τ ^ N0 = scale τ ^ (Nds + N0) :=
    (Real.rpow_add (scale_pos τ) _ _).symm
  calc ‖Compact.dSinv τ z‖ * ‖Compact.C24 ℓ τ‖ * ‖WFun z‖
      ≤ (Cds * (scale τ) ^ Nds * (Real.exp (-(4 * Real.pi * t))
            + Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)))
          * (C0 * (scale τ) ^ N0) * CW := by
        gcongr
    _ = Cds * C0 * CW * (scale τ) ^ (Nds + N0)
          * (Real.exp (-(4 * Real.pi * t)) + Real.exp (-(4 * Real.pi * t))
            * Real.exp (4 * Real.pi * τ.im)) := by
        rw [← hs]; ring
    _ ≤ Cds * C0 * CW * (scale τ) ^ (Nds + N0)
          * (2 * Real.exp (-(Real.pi * (t - τ.im)))) := by
        have h0 : (0:ℝ) ≤ Cds * C0 * CW * (scale τ) ^ (Nds + N0) := pos_f2 (by positivity)
        have h4 : Real.exp (-(4 * Real.pi * t)) + Real.exp (-(4 * Real.pi * t))
            * Real.exp (4 * Real.pi * τ.im)
            ≤ 2 * Real.exp (-(Real.pi * (t - τ.im))) := by
          rw [show Real.exp (-(4 * Real.pi * t)) + Real.exp (-(4 * Real.pi * t))
              * Real.exp (4 * Real.pi * τ.im)
              = Real.exp (-(4 * Real.pi * t)) * Real.exp (4 * Real.pi * τ.im)
                + Real.exp (-(4 * Real.pi * t)) by ring]
          exact hsum
        exact mul_le_mul_of_nonneg_left h4 h0
    _ ≤ Cds * C0 * CW * 2 * (scale τ) ^ (Nds + N0) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ Cds * C0 * CW * 2 * (scale τ) ^ (Nds + N0)
            * Real.exp (-(Real.pi * (t - τ.im))) := pos_f3 (by positivity) (Real.exp_pos _).le
        have h1t : (1:ℝ) ≤ 1 + t := by linarith
        calc Cds * C0 * CW * (scale τ) ^ (Nds + N0) * (2 * Real.exp (-(Real.pi * (t - τ.im))))
            = Cds * C0 * CW * 2 * (scale τ) ^ (Nds + N0)
              * Real.exp (-(Real.pi * (t - τ.im))) * 1 := by ring
          _ ≤ Cds * C0 * CW * 2 * (scale τ) ^ (Nds + N0)
              * Real.exp (-(Real.pi * (t - τ.im))) * (1 + t) :=
              mul_le_mul_of_nonneg_left h1t h0
          _ = Cds * C0 * CW * 2 * (scale τ) ^ (Nds + N0) * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))) := by ring

private lemma Dev6_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev6 ℓ τ z) := by
  obtain ⟨-, -, hDr⟩ := Dref_bound
  obtain ⟨CdW, hCdW, hdW⟩ := dW_bound
  obtain ⟨CB, NB, hCB, hNB, hCBb⟩ := C24_bound ℓ
  obtain ⟨CB, NB, hCB, hNB, hB0b⟩ := B24_bound ℓ
  refine ⟨CB * CdW * 25, NB, by positivity, hNB, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have hDb := hDr z hz1
  have hdb := hdW z hz1
  have hBb := hB0b τ hτ
  have hDref : ‖Compact.Dref z‖ ≤ Real.exp (2 * Real.pi * t) + 24 := by
    refine le_trans hDb ?_
    rw [he, show (Real.exp (-(Real.pi * t)) ^ 2)⁻¹ = Real.exp (2 * Real.pi * t) by
      rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
        rw [sq, ← Real.exp_add]; congr 1; ring, ← Real.exp_neg, neg_neg]]
  have hkey : (Real.exp (2 * Real.pi * t) + 24) * ‖Ept z‖ ^ 3
      ≤ 25 * Real.exp (-(Real.pi * (t - τ.im))) := by
    have h1 : Real.exp (2 * Real.pi * t) * ‖Ept z‖ ^ 3
        ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
      rw [he, show Real.exp (-(Real.pi * t)) ^ 3 = Real.exp (-(3 * Real.pi * t)) by
        rw [show (3:ℕ) = 3 from rfl, ← Real.exp_nat_mul]; congr 1; ring,
        ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, τ.im_pos, mul_pos Real.pi_pos τ.im_pos]
    have h2 : 24 * ‖Ept z‖ ^ 3 ≤ 24 * Real.exp (-(Real.pi * (t - τ.im))) := by
      have h3 : ‖Ept z‖ ^ 3 ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
        rw [he, show Real.exp (-(Real.pi * t)) ^ 3 = Real.exp (-(3 * Real.pi * t)) by
          rw [show (3:ℕ) = 3 from rfl, ← Real.exp_nat_mul]; congr 1; ring]
        exact exp_decay_le (τ := τ) (t := t) 3 (by norm_num) (by linarith [hτ.2])
      linarith
    have h4 : (Real.exp (2 * Real.pi * t) + 24) * ‖Ept z‖ ^ 3
        = Real.exp (2 * Real.pi * t) * ‖Ept z‖ ^ 3 + 24 * ‖Ept z‖ ^ 3 := by ring
    rw [h4]
    linarith [h1, h2]
  rw [show (fun τ z => Compact.Dev6 ℓ τ z) τ z = Compact.Dev6 ℓ τ z from rfl,
    show Compact.Dev6 ℓ τ z = -Compact.Dref z * Compact.dW z * Compact.B24 ℓ τ from rfl,
    norm_mul, norm_mul, norm_neg]
  calc ‖Compact.Dref z‖ * ‖Compact.dW z‖ * ‖Compact.B24 ℓ τ‖
      ≤ (Real.exp (2 * Real.pi * t) + 24) * (CdW * ‖Ept z‖ ^ 3) * (CB * (scale τ) ^ NB) := by
        gcongr
    _ = CB * CdW * (Real.exp (2 * Real.pi * t) + 24) * ‖Ept z‖ ^ 3 * (scale τ) ^ NB := by ring
    _ ≤ CB * CdW * (25 * Real.exp (-(Real.pi * (t - τ.im)))) * (scale τ) ^ NB := by
        have h0 : (0:ℝ) ≤ CB * CdW * (scale τ) ^ NB := pos_f2 (by positivity)
        have h5 : CB * CdW * (Real.exp (2 * Real.pi * t) + 24) * ‖Ept z‖ ^ 3
            ≤ CB * CdW * (25 * Real.exp (-(Real.pi * (t - τ.im)))) := by
          calc CB * CdW * (Real.exp (2 * Real.pi * t) + 24) * ‖Ept z‖ ^ 3
              = (CB * CdW) * ((Real.exp (2 * Real.pi * t) + 24) * ‖Ept z‖ ^ 3) := by ring
            _ ≤ (CB * CdW) * (25 * Real.exp (-(Real.pi * (t - τ.im)))) :=
                mul_le_mul_of_nonneg_left hkey (mul_nonneg hCB.le hCdW.le)
            _ = CB * CdW * (25 * Real.exp (-(Real.pi * (t - τ.im)))) := by ring
        exact mul_le_mul_of_nonneg_right h5 (scale_rpow_nonneg τ NB)
    _ = CB * CdW * 25 * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im))) := by ring
    _ ≤ CB * CdW * 25 * (scale τ) ^ NB * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ CB * CdW * 25 * (scale τ) ^ NB
            * Real.exp (-(Real.pi * (t - τ.im))) := pos_f3 (by positivity) (Real.exp_pos _).le
        have h1t : (1:ℝ) ≤ 1 + t := by linarith
        calc CB * CdW * 25 * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im)))
            = CB * CdW * 25 * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im))) * 1 := by ring
          _ ≤ CB * CdW * 25 * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im))) * (1 + t) :=
              mul_le_mul_of_nonneg_left h1t h0
          _ = CB * CdW * 25 * (scale τ) ^ NB * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))) := by ring

private lemma Dev7_bound (ℓ : LogLambdaData) : FunnelB (fun τ z => Compact.Dev7 ℓ τ z) := by
  obtain ⟨CdΔ, hCdΔ, hdΔ⟩ := dDelta_bound
  obtain ⟨CW, hCW, hW⟩ := W_bound
  obtain ⟨C0, N0, hC0, hN0, hC0b⟩ := C24_bound ℓ
  obtain ⟨CB, NB, hCB, hNB, hB0b⟩ := B24_bound ℓ
  refine ⟨CdΔ * CW * CB, NB, by positivity, hNB, fun τ z t hτ ht hz => ?_⟩
  have hsc : (0:ℝ) < scale τ := scale_pos τ
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have he : ‖Ept z‖ = Real.exp (-(Real.pi * t)) := norm_Ept_axis hz
  have hdb := hdΔ z hz1
  have hWb := hW z hz1
  have hBb := hB0b τ hτ
  have hkey : ‖Ept z‖ ^ 2 ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [he, show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, τ.im_pos]
  rw [show (fun τ z => Compact.Dev7 ℓ τ z) τ z = Compact.Dev7 ℓ τ z from rfl,
    show Compact.Dev7 ℓ τ z = -Compact.dDelta z * WFun z * Compact.B24 ℓ τ from rfl,
    norm_mul, norm_mul, norm_neg]
  calc ‖Compact.dDelta z‖ * ‖WFun z‖ * ‖Compact.B24 ℓ τ‖
      ≤ (CdΔ * ‖Ept z‖ ^ 2) * CW * (CB * (scale τ) ^ NB) := by
        gcongr
    _ = CdΔ * CW * CB * (scale τ) ^ NB * ‖Ept z‖ ^ 2 := by ring
    _ ≤ CdΔ * CW * CB * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ CdΔ * CW * CB * (scale τ) ^ NB := pos_f2 (by positivity)
        exact mul_le_mul_of_nonneg_left hkey h0
    _ ≤ CdΔ * CW * CB * (scale τ) ^ NB * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
        have h0 : (0:ℝ) ≤ CdΔ * CW * CB * (scale τ) ^ NB
            * Real.exp (-(Real.pi * (t - τ.im))) := pos_f3 (by positivity) (Real.exp_pos _).le
        have h1t : (1:ℝ) ≤ 1 + t := by linarith
        calc CdΔ * CW * CB * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im)))
            = CdΔ * CW * CB * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im))) * 1 := by ring
          _ ≤ CdΔ * CW * CB * (scale τ) ^ NB * Real.exp (-(Real.pi * (t - τ.im))) * (1 + t) :=
              mul_le_mul_of_nonneg_left h1t h0
          _ = CdΔ * CW * CB * (scale τ) ^ NB * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))) := by ring

/-! ## Assembly -/

/-- **Core decaying bound for the `d = 24` funnel tail.**

For `τ` in the funnel and `z = i t`, `t ≥ Im τ + 1`, the bracket
`brMinus 24 τ z + Sh τ z · br0 24 ℓ τ z` (equal to `-3456π·Sh·(K₋^{(24)} - 𝒢₋^{(24)})`) satisfies
`‖bracket‖ ≤ C (scale τ)^N (1+t)^M exp (-(π (t - Im τ)))`.  This is exactly the hypothesis of
`KMinus_funnel_tail_twentyfour_of_main`.

*Strategy.*  With `e = Ept z` (`‖e‖ = e^{-πt}`) replace the `z`-atoms by the polynomial references
`E₄(z) → 1 + 240e²`, `1/Δ(z) → e^{-2} + 24`, `E₁₄(z)/Δ(z) → (1-24e²)(e^{-2}+24)`,
`E₁₀(z)/Δ(z) → (1-264e²)(e^{-2}+24)`, `j(z) → (1+240e²)³(e^{-2}+24)`, `W(z) → Compact.Wref`,
`U²-V² → Compact.D2ref`, `𝓛 → Compact.Lref`, `Sh τ z → (1+240e²)³ - e² j(τ)`; all deviations are
`O(e²)` resp. `O(e³)` (`cusp_invDelta`, `cusp_W_second`, `cusp_D_second`, `cusp_L_second`,
`E4Fun_two_term`, `E6Fun_two_term`).  A `field_simp; ring` computation yields an exact identity
`refE = Σ_{k=1}^{8} c_k e^k` whose coefficients are polynomials in `P₂ = ψ₂(τ)E₁₀(τ)`,
`P₄ = ψ₄(τ)E₈(τ)`, `E₄(τ)³`, `Δ(τ)`, `j(τ)`, `Xc ℓ z`; note `c₁ = -29568P₄ + 15744P₂ + 27648E₄(τ)³
- 20570112Δ(τ) + 24j(τ)P₄ - 24j(τ)P₂` and the `j`-pairs cancel to `O((scale τ)^N)` by the
near-identity `Work.Asymptotics.psi4E8_sub_psi2E10_funnel` (`Funnel24Aux`), while
`e^{-kπt} e^{2π Im τ} ≤ e^{-π(t-Im τ)}` for `k ≥ 2`. -/
theorem KMinusFunnelMainBoundDecay2 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Asymptotics.Compact.brMinus ℓ 24 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) :=by
  have hTref : FunnelB (fun τ z => Compact.Tref24 ℓ τ z) := Tref24_bound ℓ
  have hD1 : FunnelB (fun τ z => Compact.Dev1 ℓ τ z) := Dev1_bound ℓ
  have hD2 : FunnelB (fun τ z => Compact.Dev2 ℓ τ z) := Dev2_bound ℓ
  have hD3 : FunnelB (fun τ z => Compact.Dev3 ℓ τ z) := Dev3_bound ℓ
  have hD4 : FunnelB (fun τ z => Compact.Dev4 ℓ τ z) := Dev4_bound ℓ
  have hD5 : FunnelB (fun τ z => Compact.Dev5 ℓ τ z) := Dev5_bound ℓ
  have hD6 : FunnelB (fun τ z => Compact.Dev6 ℓ τ z) := Dev6_bound ℓ
  have hD7 : FunnelB (fun τ z => Compact.Dev7 ℓ τ z) := Dev7_bound ℓ
  have hsum : FunnelB (fun τ z => ((((((Compact.Tref24 ℓ τ z + Compact.Dev1 ℓ τ z)
      + Compact.Dev2 ℓ τ z) + Compact.Dev3 ℓ τ z) + Compact.Dev4 ℓ τ z)
      + Compact.Dev5 ℓ τ z) + Compact.Dev6 ℓ τ z) + Compact.Dev7 ℓ τ z) :=
    FunnelB.add (FunnelB.add (FunnelB.add (FunnelB.add (FunnelB.add (FunnelB.add
      (FunnelB.add hTref hD1) hD2) hD3) hD4) hD5) hD6) hD7
  obtain ⟨CU, NU, hCU, hNU, hUb⟩ := hsum
  obtain ⟨CS, hCS, hSh⟩ := Sh_bound
  refine ⟨CS * CU, NU, 2, by positivity, hNU, by norm_num, fun τ z t hτ ht hz => ?_⟩
  have hShb := hSh τ z t hτ ht hz
  have hShge := funnel_Sh_ge τ z t hτ ht hz
  have hShne : Compact.Sh τ z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hShge
    norm_num at hShge
  have hdec := Compact.decomp24 ℓ τ z hShne
  have hUeq : (Compact.Sh τ z)⁻¹
        * (Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z)
      = ((((((Compact.Tref24 ℓ τ z + Compact.Dev1 ℓ τ z) + Compact.Dev2 ℓ τ z)
          + Compact.Dev3 ℓ τ z) + Compact.Dev4 ℓ τ z) + Compact.Dev5 ℓ τ z)
          + Compact.Dev6 ℓ τ z) + Compact.Dev7 ℓ τ z := by
    rw [hdec]; ring
  have hbr : Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z
      = Compact.Sh τ z * ((Compact.Sh τ z)⁻¹
          * (Compact.brMinus ℓ 24 τ z + Compact.Sh τ z * Compact.br0 24 ℓ τ z)) := by
    rw [← mul_assoc, mul_inv_cancel₀ hShne, one_mul]
  have hUbb := hUb τ z t hτ ht hz
  rw [hbr, hUeq]
  have hmain : ‖Compact.Sh τ z * (((((((Compact.Tref24 ℓ τ z + Compact.Dev1 ℓ τ z)
        + Compact.Dev2 ℓ τ z) + Compact.Dev3 ℓ τ z) + Compact.Dev4 ℓ τ z)
        + Compact.Dev5 ℓ τ z) + Compact.Dev6 ℓ τ z) + Compact.Dev7 ℓ τ z)‖
      ≤ ‖Compact.Sh τ z‖ * ‖(((((((Compact.Tref24 ℓ τ z + Compact.Dev1 ℓ τ z)
        + Compact.Dev2 ℓ τ z) + Compact.Dev3 ℓ τ z) + Compact.Dev4 ℓ τ z)
        + Compact.Dev5 ℓ τ z) + Compact.Dev6 ℓ τ z) + Compact.Dev7 ℓ τ z)‖ :=
    norm_mul_le _ _
  have hstep : ‖Compact.Sh τ z * (((((((Compact.Tref24 ℓ τ z + Compact.Dev1 ℓ τ z)
        + Compact.Dev2 ℓ τ z) + Compact.Dev3 ℓ τ z) + Compact.Dev4 ℓ τ z)
        + Compact.Dev5 ℓ τ z) + Compact.Dev6 ℓ τ z) + Compact.Dev7 ℓ τ z)‖
      ≤ CS * (CU * (scale τ) ^ NU * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))) :=
    le_trans hmain (mul_le_mul hShb hUbb (norm_nonneg _) hCS.le)
  refine le_trans hstep ?_
  have h1t : (1:ℝ) ≤ 1 + t := by nlinarith [τ.im_pos, hτ.2]
  have hsq : (1 + t) ≤ (1 + t) ^ (2:ℝ) := by
    rw [Real.rpow_two]; nlinarith [h1t]
  have h0 : (0:ℝ) ≤ CS * CU * (scale τ) ^ NU * Real.exp (-(Real.pi * (t - τ.im))) :=
    pos_f3 (by positivity) (Real.exp_pos _).le
  calc CS * (CU * (scale τ) ^ NU * (1 + t) * Real.exp (-(Real.pi * (t - τ.im))))
      = (CS * CU * (scale τ) ^ NU * Real.exp (-(Real.pi * (t - τ.im)))) * (1 + t) := by ring
    _ ≤ (CS * CU * (scale τ) ^ NU * Real.exp (-(Real.pi * (t - τ.im)))) * (1 + t) ^ (2:ℝ) :=
        mul_le_mul_of_nonneg_left hsq h0
    _ = CS * CU * (scale τ) ^ NU * (1 + t) ^ (2:ℝ)
          * Real.exp (-(Real.pi * (t - τ.im))) := by ring


end

end Work.Asymptotics
