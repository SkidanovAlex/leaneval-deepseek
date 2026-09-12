import Mathlib
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

/-! Lemma 3.4 of the paper (H-derivative lower bound):

For every real `x` there is `k ∈ {0,1,2,3}` with `|Re(H^(k)(x))| ≥ 1/4`.

PROOF (paper §3): suppose `|Re(H^(k)(x))| < 1/4` for all four `k`.  Set

    E_k := Re( i^k e^{ix} α(x) + (2i)^k e^{2ix} β(x) ).

From Lemma 3.6 (`Sec3H.H_iter_deriv_approx`) we have `|E_k| ≤ 1/8 + 1/4 = 3/8`.
Solving the real-linear system for the four quantities
`Re(e^{ix}α), Im(e^{ix}α), Re(e^{2ix}β), Im(e^{2ix}β)` in terms of `E_0..E_3`:

    Re(e^{ix}α)  = (4 E_0 + E_2)/3,   Im(e^{ix}α)  = -(4 E_1 + E_3)/3,
    Re(e^{2ix}β) = -(E_0 + E_2)/3,    Im(e^{2ix}β) = (E_1 + E_3)/6,

hence (with `|E_k| ≤ 3/8`):

    |Re(e^{ix}α)|, |Im(e^{ix}α)| ≤ 5/8,   |Re(e^{2ix}β)| ≤ 1/4,  |Im(e^{2ix}β)| ≤ 1/8

and so (squares) `|α|² + |β|² ≤ 25/64+25/64+1/16+1/64 = 55/64 < 1`,
contradicting `Sec3H.norm_sq_alpha_add_beta` (=1).  Note `|e^{ix}α| = |α|`
so `|α|² = Re² + Im²` of `e^{ix}α` (and similarly for `β`). -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3H

/-- `F_t(x) = e^{ix} α_t(x)`: first factor of `H`. -/
def Fterm (t : ℕ) (x : ℝ) : ℂ := Sec3.eθ x * alpha t x

/-- `G_t(x) = e^{2ix} β_t(x)`: second factor of `H`. -/
def Gterm (t : ℕ) (x : ℝ) : ℂ := Sec3.eθ (2 * x) * beta t x

/-- `i^k e^{ix} α(x) + (2i)^k e^{2ix} β(x)`: the main term of the derivative
approximation (target of `H_iter_deriv_approx`). -/
def ETerm (t : ℕ) (x : ℝ) (k : ℕ) : ℂ :=
  (Complex.I ^ k * Sec3.eθ x) * alpha t x + (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x)) * beta t x

/-- `‖w‖^2 = w.re^2 + w.im^2`. -/
lemma norm_sq_re_im (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq w]
  rw [Complex.normSq_apply]
  ring

/-- Associativity regrouping of `ETerm` against `Fterm`/`Gterm`. -/
lemma ETerm_eq_FG (t : ℕ) (x : ℝ) (k : ℕ) :
    ETerm t x k = Complex.I ^ k * Fterm t x + ((2 : ℂ) * Complex.I) ^ k * Gterm t x := by
  unfold ETerm Fterm Gterm
  rw [mul_assoc, mul_assoc]

/-- Real part of `F + G` (the `k = 0` combination). -/
lemma comb_re_0 (F G : ℂ) :
    (Complex.I ^ 0 * F + ((2 : ℂ) * Complex.I) ^ 0 * G).re = F.re + G.re := by
  norm_num

/-- Real part of `iF + 2iG` (the `k = 1` combination). -/
lemma comb_re_1 (F G : ℂ) :
    (Complex.I * F + ((2 : ℂ) * Complex.I) * G).re = -F.im - 2 * G.im := by
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re]
  norm_num
  ring

/-- Real part of `i²F + (2i)²G` (the `k = 2` combination). -/
lemma comb_re_2 (F G : ℂ) :
    (Complex.I ^ 2 * F + ((2 : ℂ) * Complex.I) ^ 2 * G).re = -F.re - 4 * G.re := by
  rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
  rw [show ((2 : ℂ) * Complex.I) ^ 2 = (-4 : ℂ) by rw [mul_pow]; norm_num]
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re]
  norm_num
  ring

/-- Real part of `i³F + (2i)³G` (the `k = 3` combination). -/
lemma comb_re_3 (F G : ℂ) :
    (Complex.I ^ 3 * F + ((2 : ℂ) * Complex.I) ^ 3 * G).re = F.im + 8 * G.im := by
  rw [show Complex.I ^ 3 = -Complex.I by norm_num]
  rw [show ((2 : ℂ) * Complex.I) ^ 3 = -8 * Complex.I by rw [mul_pow]; norm_num]
  rw [show -Complex.I * F = Complex.I * (-F) by ring]
  rw [show (-8 * Complex.I) * G = Complex.I * (-8 * G) by ring]
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re]
  norm_num

/-- Solving the real 4x4 system: if `e0 = a + c`, `e1 = -b - 2d`,
`e2 = -a - 4c`, `e3 = b + 8d` and all `|e_j| ≤ 3/8`, then
`a²+b²+c²+d² ≤ 55/64`. -/
lemma linear_bound (e0 e1 e2 e3 a b c d : ℝ)
    (h0 : |e0| ≤ 3 / 8) (h1 : |e1| ≤ 3 / 8) (h2 : |e2| ≤ 3 / 8) (h3 : |e3| ≤ 3 / 8)
    (hE0 : e0 = a + c) (hE1 : e1 = -b - 2 * d) (hE2 : e2 = -a - 4 * c) (hE3 : e3 = b + 8 * d) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 55 / 64 := by
  have h3a : |3 * a| ≤ 15 / 8 := by
    have hm : 4 * e0 + e2 = 3 * a := by linarith
    calc
      |3 * a| = |4 * e0 + e2| := by rw [← hm]
      _ ≤ |4 * e0| + |e2| := abs_add_le _ _
      _ = 4 * |e0| + |e2| := by rw [abs_mul]; norm_num
      _ ≤ 4 * (3 / 8) + 3 / 8 := by
          exact add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num)) h2
      _ = 15 / 8 := by norm_num
  have ha : |a| ≤ 5 / 8 := by
    have hm : |3 * a| = 3 * |a| := by rw [abs_mul]; norm_num
    nlinarith
  have h3b : |3 * b| ≤ 15 / 8 := by
    have hm : 3 * b = -(4 * e1 + e3) := by linarith
    calc
      |3 * b| = |-(4 * e1 + e3)| := by rw [hm]
      _ = |4 * e1 + e3| := abs_neg _
      _ ≤ |4 * e1| + |e3| := abs_add_le _ _
      _ = 4 * |e1| + |e3| := by rw [abs_mul]; norm_num
      _ ≤ 4 * (3 / 8) + 3 / 8 := by
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h3
      _ = 15 / 8 := by norm_num
  have hb : |b| ≤ 5 / 8 := by
    have hm : |3 * b| = 3 * |b| := by rw [abs_mul]; norm_num
    nlinarith
  have h3c : |3 * c| ≤ 3 / 4 := by
    have hm : 3 * c = -(e0 + e2) := by linarith
    calc
      |3 * c| = |-(e0 + e2)| := by rw [hm]
      _ = |e0 + e2| := abs_neg _
      _ ≤ |e0| + |e2| := abs_add_le _ _
      _ ≤ 3 / 8 + 3 / 8 := add_le_add h0 h2
      _ = 3 / 4 := by norm_num
  have hc : |c| ≤ 1 / 4 := by
    have hm : |3 * c| = 3 * |c| := by rw [abs_mul]; norm_num
    nlinarith
  have h6d : |6 * d| ≤ 3 / 4 := by
    have hm : e1 + e3 = 6 * d := by linarith
    calc
      |6 * d| = |e1 + e3| := by rw [← hm]
      _ ≤ |e1| + |e3| := abs_add_le _ _
      _ ≤ 3 / 8 + 3 / 8 := add_le_add h1 h3
      _ = 3 / 4 := by norm_num
  have hd : |d| ≤ 1 / 8 := by
    have hm : |6 * d| = 6 * |d| := by rw [abs_mul]; norm_num
    nlinarith
  have ha2 : a ^ 2 ≤ (5 / 8) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 8)] using ha)
  have hb2 : b ^ 2 ≤ (5 / 8) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 8)] using hb)
  have hc2 : c ^ 2 ≤ (1 / 4) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using hc)
  have hd2 : d ^ 2 ≤ (1 / 8) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] using hd)
  nlinarith

/-- Pure `norm_num` version of the arithmetic bound used in the derivative
approximation (mirrors `H_bound_aux` of `Sec3H_deriv` but without
`native_decide`, so no extra axioms). -/
lemma H_approx_bound_aux (k : ℕ) (hk : k ≤ 4) :
    (∑ i ∈ Finset.range k, ((Nat.choose k i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
      (∑ i ∈ Finset.range k, ((Nat.choose k i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) ≤ 1 / 8 := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Finset.sum_range_succ, Nat.choose]

/-- The H-derivative approximation bound of Lemma 3.6, restated with `ETerm`
and with a proof free of `native_decide` (so `#print axioms` stays clean). -/
lemma H_iter_deriv_approx_clean (t : ℕ) {k : ℕ} (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (H t) x - ETerm t x k‖ ≤ 1 / 8 := by
  by_cases hk0 : k = 0
  · subst k
    simp [H, ETerm]
  · have hk1 : 1 ≤ k := by omega
    have hFA : ContDiffAt ℝ k (FA t) x := by
      unfold FA
      exact ((contDiff_eθ (n := k)).contDiffAt.mul (contDiff_alpha (n := k) t).contDiffAt)
    have hFB : ContDiffAt ℝ k (FB t) x := by
      unfold FB
      exact ((contDiff_eθ_mul (n := k) 2).contDiffAt.mul (contDiff_beta (n := k) t).contDiffAt)
    rw [H_eq_FA_add_FB]
    have hadd := iteratedDeriv_add (n := k) (f := FA t) (g := FB t) hFA hFB
    rw [hadd]
    -- target split
    have htarget : (iteratedDeriv k (FA t) x + iteratedDeriv k (FB t) x) - ETerm t x k
        = (iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)) := by
      unfold ETerm
      ring
    rw [htarget]
    have h1 := norm_FA_sub_target_le t hk1 hk4 x
    have h2 := norm_FB_sub_target_le t hk1 hk4 x
    calc
      ‖(iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x))‖
          ≤ ‖iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)‖ +
              ‖iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖ := norm_add_le _ _
      _ ≤ (∑ i ∈ Finset.range k, ((Nat.choose k i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
            (∑ i ∈ Finset.range k, ((Nat.choose k i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) := by
            exact add_le_add h1 h2
      _ ≤ 1 / 8 := H_approx_bound_aux k hk4

/-- Auxiliary: the quantities E_k of the proof are bounded by `3/8` under the
contradiction hypothesis.  (May be used internally; statement is optional.) -/
lemma E_k_bound (t : ℕ) (x : ℝ) (hk : ∀ k ≤ 3, |(iteratedDeriv k (H t) x).re| < 1 / 4)
    (k : ℕ) (hk4 : k ≤ 3) :
    |(Complex.I ^ k * Sec3.eθ x * alpha t x + ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x).re|
      ≤ 3 / 8 := by
  change |(ETerm t x k).re| ≤ 3 / 8
  let z : ℂ := iteratedDeriv k (H t) x
  let T : ℂ := ETerm t x k
  have hdiff : ‖z - T‖ ≤ 1 / 8 := by
    have h4 : k ≤ 4 := le_trans hk4 (by norm_num)
    have hmain := H_iter_deriv_approx_clean t h4 x
    simpa [z, T] using hmain
  let p : ℝ := z.re
  let q : ℝ := T.re
  have hpq : |p - q| ≤ 1 / 8 := by
    have h1 := Complex.abs_re_le_norm (z - T)
    exact le_trans (by simpa [p, q] using h1) hdiff
  have htri : |q| ≤ |p - q| + |p| := by
    calc
      |q| = |(q - p) + p| := by congr 1; ring
      _ ≤ |q - p| + |p| := abs_add_le (q - p) p
      _ = |p - q| + |p| := by rw [abs_sub_comm]
  have hp : |p| < 1 / 4 := hk k hk4
  calc
    |q| ≤ |p - q| + |p| := htri
    _ ≤ 1 / 8 + 1 / 4 := by linarith
    _ = 3 / 8 := by norm_num

/-- Lower bound on one of the first three derivatives (or the value) of `Re H`. -/
lemma H_deriv_lbound (t : ℕ) (x : ℝ) :
    ∃ k : ℕ, k ≤ 3 ∧ (1 / 4 : ℝ) ≤ |(iteratedDeriv k (H t) x).re| := by
  by_contra hnot
  have hk : ∀ k : ℕ, k ≤ 3 → |(iteratedDeriv k (H t) x).re| < 1 / 4 := by
    intro k hk4
    exact lt_of_not_ge (fun hle => hnot ⟨k, hk4, hle⟩)
  -- The four real linear combinations E_0..E_3
  let e0 : ℝ := (ETerm t x 0).re
  let e1 : ℝ := (ETerm t x 1).re
  let e2 : ℝ := (ETerm t x 2).re
  let e3 : ℝ := (ETerm t x 3).re
  -- components a = Re(e^{ix}α), b = Im(e^{ix}α), c = Re(e^{2ix}β), d = Im(e^{2ix}β)
  let a : ℝ := (Fterm t x).re
  let b : ℝ := (Fterm t x).im
  let c : ℝ := (Gterm t x).re
  let d : ℝ := (Gterm t x).im
  have h0b : |e0| ≤ 3 / 8 := by
    dsimp [e0]
    exact E_k_bound t x hk 0 (by norm_num)
  have h1b : |e1| ≤ 3 / 8 := by
    dsimp [e1]
    exact E_k_bound t x hk 1 (by norm_num)
  have h2b : |e2| ≤ 3 / 8 := by
    dsimp [e2]
    exact E_k_bound t x hk 2 (by norm_num)
  have h3b : |e3| ≤ 3 / 8 := by
    dsimp [e3]
    exact E_k_bound t x hk 3 (by norm_num)
  have hE0 : e0 = a + c := by
    dsimp [e0, a, c]
    rw [ETerm_eq_FG]
    exact comb_re_0 (Fterm t x) (Gterm t x)
  have hE1 : e1 = -b - 2 * d := by
    dsimp [e1, b, d]
    rw [ETerm_eq_FG]
    simp only [pow_one]
    exact comb_re_1 (Fterm t x) (Gterm t x)
  have hE2 : e2 = -a - 4 * c := by
    dsimp [e2, a, c]
    rw [ETerm_eq_FG]
    exact comb_re_2 (Fterm t x) (Gterm t x)
  have hE3 : e3 = b + 8 * d := by
    dsimp [e3, b, d]
    rw [ETerm_eq_FG]
    exact comb_re_3 (Fterm t x) (Gterm t x)
  have hbnd := linear_bound e0 e1 e2 e3 a b c d h0b h1b h2b h3b hE0 hE1 hE2 hE3
  -- Norm side: |F|² + |G|² = |α|² + |β|² = 1, and equals a²+b²+c²+d².
  have hF : ‖Fterm t x‖ = ‖alpha t x‖ := by
    unfold Fterm
    rw [norm_mul, Sec3.norm_eθ]
    simp
  have hG : ‖Gterm t x‖ = ‖beta t x‖ := by
    unfold Gterm
    rw [norm_mul, Sec3.norm_eθ]
    simp
  have hsqF : ‖Fterm t x‖ ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [a, b]
    exact norm_sq_re_im (Fterm t x)
  have hsqG : ‖Gterm t x‖ ^ 2 = c ^ 2 + d ^ 2 := by
    dsimp [c, d]
    exact norm_sq_re_im (Gterm t x)
  have hsum1 : ‖Fterm t x‖ ^ 2 + ‖Gterm t x‖ ^ 2 = 1 := by
    calc
      ‖Fterm t x‖ ^ 2 + ‖Gterm t x‖ ^ 2 = ‖alpha t x‖ ^ 2 + ‖beta t x‖ ^ 2 := by rw [hF, hG]
      _ = 1 := norm_sq_alpha_add_beta t x
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
    calc
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) := by ring
      _ = ‖Fterm t x‖ ^ 2 + ‖Gterm t x‖ ^ 2 := by rw [← hsqF, ← hsqG]
      _ = 1 := hsum1
  nlinarith

end Sec3H
end Submission
