import Mathlib
import Submission.S5si_facts
import Submission.S5sinc_num

/-! Lemma "si" (paper Lemma 5.8): bounds for a grid interval of length ≤ 6π/n.

For an interval `I = [pπ/n, qπ/n]` with integers `p < q`, `q-p ≤ 6`, define

    M(θ0) := ∫_{pπ/n}^{qπ/n} sin(2n(x-θ0)) / (x-θ0) dx

(integrand extended by its continuous value `2n` at `x = θ0`).  Then

    θ0 ∈ I   ⇒   4/3 ≤ M(θ0) ≤ 4
    θ0 ∉ I   ⇒   -1  ≤ M(θ0) ≤ 2 .

Suggested route: (1) change variables `u = 2n(x-θ0)` to get
`M(θ0) = ∫_{2n(pπ/n-θ0)}^{2n(qπ/n-θ0)} sinc u du`; (2) for `θ0 ∈ I` set
`m := q-p`, `F(u) := ∫_u^{u+2mπ} sinc` for `u ∈ [-2mπ, 0]` and show `F` is
monotone between consecutive multiples of π (derivative
`F'(u) = sin u · (1/(u+2mπ) − 1/u)`), so extrema occur at `u = -kπ`;
evaluate there (split into a nonneg-index part `S(A)`, and via evenness of
sinc a negative-index part that is `S(A')` as well, see `u_neg_eq`) and
combine `S_bounds`; (3) for `θ0` outside the interval use the same monotone
argument on `u ≥ 0` together with `block_even_bounds`/`block_odd_bounds` and
`u1_lower`; single-point issues at `x = θ0`/`u = 0` are measure-zero
(use `integral_congr_ae` or the case-split extension). -/

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral

set_option autoImplicit false

namespace Submission
namespace SiBounds

/-- The linearised kernel integral (integrand extended by `2n` at `x = θ0`,
so that it is continuous everywhere). -/
def LinInt (n : ℕ) (a b θ0 : ℝ) : ℝ :=
  ∫ x in a..b,
    (if x - θ0 = 0 then (2 * (n : ℝ))
     else Real.sin (2 * (n : ℝ) * (x - θ0)) / (x - θ0))

open SiFacts SincNum

/-- `LinInt` integrand is `2n * sinc(2n(x-θ0))` -/
lemma linint_integrand_eq (n : ℕ) (hn : 1 ≤ n) (θ0 x : ℝ) :
    (if x - θ0 = 0 then (2 * (n : ℝ)) else Real.sin (2 * (n : ℝ) * (x - θ0)) / (x - θ0))
      = 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - θ0)) := by
  by_cases h : x - θ0 = 0
  · rw [if_pos h]
    have : 2 * (n : ℝ) * (x - θ0) = 0 := by rw [h]; ring
    rw [this, Real.sinc_zero]
    ring
  · rw [if_neg h]
    have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
    have harg : 2 * (n : ℝ) * (x - θ0) ≠ 0 := mul_ne_zero hn0 h
    rw [Real.sinc_of_ne_zero harg]
    field_simp [h, harg]

/-- `LinInt` equals a plain integral of the continuous kernel -/
lemma linint_eq_kernel (n : ℕ) (hn : 1 ≤ n) (a b θ0 : ℝ) :
    LinInt n a b θ0 =
      ∫ x in a..b, (2 * (n : ℝ)) * Real.sinc (2 * (n : ℝ) * (x - θ0)) := by
  unfold LinInt
  apply intervalIntegral.integral_congr
  intro x hx
  exact linint_integrand_eq n hn θ0 x

/-- change of variables `u = 2n(x-θ0)` -/
lemma linint_eq_sinc (n : ℕ) (hn : 1 ≤ n) (a b θ0 : ℝ) :
    LinInt n a b θ0 =
      ∫ u in (2 * (n : ℝ) * (a - θ0))..(2 * (n : ℝ) * (b - θ0)), Real.sinc u := by
  rw [linint_eq_kernel n hn]
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  have h1 : (∫ x in a..b, Real.sinc ((2 * (n : ℝ)) * (x - θ0)))
      = ∫ y in (a - θ0)..(b - θ0), Real.sinc ((2 * (n : ℝ)) * y) := by
    simpa using (intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => Real.sinc ((2 * (n : ℝ)) * y)) (d := θ0))
  have h2 : (∫ y in (a - θ0)..(b - θ0), Real.sinc ((2 * (n : ℝ)) * y))
      = (2 * (n : ℝ))⁻¹ * ∫ u in ((2 * (n : ℝ)) * (a - θ0))..((2 * (n : ℝ)) * (b - θ0)), Real.sinc u := by
    have hh := intervalIntegral.integral_comp_mul_left (f := Real.sinc) (c := (2 * (n : ℝ))) (hc := hn0)
        (a := a - θ0) (b := b - θ0)
    simpa using hh
  calc
    (∫ x in a..b, (2 * (n : ℝ)) * Real.sinc ((2 * (n : ℝ)) * (x - θ0)))
        = (2 * (n : ℝ)) * ∫ x in a..b, Real.sinc ((2 * (n : ℝ)) * (x - θ0)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (2 * (n : ℝ)) * ∫ y in (a - θ0)..(b - θ0), Real.sinc ((2 * (n : ℝ)) * y) := by rw [h1]
    _ = (2 * (n : ℝ)) * ((2 * (n : ℝ))⁻¹ * ∫ u in ((2 * (n : ℝ)) * (a - θ0))..((2 * (n : ℝ)) * (b - θ0)), Real.sinc u) := by rw [h2]
    _ = ∫ u in ((2 * (n : ℝ)) * (a - θ0))..((2 * (n : ℝ)) * (b - θ0)), Real.sinc u := by
            field_simp [hn0]

/-- interval integral of sinc -/
def sincInt (a b : ℝ) : ℝ := ∫ x in a..b, Real.sinc x

/-- window length `2mπ` -/
def winLen (m : ℕ) : ℝ := 2 * (m : ℝ) * Real.pi

/-- window integral `∫_u^{u+2mπ} sinc` -/
def W (m : ℕ) (u : ℝ) : ℝ := sincInt u (u + winLen m)

/-- delta integrand -/
def D (m : ℕ) (x : ℝ) : ℝ := Real.sinc (x + winLen m) - Real.sinc x

-- partial sums and their integral values -------------------------------------

/-- `pref k = u 0 + ... + u (k-1)` -/
def pref (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, SiFacts.u j

lemma pref_succ (k : ℕ) : pref (k + 1) = pref k + SiFacts.u k := by
  unfold pref
  rw [Finset.sum_range_succ]

lemma S_eq_pref (k : ℕ) : SiFacts.S k = pref (k + 1) := by
  unfold SiFacts.S pref
  rfl

lemma u0_eq_sincInt : SiFacts.u 0 = sincInt 0 Real.pi := by
  unfold SiFacts.u sincInt
  norm_num

lemma u1_eq_sincInt : SiFacts.u 1 = sincInt Real.pi (2 * Real.pi) := by
  unfold SiFacts.u sincInt
  norm_num

lemma sincInt_add_adjacent (a b c : ℝ) :
    sincInt a b + sincInt b c = sincInt a c := by
  unfold sincInt
  have h1 : IntervalIntegrable (fun x : ℝ => Real.sinc x) volume a b :=
    (Real.continuous_sinc).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => Real.sinc x) volume b c :=
    (Real.continuous_sinc).intervalIntegrable _ _
  exact intervalIntegral.integral_add_adjacent_intervals (μ := volume) h1 h2

/-- `∫_0^{kπ} sinc = u0+...+u(k-1)` -/
lemma sincInt_zero_mul_pi (k : ℕ) : sincInt 0 ((k : ℝ) * Real.pi) = pref k := by
  induction k with
  | zero =>
      unfold pref sincInt
      simp
  | succ k ih =>
      have hrec : sincInt 0 (((k + 1 : ℕ) : ℝ) * Real.pi) =
          sincInt 0 ((k : ℝ) * Real.pi) + sincInt ((k : ℝ) * Real.pi) (((k + 1 : ℕ) : ℝ) * Real.pi) := by
        exact (sincInt_add_adjacent 0 ((k : ℝ) * Real.pi) (((k + 1 : ℕ) : ℝ) * Real.pi)).symm
      rw [hrec, ih]
      have hlast : sincInt ((k : ℝ) * Real.pi) (((k + 1 : ℕ) : ℝ) * Real.pi) = SiFacts.u k := rfl
      rw [hlast]
      rw [pref_succ]

/-- `∫_{-kπ}^0 sinc = u0+...+u(k-1)` -/
lemma sincInt_neg_mul_pi_zero (k : ℕ) : sincInt (-((k : ℝ) * Real.pi)) 0 = pref k := by
  induction k with
  | zero =>
      unfold pref sincInt
      simp
  | succ k ih =>
      have hrec : sincInt (-(((k + 1 : ℕ) : ℝ) * Real.pi)) 0 =
          sincInt (-(((k + 1 : ℕ) : ℝ) * Real.pi)) (-((k : ℝ) * Real.pi))
            + sincInt (-((k : ℝ) * Real.pi)) 0 := by
        exact (sincInt_add_adjacent (-(((k + 1 : ℕ) : ℝ) * Real.pi)) (-((k : ℝ) * Real.pi)) 0).symm
      rw [hrec, ih]
      have hlast : sincInt (-(((k + 1 : ℕ) : ℝ) * Real.pi)) (-((k : ℝ) * Real.pi)) = SiFacts.u k := by
        have hu := SiFacts.u_neg_eq (k + 1) (by omega)
        unfold sincInt SiFacts.u at hu ⊢
        simpa [show (k + 1 - 1 : ℕ) = k by omega] using hu
      rw [hlast]
      rw [pref_succ]
      rw [add_comm]

-- numeric bridges ------------------------------------------------------------

lemma S1_eq_u0_add_u1 : SiFacts.S 1 = SiFacts.u 0 + SiFacts.u 1 := by
  unfold SiFacts.S
  norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp

lemma S0_eq_u0 : SiFacts.S 0 = SiFacts.u 0 := by
  unfold SiFacts.S
  norm_num

lemma S1_eq_sincInt : SiFacts.S 1 = sincInt 0 (2 * Real.pi) := by
  rw [S1_eq_u0_add_u1, u0_eq_sincInt, u1_eq_sincInt]
  have h : sincInt 0 Real.pi + sincInt Real.pi (2 * Real.pi) = sincInt 0 (2 * Real.pi) :=
    sincInt_add_adjacent 0 Real.pi (2 * Real.pi)
  linarith

lemma S0_eq_sincInt : SiFacts.S 0 = sincInt 0 Real.pi := by
  rw [S0_eq_u0, u0_eq_sincInt]

lemma S1_ge_four_thirds : (4 / 3 : ℝ) ≤ SiFacts.S 1 := by
  rw [S1_eq_sincInt]
  exact SincNum.int_0_2pi_ge

lemma S0_le_two : SiFacts.S 0 ≤ 2 := by
  rw [S0_eq_sincInt]
  exact SincNum.int_0_pi_le

lemma u1_ge_neg_one : -1 ≤ SiFacts.u 1 := by
  rw [u1_eq_sincInt]
  exact SincNum.int_pi_2pi_ge

lemma S0_pos : 0 < SiFacts.S 0 := by
  rw [S0_eq_u0]
  exact SiFacts.u0_pos

lemma S1_pos : 0 < SiFacts.S 1 := by
  rw [S1_eq_u0_add_u1]
  have hp := SiFacts.u_pair_pos 0
  norm_num at hp
  linarith


-- trig sign helpers ----------------------------------------------------------

/-- `((2t+1)π) = (2t)π + π` -/
lemma two_mul_add_one_pi (t : ℕ) :
    (((2 * t + 1 : ℕ) : ℝ) * Real.pi) = ((2 * t : ℕ) : ℝ) * Real.pi + Real.pi := by
  have hc : ((2 * t + 1 : ℕ) : ℝ) = ((2 * t : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hc]
  ring

/-- `((2t+2)π) = (2t+1)π + π` -/
lemma two_mul_add_two_pi (t : ℕ) :
    (((2 * t + 2 : ℕ) : ℝ) * Real.pi) = ((2 * t + 1 : ℕ) : ℝ) * Real.pi + Real.pi := by
  have hc : ((2 * t + 2 : ℕ) : ℝ) = ((2 * t + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hc]
  ring

/-- on `(2tπ,(2t+1)π)`, sin is nonnegative -/
lemma sin_nonneg_of_even_piece (t : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (((2 * t : ℕ) : ℝ) * Real.pi) (((2 * t + 1 : ℕ) : ℝ) * Real.pi)) :
    0 ≤ Real.sin x := by
  have hx2 : x < ((2 * t : ℕ) : ℝ) * Real.pi + Real.pi := by
    rw [two_mul_add_one_pi] at hx
    exact hx.2
  have hsub1 : 0 < x - ((2 * t : ℕ) : ℝ) * Real.pi := by linarith [hx.1]
  have hsub2 : x - ((2 * t : ℕ) : ℝ) * Real.pi < Real.pi := by linarith
  have hsin : Real.sin x = Real.sin (x - ((2 * t : ℕ) : ℝ) * Real.pi) := by
    have hs := Real.sin_sub_nat_mul_pi x (2 * t)
    rw [hs]
    have hpow : (-1 : ℝ) ^ (2 * t) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpow, one_mul]
  rw [hsin]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hsub1) (le_of_lt hsub2)

/-- on `((2t+1)π,(2t+2)π)`, sin is nonpositive -/
lemma sin_nonpos_of_odd_piece (t : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (((2 * t + 1 : ℕ) : ℝ) * Real.pi) (((2 * t + 2 : ℕ) : ℝ) * Real.pi)) :
    Real.sin x ≤ 0 := by
  have hx2 : x < ((2 * t + 1 : ℕ) : ℝ) * Real.pi + Real.pi := by
    rw [two_mul_add_two_pi] at hx
    exact hx.2
  have hsub1 : 0 < x - ((2 * t + 1 : ℕ) : ℝ) * Real.pi := by linarith [hx.1]
  have hsub2 : x - ((2 * t + 1 : ℕ) : ℝ) * Real.pi < Real.pi := by linarith
  have hsin : Real.sin x = - Real.sin (x - ((2 * t + 1 : ℕ) : ℝ) * Real.pi) := by
    have hs := Real.sin_sub_nat_mul_pi x (2 * t + 1)
    -- sin (x - nπ) = (-1)^n sin x  with n odd
    have hpow : (-1 : ℝ) ^ (2 * t + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    -- from hs: sin(x−nπ) = − sin x ⟹ sin x = − sin(x−nπ)
    calc
      Real.sin x = -((-1 : ℝ) ^ (2 * t + 1) * Real.sin x) := by rw [hpow]; ring
      _ = -Real.sin (x - ((2 * t + 1 : ℕ) : ℝ) * Real.pi) := by rw [← hs]
  rw [hsin]
  have hsinr : 0 ≤ Real.sin (x - ((2 * t + 1 : ℕ) : ℝ) * Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hsub1) (le_of_lt hsub2)
  linarith

/-- on `(-(2t+1)π,-2tπ)` sin is nonpositive -/
lemma sin_nonpos_of_neg_even_piece (t : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(((2 * t + 1 : ℕ) : ℝ) * Real.pi)) (-(((2 * t : ℕ) : ℝ) * Real.pi))) :
    Real.sin x ≤ 0 := by
  have hy : -x ∈ Set.Ioo (((2 * t : ℕ) : ℝ) * Real.pi) (((2 * t + 1 : ℕ) : ℝ) * Real.pi) := by
    constructor <;> linarith [hx.1, hx.2]
  have hneg : Real.sin x = -Real.sin (-x) := by
    rw [Real.sin_neg]
    ring
  rw [hneg]
  have hs := sin_nonneg_of_even_piece t hy
  linarith

/-- on `(-(2t+2)π,-(2t+1)π)` sin is nonnegative -/
lemma sin_nonneg_of_neg_odd_piece (t : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(((2 * t + 2 : ℕ) : ℝ) * Real.pi)) (-(((2 * t + 1 : ℕ) : ℝ) * Real.pi))) :
    0 ≤ Real.sin x := by
  have hy : -x ∈ Set.Ioo (((2 * t + 1 : ℕ) : ℝ) * Real.pi) (((2 * t + 2 : ℕ) : ℝ) * Real.pi) := by
    constructor <;> linarith [hx.1, hx.2]
  have hneg : Real.sin x = -Real.sin (-x) := by
    rw [Real.sin_neg]
    ring
  rw [hneg]
  have hs := sin_nonpos_of_odd_piece t hy
  linarith

-- delta sign machinery -------------------------------------------------------

lemma winLen_nonneg (m : ℕ) : 0 ≤ winLen m := by
  unfold winLen
  positivity

lemma winLen_pos (m : ℕ) (hm : 1 ≤ m) : 0 < winLen m := by
  unfold winLen
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  positivity

lemma sin_add_winLen (m : ℕ) (x : ℝ) : Real.sin (x + winLen m) = Real.sin x := by
  unfold winLen
  have hw : 2 * (m : ℝ) * Real.pi = ((2 * m : ℕ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hw]
  have hs := Real.sin_add_nat_mul_pi x (2 * m)
  rw [hs]
  have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul]
    norm_num
  rw [hpow, one_mul]

/-- D on the region `x < 0 < x + L` (inside pieces) -/
lemma D_eq_sin_mul_neg (m : ℕ) (x : ℝ) (hx0 : x < 0) (hxL : 0 < x + winLen m) :
    D m x = Real.sin x * (1 / (x + winLen m) - 1 / x) := by
  unfold D
  rw [Real.sinc_of_ne_zero (ne_of_lt hx0)]
  rw [Real.sinc_of_ne_zero (ne_of_gt hxL)]
  rw [sin_add_winLen]
  ring

/-- D on the region `x > 0` (outside pieces) -/
lemma D_eq_sin_mul_pos (m : ℕ) (x : ℝ) (hx0 : 0 < x) :
    D m x = Real.sin x * (1 / (x + winLen m) - 1 / x) := by
  unfold D
  rw [Real.sinc_of_ne_zero (ne_of_gt hx0)]
  have hxL : x + winLen m ≠ 0 := by
    have : 0 < x + winLen m := by linarith [winLen_nonneg m]
    exact ne_of_gt this
  rw [Real.sinc_of_ne_zero hxL]
  rw [sin_add_winLen]
  ring

/-- factor is positive when `x < 0 < x+L` -/
lemma D_factor_pos (m : ℕ) {x : ℝ} (hx0 : x < 0) (hxL : 0 < x + winLen m) :
    0 < 1 / (x + winLen m) - 1 / x := by
  have h1 : 0 < 1 / (x + winLen m) := div_pos zero_lt_one hxL
  have hxinv : 1 / x < 0 := one_div_neg.mpr hx0
  linarith

/-- factor is negative when `x > 0` (and m ≥ 1) -/
lemma D_factor_neg (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx0 : 0 < x) :
    1 / (x + winLen m) - 1 / x < 0 := by
  have hxL : x < x + winLen m := by
    have : 0 < winLen m := winLen_pos m hm
    linarith
  have hlt : 1 / (x + winLen m) < 1 / x := div_lt_div_of_pos_left zero_lt_one hx0 hxL
  linarith

/-- D at a multiple of π away from 0 and -L -/
lemma D_eq_zero_of_sin_zero (m : ℕ) (y : ℝ) (hy : Real.sin y = 0) (hy0 : y ≠ 0)
    (hyL : y + winLen m ≠ 0) : D m y = 0 := by
  unfold D
  rw [Real.sinc_of_ne_zero hy0]
  rw [Real.sinc_of_ne_zero hyL]
  rw [sin_add_winLen]
  rw [hy]
  ring

/-- `D(0) = -1` -/
lemma D_zero_val (m : ℕ) (hm : 1 ≤ m) : D m 0 = -1 := by
  unfold D
  rw [show (0 + winLen m) = winLen m by ring]
  rw [Real.sinc_zero]
  have hL : winLen m ≠ 0 := ne_of_gt (winLen_pos m hm)
  rw [Real.sinc_of_ne_zero hL]
  have hs := sin_add_winLen m (0 : ℝ)
  have hsin : Real.sin (winLen m) = 0 := by simpa using hs
  rw [hsin]
  ring

/-- `D(-L) = 1` -/
lemma D_neg_winLen_val (m : ℕ) (hm : 1 ≤ m) : D m (-winLen m) = 1 := by
  unfold D
  have hneg : -winLen m ≠ 0 := by linarith [winLen_pos m hm]
  have h0 : -winLen m + winLen m = 0 := by ring
  rw [h0, Real.sinc_zero]
  rw [Real.sinc_of_ne_zero hneg]
  have hs := sin_add_winLen m (0 : ℝ)
  have hL0 : Real.sin (winLen m) = 0 := by simpa using hs
  have hsin : Real.sin (-winLen m) = 0 := by
    rw [Real.sin_neg, hL0]
    ring
  rw [hsin]
  ring



/-- sinc at nonzero natural multiple of π is 0 -/
lemma sinc_nat_mul_pi_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (((k : ℕ) : ℝ) * Real.pi) = 0 := by
  rw [Real.sinc_of_ne_zero]
  · rw [Real.sin_nat_mul_pi]
    simp
  · apply mul_ne_zero
    · exact_mod_cast hk
    · exact ne_of_gt Real.pi_pos

/-- sinc at a natural multiple of π -/
lemma sinc_nat_mul_pi_val (k : ℕ) :
    Real.sinc (((k : ℕ) : ℝ) * Real.pi) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa using (Real.sinc_zero : Real.sinc 0 = 1)
  · have h := sinc_nat_mul_pi_ne_zero k hk
    rw [h]
    simp [hk]

/-- sinc at nonzero negative natural multiple of π is 0 -/
lemma sinc_neg_nat_mul_pi_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (-(((k : ℕ) : ℝ) * Real.pi)) = 0 := by
  rw [Real.sinc_neg]
  exact sinc_nat_mul_pi_ne_zero k hk

/-- `D(kπ) = 0` for k ≥ 1 -/
lemma D_nat_pi_eq_zero (m k : ℕ) (hk : 1 ≤ k) : D m (((k : ℕ) : ℝ) * Real.pi) = 0 := by
  unfold D
  have hsum : ((k : ℕ) : ℝ) * Real.pi + winLen m = (((k + 2 * m : ℕ) : ℝ) * Real.pi) := by
    unfold winLen
    push_cast
    ring
  rw [hsum]
  have hk0 : k + 2 * m ≠ 0 := by omega
  rw [sinc_nat_mul_pi_ne_zero (k + 2 * m) hk0, sinc_nat_mul_pi_ne_zero k (by omega)]
  ring

/-- `D(kπ) ≤ 0` for all k -/
lemma D_le_zero_at_nat_pi (m k : ℕ) (hm : 1 ≤ m) :
    D m (((k : ℕ) : ℝ) * Real.pi) ≤ 0 := by
  by_cases hk : k = 0
  · subst k
    have hD : D m (((0 : ℕ) : ℝ) * Real.pi) = -1 := by
      rw [show (((0 : ℕ) : ℝ) * Real.pi) = 0 by simp]
      exact D_zero_val m hm
    rw [hD]
    norm_num
  · rw [D_nat_pi_eq_zero m k (by omega)]

/-- `D(kπ) ≥ 0` for k ≥ 1 -/
lemma D_ge_zero_at_nat_pi (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    0 ≤ D m (((k : ℕ) : ℝ) * Real.pi) := by
  rw [D_nat_pi_eq_zero m k hk]

/-- `D(-kπ) = 0` for `1 ≤ k < 2m` -/
lemma D_neg_pi_eq_zero (m k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * m) :
    D m (-(((k : ℕ) : ℝ) * Real.pi)) = 0 := by
  unfold D
  have hk2' : k ≤ 2 * m := by omega
  have hsum : -(((k : ℕ) : ℝ) * Real.pi) + winLen m = (((2 * m - k : ℕ) : ℝ) * Real.pi) := by
    unfold winLen
    rw [Nat.cast_sub hk2']
    push_cast
    ring
  rw [hsum]
  have hdiff : 2 * m - k ≠ 0 := by omega
  rw [sinc_nat_mul_pi_ne_zero (2 * m - k) hdiff, sinc_neg_nat_mul_pi_ne_zero k (by omega)]
  ring

/-- `D(-kπ) ≤ 0` for `k < 2m` -/
lemma D_le_zero_at_neg_pi (m k : ℕ) (hm : 1 ≤ m) (hk : k < 2 * m) :
    D m (-(((k : ℕ) : ℝ) * Real.pi)) ≤ 0 := by
  by_cases hk0 : k = 0
  · subst k
    have hD : D m (-(((0 : ℕ) : ℝ) * Real.pi)) = -1 := by
      rw [show (-(((0 : ℕ) : ℝ) * Real.pi)) = 0 by simp]
      exact D_zero_val m hm
    rw [hD]
    norm_num
  · rw [D_neg_pi_eq_zero m k (by omega) hk]

/-- `D(-kπ) ≥ 0` for `1 ≤ k ≤ 2m` -/
lemma D_ge_zero_at_neg_pi (m k : ℕ) (hm : 1 ≤ m) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * m) :
    0 ≤ D m (-(((k : ℕ) : ℝ) * Real.pi)) := by
  by_cases hk2m : k = 2 * m
  · have hD : D m (-(((k : ℕ) : ℝ) * Real.pi)) = 1 := by
      rw [hk2m]
      have hw : winLen m = ((2 * m : ℕ) : ℝ) * Real.pi := by
        unfold winLen
        push_cast
        ring
      rw [← hw]
      unfold D
      have hneg : -winLen m ≠ 0 := by linarith [winLen_pos m hm]
      rw [Real.sinc_of_ne_zero hneg]
      have hz : -winLen m + winLen m = 0 := by ring
      rw [hz, Real.sinc_zero]
      have hs := sin_add_winLen m (0 : ℝ)
      have hL0 : Real.sin (winLen m) = 0 := by simpa using hs
      have hsin : Real.sin (-winLen m) = 0 := by
        rw [Real.sin_neg, hL0]
        ring
      rw [hsin]
      ring
    rw [hD]
    norm_num
  · rw [D_neg_pi_eq_zero m k hk1 (by omega)]

/-- outside even piece `[2tπ,(2t+1)π]`: D ≤ 0 -/
lemma D_nonpos_on_even_out_piece (m t : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ Set.Icc (((2 * t : ℕ) : ℝ) * Real.pi) (((2 * t + 1 : ℕ) : ℝ) * Real.pi), D m x ≤ 0 := by
  intro x hx
  by_cases hxA : x = ((2 * t : ℕ) : ℝ) * Real.pi
  · rw [hxA]
    exact D_le_zero_at_nat_pi m (2 * t) hm
  · by_cases hxB : x = ((2 * t + 1 : ℕ) : ℝ) * Real.pi
    · rw [hxB]
      exact D_le_zero_at_nat_pi m (2 * t + 1) hm
    · have hlt1 : ((2 * t : ℕ) : ℝ) * Real.pi < x := lt_of_le_of_ne hx.1 (by
        intro hEq
        exact hxA hEq.symm)
      have hlt2 : x < ((2 * t + 1 : ℕ) : ℝ) * Real.pi := lt_of_le_of_ne hx.2 (by
        intro hEq
        exact hxB hEq)
      have hx0 : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ ((2 * t : ℕ) : ℝ) * Real.pi) hlt1
      rw [D_eq_sin_mul_pos m x hx0]
      have hfac : 1 / (x + winLen m) - 1 / x ≤ 0 := le_of_lt (D_factor_neg m hm hx0)
      have hsin : 0 ≤ Real.sin x := sin_nonneg_of_even_piece t ⟨hlt1, hlt2⟩
      exact mul_nonpos_of_nonneg_of_nonpos hsin hfac

/-- outside odd piece `[(2t+1)π,(2t+2)π]`: D ≥ 0 -/
lemma D_nonneg_on_odd_out_piece (m t : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ Set.Icc (((2 * t + 1 : ℕ) : ℝ) * Real.pi) (((2 * t + 2 : ℕ) : ℝ) * Real.pi), 0 ≤ D m x := by
  intro x hx
  by_cases hxA : x = ((2 * t + 1 : ℕ) : ℝ) * Real.pi
  · rw [hxA]
    exact D_ge_zero_at_nat_pi m (2 * t + 1) hm (by omega)
  · by_cases hxB : x = ((2 * t + 2 : ℕ) : ℝ) * Real.pi
    · rw [hxB]
      exact D_ge_zero_at_nat_pi m (2 * t + 2) hm (by omega)
    · have hlt1 : ((2 * t + 1 : ℕ) : ℝ) * Real.pi < x := lt_of_le_of_ne hx.1 (by
        intro hEq
        exact hxA hEq.symm)
      have hlt2 : x < ((2 * t + 2 : ℕ) : ℝ) * Real.pi := lt_of_le_of_ne hx.2 (by
        intro hEq
        exact hxB hEq)
      have hx0 : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ ((2 * t + 1 : ℕ) : ℝ) * Real.pi) hlt1
      rw [D_eq_sin_mul_pos m x hx0]
      have hfac : 1 / (x + winLen m) - 1 / x ≤ 0 := le_of_lt (D_factor_neg m hm hx0)
      have hsin : Real.sin x ≤ 0 := sin_nonpos_of_odd_piece t ⟨hlt1, hlt2⟩
      exact mul_nonneg_of_nonpos_of_nonpos hsin hfac

/-- inside even piece `[-(2t+1)π,-2tπ]` (valid when `2t+1 ≤ 2m`): D ≤ 0 -/
lemma D_nonpos_on_even_in_piece (m t : ℕ) (hm : 1 ≤ m) (ht : 2 * t + 1 ≤ 2 * m) :
    ∀ x ∈ Set.Icc (-(((2 * t + 1 : ℕ) : ℝ) * Real.pi)) (-(((2 * t : ℕ) : ℝ) * Real.pi)), D m x ≤ 0 := by
  intro x hx
  by_cases hxA : x = -(((2 * t + 1 : ℕ) : ℝ) * Real.pi)
  · rw [hxA]
    exact D_le_zero_at_neg_pi m (2 * t + 1) hm (by omega)
  · by_cases hxB : x = -(((2 * t : ℕ) : ℝ) * Real.pi)
    · rw [hxB]
      exact D_le_zero_at_neg_pi m (2 * t) hm (by omega)
    · have hlt1 : -(((2 * t + 1 : ℕ) : ℝ) * Real.pi) < x := lt_of_le_of_ne hx.1 (by
        intro hEq
        exact hxA hEq.symm)
      have hlt2 : x < -(((2 * t : ℕ) : ℝ) * Real.pi) := lt_of_le_of_ne hx.2 (by
        intro hEq
        exact hxB hEq)
      have hx0 : x < 0 := lt_of_lt_of_le hlt2 (by
        have hle : 0 ≤ ((2 * t : ℕ) : ℝ) * Real.pi := by positivity
        linarith)
      have hxL : 0 < x + winLen m := by
        have hb : -(((2 * t + 1 : ℕ) : ℝ) * Real.pi) + winLen m < x + winLen m := by linarith [hlt1]
        have hcast : ((2 * t + 1 : ℕ) : ℝ) * Real.pi ≤ (2 * m : ℕ) * Real.pi := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (le_of_lt Real.pi_pos)
        have hw : winLen m = (2 * m : ℕ) * Real.pi := by
          unfold winLen
          push_cast
          ring
        have hnneg : 0 ≤ -(((2 * t + 1 : ℕ) : ℝ) * Real.pi) + winLen m := by
          rw [hw]
          linarith
        linarith
      rw [D_eq_sin_mul_neg m x hx0 hxL]
      have hfac : 0 < 1 / (x + winLen m) - 1 / x := D_factor_pos m hx0 hxL
      have hsin : Real.sin x ≤ 0 := sin_nonpos_of_neg_even_piece t ⟨hlt1, hlt2⟩
      exact mul_nonpos_of_nonpos_of_nonneg hsin (le_of_lt hfac)

/-- inside odd piece `[-(2t+2)π,-(2t+1)π]` (valid when `2t+2 ≤ 2m`): D ≥ 0 -/
lemma D_nonneg_on_odd_in_piece (m t : ℕ) (hm : 1 ≤ m) (ht : 2 * t + 2 ≤ 2 * m) :
    ∀ x ∈ Set.Icc (-(((2 * t + 2 : ℕ) : ℝ) * Real.pi)) (-(((2 * t + 1 : ℕ) : ℝ) * Real.pi)), 0 ≤ D m x := by
  intro x hx
  by_cases hxA : x = -(((2 * t + 2 : ℕ) : ℝ) * Real.pi)
  · rw [hxA]
    exact D_ge_zero_at_neg_pi m (2 * t + 2) hm (by omega) ht
  · by_cases hxB : x = -(((2 * t + 1 : ℕ) : ℝ) * Real.pi)
    · rw [hxB]
      exact D_ge_zero_at_neg_pi m (2 * t + 1) hm (by omega) (by omega)
    · have hlt1 : -(((2 * t + 2 : ℕ) : ℝ) * Real.pi) < x := lt_of_le_of_ne hx.1 (by
        intro hEq
        exact hxA hEq.symm)
      have hlt2 : x < -(((2 * t + 1 : ℕ) : ℝ) * Real.pi) := lt_of_le_of_ne hx.2 (by
        intro hEq
        exact hxB hEq)
      have hx0 : x < 0 := lt_of_lt_of_le hlt2 (by
        have hle : 0 ≤ ((2 * t + 1 : ℕ) : ℝ) * Real.pi := by positivity
        linarith)
      have hxL : 0 < x + winLen m := by
        have hb : -(((2 * t + 2 : ℕ) : ℝ) * Real.pi) + winLen m < x + winLen m := by linarith [hlt1]
        have hcast : ((2 * t + 2 : ℕ) : ℝ) * Real.pi ≤ (2 * m : ℕ) * Real.pi := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (le_of_lt Real.pi_pos)
        have hw : winLen m = (2 * m : ℕ) * Real.pi := by
          unfold winLen
          push_cast
          ring
        have hnneg : 0 ≤ -(((2 * t + 2 : ℕ) : ℝ) * Real.pi) + winLen m := by
          rw [hw]
          linarith
        linarith
      rw [D_eq_sin_mul_neg m x hx0 hxL]
      have hfac : 0 < 1 / (x + winLen m) - 1 / x := D_factor_pos m hx0 hxL
      have hsin : 0 ≤ Real.sin x := sin_nonneg_of_neg_odd_piece t ⟨hlt1, hlt2⟩
      exact mul_nonneg hsin (le_of_lt hfac)

-- window bounds --------------------------------------------------------------

/-- compensation: `∫_{u+L}^{v+L} sinc − ∫_u^v sinc = ∫_u^v D` -/
lemma sincInt_shift_sub (m : ℕ) {u v : ℝ} :
    sincInt (u + winLen m) (v + winLen m) - sincInt u v = ∫ x in u..v, D m x := by
  have hshift : (∫ x in u..v, Real.sinc (x + winLen m)) = sincInt (u + winLen m) (v + winLen m) := by
    simpa [sincInt] using
      (intervalIntegral.integral_comp_add_right (f := Real.sinc) (d := winLen m))
  have hf : IntervalIntegrable (fun x : ℝ => Real.sinc (x + winLen m)) volume u v :=
    (Real.continuous_sinc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun x : ℝ => Real.sinc x) volume u v :=
    (Real.continuous_sinc).intervalIntegrable _ _
  calc
    sincInt (u + winLen m) (v + winLen m) - sincInt u v
        = (∫ x in u..v, Real.sinc (x + winLen m)) - sincInt u v := by rw [← hshift]
    _ = (∫ x in u..v, Real.sinc (x + winLen m)) - (∫ x in u..v, Real.sinc x) := rfl
    _ = ∫ x in u..v, (Real.sinc (x + winLen m) - Real.sinc x) := by
            rw [intervalIntegral.integral_sub hf hg]
    _ = ∫ x in u..v, D m x := by
            unfold D
            rfl

/-- difference of window values equals integral of D -/
lemma W_sub_eq_integral_D (m : ℕ) {u v : ℝ} :
    W m v - W m u = ∫ x in u..v, D m x := by
  unfold W
  have h1 : sincInt u (v + winLen m) = sincInt u v + sincInt v (v + winLen m) :=
    (sincInt_add_adjacent u v (v + winLen m)).symm
  have h2 : sincInt u (u + winLen m) = sincInt u (v + winLen m) - sincInt (u + winLen m) (v + winLen m) := by
    have h := sincInt_add_adjacent u (u + winLen m) (v + winLen m)
    linarith
  have hmain : sincInt (u + winLen m) (v + winLen m) - sincInt u v = ∫ x in u..v, D m x :=
    sincInt_shift_sub m
  linarith

/-- window increasing on a piece where D ≥ 0 -/
lemma W_monotone_incr (m : ℕ) {a b u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hD : ∀ x ∈ Set.Icc a b, 0 ≤ D m x) : W m u ≤ W m v := by
  have hsub := W_sub_eq_integral_D (m := m) (u := u) (v := v)
  have hnonneg : 0 ≤ ∫ x in u..v, D m x := by
    apply intervalIntegral.integral_nonneg (a := u) (b := v) huv
    intro x hx
    exact hD x ⟨le_trans hau hx.1, le_trans hx.2 hvb⟩
  linarith

/-- window decreasing on a piece where D ≤ 0 -/
lemma W_monotone_decr (m : ℕ) {a b u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hD : ∀ x ∈ Set.Icc a b, D m x ≤ 0) : W m v ≤ W m u := by
  have hsub := W_sub_eq_integral_D (m := m) (u := u) (v := v)
  have hnonneg_neg : 0 ≤ ∫ x in u..v, -(D m x) := by
    apply intervalIntegral.integral_nonneg (a := u) (b := v) huv
    intro x hx
    exact neg_nonneg.mpr (hD x ⟨le_trans hau hx.1, le_trans hx.2 hvb⟩)
  have hrew : (∫ x in u..v, -(D m x)) = - (∫ x in u..v, D m x) := by
    rw [intervalIntegral.integral_neg]
  have hnonpos : (∫ x in u..v, D m x) ≤ 0 := by linarith
  linarith

-- partial sums: connection to SiFacts.S --------------------------------------

lemma pref_eq_S_pred (k : ℕ) (hk : 1 ≤ k) : pref k = SiFacts.S (k - 1) := by
  rw [S_eq_pref (k - 1)]
  congr 1
  omega

lemma pref_ge_S1 (k : ℕ) (hk : 1 ≤ k) : SiFacts.S 1 ≤ pref k := by
  rw [pref_eq_S_pred k hk]
  exact (SiFacts.S_bounds (k - 1)).1

lemma pref_le_S0 (k : ℕ) : pref k ≤ SiFacts.S 0 := by
  by_cases hk : k = 0
  · subst k
    unfold pref
    simp
    exact le_of_lt S0_pos
  · rw [pref_eq_S_pred k (by omega)]
    exact (SiFacts.S_bounds (k - 1)).2

-- critical values W(-kπ) ------------------------------------------------------

lemma W_neg_kpi_eq (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ 2 * m) :
    W m (-(((k : ℕ) : ℝ) * Real.pi)) = pref k + pref (2 * m - k) := by
  unfold W
  have hwin : -(((k : ℕ) : ℝ) * Real.pi) + winLen m = (((2 * m - k : ℕ) : ℝ) * Real.pi) := by
    unfold winLen
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [hwin]
  have h := sincInt_add_adjacent (-(((k : ℕ) : ℝ) * Real.pi)) 0 (((2 * m - k : ℕ) : ℝ) * Real.pi)
  calc
    sincInt (-(((k : ℕ) : ℝ) * Real.pi)) (((2 * m - k : ℕ) : ℝ) * Real.pi)
        = sincInt (-(((k : ℕ) : ℝ) * Real.pi)) 0 + sincInt 0 (((2 * m - k : ℕ) : ℝ) * Real.pi) := h.symm
    _ = pref k + pref (2 * m - k) := by
            rw [sincInt_neg_mul_pi_zero k, sincInt_zero_mul_pi (2 * m - k)]

lemma W_neg_kpi_ge_S1 (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ 2 * m) :
    SiFacts.S 1 ≤ W m (-(((k : ℕ) : ℝ) * Real.pi)) := by
  rw [W_neg_kpi_eq m k hm hk]
  by_cases hk0 : k = 0
  · subst k
    have hp0 : pref 0 = 0 := by unfold pref; simp
    have h2m : 2 * m - 0 = 2 * m := by omega
    rw [hp0, h2m, zero_add]
    exact pref_ge_S1 (2 * m) (by omega)
  · by_cases hk2m : k = 2 * m
    · subst k
      have hp0 : pref 0 = 0 := by unfold pref; simp
      have h0 : 2 * m - 2 * m = 0 := by omega
      rw [h0, hp0, add_zero]
      exact pref_ge_S1 (2 * m) (by omega)
    · have hk1 : 1 ≤ k := by omega
      have hk2 : 1 ≤ 2 * m - k := by omega
      have h1 := pref_ge_S1 k hk1
      have h2 := pref_ge_S1 (2 * m - k) hk2
      have hpos : 0 ≤ SiFacts.S 1 := le_of_lt S1_pos
      nlinarith




lemma W_neg_kpi_le_two_S0 (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ 2 * m) :
    W m (-(((k : ℕ) : ℝ) * Real.pi)) ≤ 2 * SiFacts.S 0 := by
  rw [W_neg_kpi_eq m k hm hk]
  have h1 := pref_le_S0 k
  have h2 := pref_le_S0 (2 * m - k)
  linarith

-- piece betweenness ------------------------------------------------------------

/-- window between its endpoint values on a D ≥ 0 piece -/
lemma W_between_nonneg_piece (m : ℕ) {a b u : ℝ} (hau : a ≤ u) (hub : u ≤ b)
    (hD : ∀ x ∈ Set.Icc a b, 0 ≤ D m x) :
    W m a ≤ W m u ∧ W m u ≤ W m b := by
  constructor
  · exact W_monotone_incr (m := m) (a := a) (b := b) (u := a) (v := u) (le_refl a) hau hub hD
  · exact W_monotone_incr (m := m) (a := a) (b := b) (u := u) (v := b) hau hub (le_refl b) hD

/-- window between its endpoint values on a D ≤ 0 piece -/
lemma W_between_nonpos_piece (m : ℕ) {a b u : ℝ} (hau : a ≤ u) (hub : u ≤ b)
    (hD : ∀ x ∈ Set.Icc a b, D m x ≤ 0) :
    W m b ≤ W m u ∧ W m u ≤ W m a := by
  constructor
  · exact W_monotone_decr (m := m) (a := a) (b := b) (u := u) (v := b) hau hub (le_refl b) hD
  · exact W_monotone_decr (m := m) (a := a) (b := b) (u := a) (v := u) (le_refl a) hau hub hD

/-- bounds for u on an inside piece `[-(k+1)π,-kπ]` -/
lemma W_inside_piece (m k : ℕ) (hm : 1 ≤ m) (hk : k + 1 ≤ 2 * m) :
    ∀ u ∈ Set.Icc (-(((k + 1 : ℕ) : ℝ) * Real.pi)) (-(((k : ℕ) : ℝ) * Real.pi)),
      SiFacts.S 1 ≤ W m u ∧ W m u ≤ 2 * SiFacts.S 0 := by
  intro u hu
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- k = 2t even: decreasing on the piece
    have hDk : ∀ x ∈ Set.Icc (-(((k + 1 : ℕ) : ℝ) * Real.pi)) (-(((k : ℕ) : ℝ) * Real.pi)), D m x ≤ 0 := by
      simpa [show 2 * t = k by omega, show 2 * t + 1 = k + 1 by omega] using
        (D_nonpos_on_even_in_piece m t hm (by omega))
    have hbet := W_between_nonpos_piece (m := m) (a := -(((k + 1 : ℕ) : ℝ) * Real.pi))
      (b := -(((k : ℕ) : ℝ) * Real.pi)) (u := u) hu.1 hu.2 hDk
    constructor
    · have hb := W_neg_kpi_ge_S1 m k hm (by omega)
      exact le_trans hb hbet.1
    · have ha := W_neg_kpi_le_two_S0 m (k + 1) hm (by omega)
      exact le_trans hbet.2 ha
  · -- k = 2t+1 odd: increasing on the piece
    have hDk : ∀ x ∈ Set.Icc (-(((k + 1 : ℕ) : ℝ) * Real.pi)) (-(((k : ℕ) : ℝ) * Real.pi)), 0 ≤ D m x := by
      simpa [show 2 * t + 1 = k by omega, show 2 * t + 2 = k + 1 by omega] using
        (D_nonneg_on_odd_in_piece m t hm (by omega))
    have hbet := W_between_nonneg_piece (m := m) (a := -(((k + 1 : ℕ) : ℝ) * Real.pi))
      (b := -(((k : ℕ) : ℝ) * Real.pi)) (u := u) hu.1 hu.2 hDk
    constructor
    · have ha := W_neg_kpi_ge_S1 m (k + 1) hm (by omega)
      exact le_trans ha hbet.1
    · have hb := W_neg_kpi_le_two_S0 m k hm (by omega)
      exact le_trans hbet.2 hb


/-- winLen m as a natural multiple of π -/
lemma winLen_eq_nat_pi (m : ℕ) : winLen m = ((2 * m : ℕ) : ℝ) * Real.pi := by
  unfold winLen
  push_cast
  ring


/-- `-((2m:ℕ):ℝ)π = -winLen m` -/

lemma nat_two_mul_pi (m : ℕ) : (((2 * m : ℕ) : ℝ) * Real.pi) = winLen m := by
  unfold winLen
  push_cast
  ring

lemma neg_nat_two_mul_pi_eq (m : ℕ) : -(((2 * m : ℕ) : ℝ) * Real.pi) = -winLen m := by
  unfold winLen
  push_cast
  ring

/-- inside: `u ∈ [-2mπ, 0]` gives `S1 ≤ W m u ≤ 2·S0` -/
lemma W_inside_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∀ u : ℝ, -winLen m ≤ u → u ≤ 0 →
      SiFacts.S 1 ≤ W m u ∧ W m u ≤ 2 * SiFacts.S 0 := by
  intro u huL hu0
  by_cases hEq : u = -winLen m
  · have h1 : SiFacts.S 1 ≤ W m (-winLen m) := by
      have h := W_neg_kpi_ge_S1 m (2 * m) hm (by omega)
      rwa [nat_two_mul_pi m] at h
    have h2 : W m (-winLen m) ≤ 2 * SiFacts.S 0 := by
      have h := W_neg_kpi_le_two_S0 m (2 * m) hm (by omega)
      rwa [nat_two_mul_pi m] at h
    rw [hEq]
    exact ⟨h1, h2⟩
  · have huL' : -winLen m < u := lt_of_le_of_ne huL (by
      intro hEq2
      apply hEq
      exact hEq2.symm)
    let w : ℝ := -u / Real.pi
    have hw0 : 0 ≤ w := by
      dsimp [w]
      have hnonneg : 0 ≤ -u := by linarith
      exact div_nonneg hnonneg (le_of_lt Real.pi_pos)
    have hwlt : w < (2 * (m : ℝ)) := by
      dsimp [w]
      have h1 : -u < winLen m := by linarith
      rw [winLen_eq_nat_pi m] at h1
      have h2 : (-u) / Real.pi < ((2 * m : ℕ) : ℝ) * Real.pi / Real.pi := by
        exact div_lt_div_of_pos_right h1 Real.pi_pos
      have h3 : ((2 * m : ℕ) : ℝ) * Real.pi / Real.pi = (2 * (m : ℝ)) := by
        field_simp [Real.pi_ne_zero]
        push_cast
        ring
      rwa [h3] at h2
    let kk : ℤ := Int.floor w
    let n : ℕ := kk.toNat
    have hn_eq : (n : ℤ) = kk := by
      dsimp [n]
      exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr hw0)
    have hn2r : (n : ℝ) = (kk : ℝ) := by
      have hh := congrArg (fun z : ℤ => (z : ℝ)) hn_eq
      simpa using hh
    have hkk_lt2m : kk < 2 * (m : ℤ) := by
      have hkk_le_w : (kk : ℝ) ≤ w := Int.floor_le w
      have hreal : (kk : ℝ) < (2 * (m : ℤ) : ℝ) := by
        have hc : (2 * (m : ℤ) : ℝ) = 2 * (m : ℝ) := by simp
        rw [hc]
        exact lt_of_le_of_lt hkk_le_w hwlt
      have hz : kk < (2 * (m : ℤ)) := by
        exact_mod_cast hreal
      simpa using hz
    have hn_lt_2m : n + 1 ≤ 2 * m := by
      have hk2 : kk + 1 ≤ 2 * (m : ℤ) := by omega
      have hn2 : (n : ℤ) + 1 ≤ 2 * (m : ℤ) := by
        simpa [hn_eq] using hk2
      have hn3 : ((n + 1 : ℕ) : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by
        simpa [Nat.cast_add, Nat.cast_mul] using hn2
      exact_mod_cast hn3
    have hkk_le_w2 : (kk : ℝ) * Real.pi ≤ -u := by
      have h := Int.floor_le w
      have : (kk : ℝ) ≤ (-u) / Real.pi := h
      exact (le_div_iff₀ Real.pi_pos).mp this
    have hw_lt_kk : -u < ((kk : ℝ) + 1) * Real.pi := by
      have h := Int.lt_floor_add_one w
      have : (-u) / Real.pi < (kk : ℝ) + 1 := h
      exact (div_lt_iff₀ Real.pi_pos).mp this
    have huB : u ≤ -(((n : ℕ) : ℝ) * Real.pi) := by
      have : (kk : ℝ) * Real.pi ≤ -u := hkk_le_w2
      have h : u ≤ -((kk : ℝ) * Real.pi) := by linarith
      rwa [← hn2r] at h
    have huA : -(((n + 1 : ℕ) : ℝ) * Real.pi) ≤ u := by
      have : -u < (((kk : ℝ) + 1) * Real.pi) := hw_lt_kk
      have h : -(((kk : ℝ) + 1) * Real.pi) < u := by linarith
      have hn1r : ((n + 1 : ℕ) : ℝ) = (kk : ℝ) + 1 := by
        have hc := congrArg (fun z : ℤ => (z : ℝ)) hn_eq
        simp [Nat.cast_add] at hc ⊢
        linarith
      have h' : -(((n + 1 : ℕ) : ℝ) * Real.pi) < u := by
        simpa [← hn1r] using h
      exact le_of_lt h'
    have hpiece := W_inside_piece m n hm hn_lt_2m u ⟨huA, huB⟩
    exact hpiece


-- outside: window from a nonnegative start ------------------------------------

/-- `W(jπ) = block j m` (2m half-periods from j) -/
lemma W_nat_pi_eq_block (m j : ℕ) : W m (((j : ℕ) : ℝ) * Real.pi) = SiFacts.block j m := by
  unfold W SiFacts.block
  have hw : ((j : ℕ) : ℝ) * Real.pi + winLen m = (((j + 2 * m : ℕ) : ℝ) * Real.pi) := by
    unfold winLen
    push_cast
    ring
  rw [hw]
  rfl

/-- `|u k| ≤ |u j|` when `j ≤ k` -/
lemma abs_u_le_of_le (j k : ℕ) (hjk : j ≤ k) : |SiFacts.u k| ≤ |SiFacts.u j| := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst j
      rfl
  | succ k ih =>
      by_cases hjk' : j ≤ k
      · exact le_trans (le_of_lt (SiFacts.u_abs_decreasing k)) (ih hjk')
      · have : j = k + 1 := by omega
        subst j
        rfl

/-- even-index `u(2t) ≤ u 0` -/
lemma u_even_le_u0 (t : ℕ) : SiFacts.u (2 * t) ≤ SiFacts.u 0 := by
  have hmag := abs_u_le_of_le 0 (2 * t) (by omega)
  rw [abs_of_pos (SiFacts.u0_pos), abs_of_pos (SiFacts.u_pos_even t)] at hmag
  exact hmag

/-- `u 1 ≤ u(2t+1)` -/
lemma u1_le_u_odd (t : ℕ) : SiFacts.u 1 ≤ SiFacts.u (2 * t + 1) := by
  have hmag := abs_u_le_of_le 1 (2 * t + 1) (by omega)
  have h1 : SiFacts.u 1 < 0 := SiFacts.u_neg_odd 0
  have hodd : SiFacts.u (2 * t + 1) < 0 := SiFacts.u_neg_odd t
  rw [abs_of_neg h1, abs_of_neg hodd] at hmag
  linarith

/-- block starting at j: `u1 ≤ block j m ≤ S0` -/
lemma block_out_bounds (m j : ℕ) (hm : 1 ≤ m) :
    SiFacts.u 1 ≤ SiFacts.block j m ∧ SiFacts.block j m ≤ SiFacts.S 0 := by
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hb := (SiFacts.block_even_bounds t m hm)
    -- hb : 0 < block (2t) m ∧ block < u (2t); block j m with j = 2t
    have hb' : 0 < SiFacts.block j m ∧ SiFacts.block j m < SiFacts.u j := by
      simpa [ht, Nat.two_mul] using hb
    constructor
    · have hu1 : SiFacts.u 1 < 0 := SiFacts.u_neg_odd 0
      linarith
    · have hu := u_even_le_u0 t
      have hu' : SiFacts.u j ≤ SiFacts.u 0 := by simpa [ht, Nat.two_mul] using hu
      have hS0 : SiFacts.u 0 = SiFacts.S 0 := S0_eq_u0.symm
      rw [hS0] at hu'
      have hlt := hb'.2
      exact le_trans (le_of_lt hlt) hu'
  · have hb := (SiFacts.block_odd_bounds t m hm)
    have hb' : SiFacts.u j < SiFacts.block j m ∧ SiFacts.block j m < 0 := by
      simpa [← ht] using hb
    constructor
    · have hu := u1_le_u_odd t
      have hu' : SiFacts.u 1 ≤ SiFacts.u j := by simpa [← ht] using hu
      linarith
    · have hS0 : 0 ≤ SiFacts.S 0 := le_of_lt S0_pos
      linarith

/-- endpoint value at `jπ` is between u1 and S0 -/
lemma W_nat_pi_bounds (m j : ℕ) (hm : 1 ≤ m) :
    SiFacts.u 1 ≤ W m (((j : ℕ) : ℝ) * Real.pi) ∧
      W m (((j : ℕ) : ℝ) * Real.pi) ≤ SiFacts.S 0 := by
  rw [W_nat_pi_eq_block]
  exact block_out_bounds m j hm

/-- outside piece bounds: on `[jπ,(j+1)π]` for any j -/
lemma W_out_piece (m j : ℕ) (hm : 1 ≤ m) :
    ∀ v ∈ Set.Icc (((j : ℕ) : ℝ) * Real.pi) (((j + 1 : ℕ) : ℝ) * Real.pi),
      SiFacts.u 1 ≤ W m v ∧ W m v ≤ SiFacts.S 0 := by
  intro v hv
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- j = 2t even: decreasing on [2tπ,(2t+1)π]
    have hD : ∀ x ∈ Set.Icc (((j : ℕ) : ℝ) * Real.pi) (((j + 1 : ℕ) : ℝ) * Real.pi), D m x ≤ 0 := by
      simpa [show 2 * t = j by omega, show 2 * t + 1 = j + 1 by omega] using
        (D_nonpos_on_even_out_piece m t hm)
    have hbet := W_between_nonpos_piece (m := m) (a := ((j : ℕ) : ℝ) * Real.pi)
      (b := ((j + 1 : ℕ) : ℝ) * Real.pi) (u := v) hv.1 hv.2 hD
    constructor
    · have hb := (W_nat_pi_bounds m (j + 1) hm).1
      exact le_trans hb hbet.1
    · have ha := (W_nat_pi_bounds m j hm).2
      exact le_trans hbet.2 ha
  · -- j = 2t+1 odd: increasing
    have hD : ∀ x ∈ Set.Icc (((j : ℕ) : ℝ) * Real.pi) (((j + 1 : ℕ) : ℝ) * Real.pi), 0 ≤ D m x := by
      simpa [show 2 * t + 1 = j by omega, show 2 * t + 2 = j + 1 by omega] using
        (D_nonneg_on_odd_out_piece m t hm)
    have hbet := W_between_nonneg_piece (m := m) (a := ((j : ℕ) : ℝ) * Real.pi)
      (b := ((j + 1 : ℕ) : ℝ) * Real.pi) (u := v) hv.1 hv.2 hD
    constructor
    · have ha := (W_nat_pi_bounds m j hm).1
      exact le_trans ha hbet.1
    · have hb := (W_nat_pi_bounds m (j + 1) hm).2
      exact le_trans hbet.2 hb

/-- outside: `v ≥ 0` gives `u1 ≤ W m v ≤ S0` -/
lemma W_outside_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∀ v : ℝ, 0 ≤ v → SiFacts.u 1 ≤ W m v ∧ W m v ≤ SiFacts.S 0 := by
  intro v hv0
  let w : ℝ := v / Real.pi
  have hw0 : 0 ≤ w := by
    dsimp [w]
    exact div_nonneg hv0 (le_of_lt Real.pi_pos)
  let kk : ℤ := Int.floor w
  let n : ℕ := kk.toNat
  have hn_eq : (n : ℤ) = kk := by
    dsimp [n]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr hw0)
  have hn2r : (n : ℝ) = (kk : ℝ) := by
    have hh := congrArg (fun z : ℤ => (z : ℝ)) hn_eq
    simpa using hh
  have hkk_le_w : (kk : ℝ) ≤ w := Int.floor_le w
  have hw_lt_kk : w < (kk : ℝ) + 1 := Int.lt_floor_add_one w
  have hvA : ((n : ℕ) : ℝ) * Real.pi ≤ v := by
    have this2 : (kk : ℝ) ≤ v / Real.pi := hkk_le_w
    have h : (kk : ℝ) * Real.pi ≤ v := (le_div_iff₀ (Real.pi_pos)).mp this2
    -- (kk:ℝ)*π ≤ v; rewrite (kk:ℝ) → (n:ℝ)
    have h' : (n : ℝ) * Real.pi ≤ v := by
      simpa [← hn2r] using h
    exact h'
  have hvB : v ≤ ((n + 1 : ℕ) : ℝ) * Real.pi := by
    have : v / Real.pi < (kk : ℝ) + 1 := hw_lt_kk
    have h : v < ((kk : ℝ) + 1) * Real.pi := (div_lt_iff₀ Real.pi_pos).mp this
    have hn1r : ((n + 1 : ℕ) : ℝ) = (kk : ℝ) + 1 := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) hn_eq
      simp [Nat.cast_add] at hc ⊢
      linarith
    have h' : v < ((n + 1 : ℕ) : ℝ) * Real.pi := by
      simpa [hn1r] using h
    exact le_of_lt h'
  have hpiece := W_out_piece m n hm v ⟨hvA, hvB⟩
  exact hpiece


-- theorem assembly tests -------------------------------------------------------


-- theorem assembly helpers ----------------------------------------------------

/-- `q-p` as a positive natural -/
def gridM (p q : ℤ) : ℕ := Int.toNat (q - p)

lemma gridM_cast (p q : ℤ) (hpq : p < q) : ((gridM p q : ℕ) : ℝ) = ((q - p : ℤ) : ℝ) := by
  have hd : 0 ≤ q - p := by omega
  have hz : ((gridM p q : ℕ) : ℤ) = q - p := by
    simpa [gridM] using (Int.toNat_of_nonneg hd)
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa using hr

lemma gridM_pos (p q : ℤ) (hpq : p < q) : 1 ≤ gridM p q := by
  have hd : 0 ≤ q - p := by omega
  have hcast : ((Int.toNat (q - p) : ℕ) : ℤ) = q - p := Int.toNat_of_nonneg hd
  have h1 : (1 : ℤ) ≤ q - p := by omega
  dsimp [gridM]
  rw [← hcast] at h1
  exact_mod_cast h1

/-- `2n(qπ/n − θ0) = 2n(pπ/n − θ0) + winLen(gridM p q)` -/
lemma grid_win_shift (n : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hpq : p < q) (θ0 : ℝ) :
    (2 * (n : ℝ)) * (((q : ℝ) * Real.pi) / (n : ℝ) - θ0) =
      (2 * (n : ℝ)) * (((p : ℝ) * Real.pi) / (n : ℝ) - θ0) + winLen (gridM p q) := by
  have hnz : (n : ℝ) ≠ 0 := by positivity
  have hq : (n : ℝ) * (((q : ℝ) * Real.pi) / (n : ℝ)) = (q : ℝ) * Real.pi := by field_simp [hnz]
  have hp : (n : ℝ) * (((p : ℝ) * Real.pi) / (n : ℝ)) = (p : ℝ) * Real.pi := by field_simp [hnz]
  have hcast : ((q - p : ℤ) : ℝ) = (q : ℝ) - (p : ℝ) := by rw [Int.cast_sub]
  have hm : ((gridM p q : ℕ) : ℝ) = ((q - p : ℤ) : ℝ) := gridM_cast p q hpq
  have hcore : (2 * (n : ℝ)) * (((q : ℝ) * Real.pi / (n : ℝ)) - θ0) -
        (2 * (n : ℝ)) * (((p : ℝ) * Real.pi / (n : ℝ)) - θ0) = winLen (gridM p q) := by
    calc
      (2 * (n : ℝ)) * (((q : ℝ) * Real.pi / (n : ℝ)) - θ0) - (2 * (n : ℝ)) * (((p : ℝ) * Real.pi / (n : ℝ)) - θ0)
          = (2 * (n : ℝ)) * (((q : ℝ) * Real.pi / (n : ℝ)) - ((p : ℝ) * Real.pi / (n : ℝ))) := by ring
      _ = 2 * ((n : ℝ) * ((q : ℝ) * Real.pi / (n : ℝ))) - 2 * ((n : ℝ) * ((p : ℝ) * Real.pi / (n : ℝ))) := by ring
      _ = 2 * ((q : ℝ) * Real.pi) - 2 * ((p : ℝ) * Real.pi) := by rw [hq, hp]
      _ = 2 * ((q : ℝ) - (p : ℝ)) * Real.pi := by ring_nf
      _ = (2 * ((q - p : ℤ) : ℝ)) * Real.pi := by rw [hcast]
      _ = 2 * ((gridM p q : ℕ) : ℝ) * Real.pi := by rw [hm]
      _ = winLen (gridM p q) := by
              unfold winLen
              rfl
  have h1 : (2 * (n : ℝ)) * (((q : ℝ) * Real.pi / (n : ℝ)) - θ0) -
        (2 * (n : ℝ)) * (((p : ℝ) * Real.pi / (n : ℝ)) - θ0) = winLen (gridM p q) := hcore
  linarith

/-- lower endpoint of window when θ0 is inside -/
lemma grid_win_start_ge (n : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hpq : p < q) (θ0 : ℝ)
    (hhi : θ0 ≤ ((q : ℝ) * Real.pi) / (n : ℝ)) :
    -winLen (gridM p q) ≤ (2 * (n : ℝ)) * (((p : ℝ) * Real.pi) / (n : ℝ) - θ0) := by
  let a : ℝ := (p : ℝ) * Real.pi / (n : ℝ)
  let b : ℝ := (q : ℝ) * Real.pi / (n : ℝ)
  have hs := grid_win_shift n hn p q hpq θ0
  have h1 : (2 * (n : ℝ)) * (a - θ0) - (2 * (n : ℝ)) * (b - θ0) = -winLen (gridM p q) := by
    have : (2 * (n : ℝ)) * (b - θ0) = (2 * (n : ℝ)) * (a - θ0) + winLen (gridM p q) := hs
    linarith
  have hb0 : 0 ≤ (2 * (n : ℝ)) * (b - θ0) := by
    have hd : 0 ≤ b - θ0 := by linarith
    exact mul_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)) hd
  have h2 : (2 * (n : ℝ)) * (a - θ0) ≥ (2 * (n : ℝ)) * (a - θ0) - (2 * (n : ℝ)) * (b - θ0) := by linarith
  rw [h1] at h2
  linarith

/-- upper endpoint of window when θ0 is inside -/
lemma grid_win_start_le (n : ℕ) (hn : 1 ≤ n) (p : ℤ) (θ0 : ℝ)
    (hlo : ((p : ℝ) * Real.pi) / (n : ℝ) ≤ θ0) :
    (2 * (n : ℝ)) * (((p : ℝ) * Real.pi) / (n : ℝ) - θ0) ≤ 0 := by
  have hd : ((p : ℝ) * Real.pi) / (n : ℝ) - θ0 ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * (n : ℝ)) hd

/-- mirror: integral over a window ending at ≤ 0 equals window from ≥ 0 -/
lemma sincInt_refl_shift (L : ℝ) {A : ℝ} : sincInt (A - L) A = sincInt (-A) (-A + L) := by
  unfold sincInt
  have hh := intervalIntegral.integral_comp_neg (f := Real.sinc) (a := A - L) (b := A)
  have hneg : (∫ x in (A - L)..A, Real.sinc x) = ∫ x in -A..-(A - L), Real.sinc x := by
    simpa [Real.sinc_neg] using hh
  rw [hneg]
  congr 1
  ring


lemma grid_win_start_nonneg (n : ℕ) (hn : 1 ≤ n) (p : ℤ) (θ0 : ℝ)
    (hlo : θ0 ≤ ((p : ℝ) * Real.pi) / (n : ℝ)) :
    0 ≤ (2 * (n : ℝ)) * (((p : ℝ) * Real.pi) / (n : ℝ) - θ0) := by
  have hd : 0 ≤ ((p : ℝ) * Real.pi) / (n : ℝ) - θ0 := by linarith
  exact mul_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)) hd

lemma grid_win_end_nonpos (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (θ0 : ℝ)
    (hhi : ((q : ℝ) * Real.pi) / (n : ℝ) ≤ θ0) :
    (2 * (n : ℝ)) * (((q : ℝ) * Real.pi) / (n : ℝ) - θ0) ≤ 0 := by
  have hd : ((q : ℝ) * Real.pi) / (n : ℝ) - θ0 ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * (n : ℝ)) hd


theorem si_inside_lower (n : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hpq : p < q)
    (hlen : q - p ≤ 6) (θ0 : ℝ)
    (hlo : (p : ℝ) * Real.pi / (n : ℝ) ≤ θ0)
    (hhi : θ0 ≤ (q : ℝ) * Real.pi / (n : ℝ)) :
    (4 / 3 : ℝ) ≤ LinInt n ((p : ℝ) * Real.pi / (n : ℝ)) ((q : ℝ) * Real.pi / (n : ℝ)) θ0  := by
  let a : ℝ := (p : ℝ) * Real.pi / (n : ℝ)
  let b : ℝ := (q : ℝ) * Real.pi / (n : ℝ)
  have hM : LinInt n a b θ0 = W (gridM p q) (2 * (n : ℝ) * (a - θ0)) := by
    have hlin := linint_eq_sinc n hn a b θ0
    rw [hlin]
    rw [grid_win_shift n hn p q hpq θ0]
    rfl
  have hstart_ge := grid_win_start_ge n hn p q hpq θ0 hhi
  have hstart_le := grid_win_start_le n hn p θ0 hlo
  have hb := W_inside_bounds (gridM p q) (gridM_pos p q hpq) (2 * (n : ℝ) * (a - θ0)) hstart_ge hstart_le
  have hS1 : (4 / 3 : ℝ) ≤ SiFacts.S 1 := S1_ge_four_thirds
  rw [hM]
  exact le_trans hS1 hb.1


theorem si_inside_upper (n : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hpq : p < q)
    (hlen : q - p ≤ 6) (θ0 : ℝ)
    (hlo : (p : ℝ) * Real.pi / (n : ℝ) ≤ θ0)
    (hhi : θ0 ≤ (q : ℝ) * Real.pi / (n : ℝ)) :
    LinInt n ((p : ℝ) * Real.pi / (n : ℝ)) ((q : ℝ) * Real.pi / (n : ℝ)) θ0 ≤ 4  := by
  let a : ℝ := (p : ℝ) * Real.pi / (n : ℝ)
  let b : ℝ := (q : ℝ) * Real.pi / (n : ℝ)
  have hM : LinInt n a b θ0 = W (gridM p q) (2 * (n : ℝ) * (a - θ0)) := by
    have hlin := linint_eq_sinc n hn a b θ0
    rw [hlin]
    rw [grid_win_shift n hn p q hpq θ0]
    rfl
  have hstart_ge := grid_win_start_ge n hn p q hpq θ0 hhi
  have hstart_le := grid_win_start_le n hn p θ0 hlo
  have hb := W_inside_bounds (gridM p q) (gridM_pos p q hpq) (2 * (n : ℝ) * (a - θ0)) hstart_ge hstart_le
  have hS0 : 2 * SiFacts.S 0 ≤ 4 := by
    have h1 := S0_le_two
    have h2 : 0 ≤ 2 := by norm_num
    nlinarith
  rw [hM]
  exact le_trans hb.2 hS0


theorem si_outside_lower (n : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hpq : p < q)
    (hlen : q - p ≤ 6) (θ0 : ℝ)
    (hout : θ0 ≤ (p : ℝ) * Real.pi / (n : ℝ) ∨ (q : ℝ) * Real.pi / (n : ℝ) ≤ θ0) :
    -1 ≤ LinInt n ((p : ℝ) * Real.pi / (n : ℝ)) ((q : ℝ) * Real.pi / (n : ℝ)) θ0  := by
  let a : ℝ := (p : ℝ) * Real.pi / (n : ℝ)
  let b : ℝ := (q : ℝ) * Real.pi / (n : ℝ)
  have hlin := linint_eq_sinc n hn a b θ0
  rcases hout with hleft | hright
  · -- θ0 ≤ a: window from nonneg start
    have hM : LinInt n a b θ0 = W (gridM p q) (2 * (n : ℝ) * (a - θ0)) := by
      rw [hlin]
      rw [grid_win_shift n hn p q hpq θ0]
      rfl
    have hstart := grid_win_start_nonneg n hn p θ0 hleft
    have hb := W_outside_bounds (gridM p q) (gridM_pos p q hpq) (2 * (n : ℝ) * (a - θ0)) hstart
    have hu1 : -1 ≤ SiFacts.u 1 := u1_ge_neg_one
    rw [hM]
    exact le_trans hu1 hb.1
  · -- b ≤ θ0: reflect to a window from a nonneg start
    have hA : (2 * (n : ℝ) * (a - θ0)) = (2 * (n : ℝ) * (b - θ0)) - winLen (gridM p q) := by
      have hs := grid_win_shift n hn p q hpq θ0
      linarith
    have hM : LinInt n a b θ0 = W (gridM p q) (-(2 * (n : ℝ) * (b - θ0))) := by
      rw [hlin]
      rw [hA]
      -- sincInt (B−L) B = sincInt (−B) (−B + L)
      change sincInt ((2 * (n : ℝ) * (b - θ0)) - winLen (gridM p q)) (2 * (n : ℝ) * (b - θ0))
        = W (gridM p q) (-(2 * (n : ℝ) * (b - θ0)))
      rw [sincInt_refl_shift (winLen (gridM p q)) (A := (2 * (n : ℝ) * (b - θ0)))]
      rfl
    have hstart : 0 ≤ -(2 * (n : ℝ) * (b - θ0)) := by
      have hB := grid_win_end_nonpos n hn q θ0 hright
      linarith
    have hb := W_outside_bounds (gridM p q) (gridM_pos p q hpq) (-(2 * (n : ℝ) * (b - θ0))) hstart
    have hu1 : -1 ≤ SiFacts.u 1 := u1_ge_neg_one
    rw [hM]
    exact le_trans hu1 hb.1


theorem si_outside_upper (n : ℕ) (hn : 1 ≤ n) (p q : ℤ) (hpq : p < q)
    (hlen : q - p ≤ 6) (θ0 : ℝ)
    (hout : θ0 ≤ (p : ℝ) * Real.pi / (n : ℝ) ∨ (q : ℝ) * Real.pi / (n : ℝ) ≤ θ0) :
    LinInt n ((p : ℝ) * Real.pi / (n : ℝ)) ((q : ℝ) * Real.pi / (n : ℝ)) θ0 ≤ 2  := by
  let a : ℝ := (p : ℝ) * Real.pi / (n : ℝ)
  let b : ℝ := (q : ℝ) * Real.pi / (n : ℝ)
  have hlin := linint_eq_sinc n hn a b θ0
  rcases hout with hleft | hright
  · have hM : LinInt n a b θ0 = W (gridM p q) (2 * (n : ℝ) * (a - θ0)) := by
      rw [hlin]
      rw [grid_win_shift n hn p q hpq θ0]
      rfl
    have hstart := grid_win_start_nonneg n hn p θ0 hleft
    have hb := W_outside_bounds (gridM p q) (gridM_pos p q hpq) (2 * (n : ℝ) * (a - θ0)) hstart
    rw [hM]
    exact le_trans hb.2 S0_le_two
  · have hA : (2 * (n : ℝ) * (a - θ0)) = (2 * (n : ℝ) * (b - θ0)) - winLen (gridM p q) := by
      have hs := grid_win_shift n hn p q hpq θ0
      linarith
    have hM : LinInt n a b θ0 = W (gridM p q) (-(2 * (n : ℝ) * (b - θ0))) := by
      rw [hlin]
      rw [hA]
      change sincInt ((2 * (n : ℝ) * (b - θ0)) - winLen (gridM p q)) (2 * (n : ℝ) * (b - θ0))
        = W (gridM p q) (-(2 * (n : ℝ) * (b - θ0)))
      rw [sincInt_refl_shift (winLen (gridM p q)) (A := (2 * (n : ℝ) * (b - θ0)))]
      rfl
    have hstart : 0 ≤ -(2 * (n : ℝ) * (b - θ0)) := by
      have hB := grid_win_end_nonpos n hn q θ0 hright
      linarith
    have hb := W_outside_bounds (gridM p q) (gridM_pos p q hpq) (-(2 * (n : ℝ) * (b - θ0))) hstart
    rw [hM]
    exact le_trans hb.2 S0_le_two


end SiBounds
end Submission
