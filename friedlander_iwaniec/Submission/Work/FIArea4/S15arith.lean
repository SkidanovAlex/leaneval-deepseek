/-
# Area 4 / FI §15: the final arithmetic (the "endgame" absorption)

This file isolates the **scalar arithmetic** that turns the analytic bound produced by the §15
chain (Proposition 14.1 at each dyadic scale + the closing estimate) into the frozen statement
`Work.FITop3.Area4` / `Work.FITop4.Area4`:

  `‖V(β)‖ ≤ c·(P^{-1} + X^{-1/3})·N²`   for `1 ≤ X ≤ N^{1/9}`.

The analytic part of §15 produces an inequality of the shape

  `V ≤ C · θ² · (log N + 1)^K · (X^{-1/2}N + N^{1/3}X^{-1/3}N^{2/3} + N^{23/24+ε} + 1) · N`,

with a log-power `K` bounded by the budget `2·2^20` of the frozen `Params`
(`A' ≥ 2A + 2^20`, so `θ²(log x)^K ≤ (log x)^{K-2A'} ≤ 1` whenever `K ≤ 2A'`).  The three
ingredients are

* `theta_sq_log_pow_le` : `θ²(log N + 1)^K ≤ 2^K` for every `K ≤ 2·2^20` — this is why an
  absolute constant `c` in `Area4` is compatible with the paper's `≪` (whose implied constants
  may depend on the fixed parameters): all log-powers up to `2^20` are absorbed by the saving
  `θ² = (log x)^{-2A'}`;
* `X_inv_third_ge` : `N^{-1/27} ≤ X^{-1/3}` (from `X ≤ N^{1/9}`), and
* the four term bounds `half_le`, `mid_le`, `tail_le`, `one_le_third`, which show that each of the
  four terms of the bracket is `≤ X^{-1/3}N²`.

Nothing here uses anything but the fields of `Work.FITop.Params`; the file is self-contained.
-/
import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea4

open scoped BigOperators

/-! ### `log N` versus `log x` -/

/-- `1 < log x` (from `3 ≤ x`). -/
lemma log_x_gt_one (Pa : Work.FITop.Params) : 1 < Real.log (Pa.x : ℝ) := by
  have h : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have h2 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast Pa.hx
  linarith

/-- `log N ≤ (1/2)·log x`: from (4.6), `N < x^{1/2}(log x)^{-B} ≤ x^{1/2}`. -/
lemma log_N_le_half_log_x (Pa : Work.FITop.Params) :
    Real.log Pa.N ≤ (1/2) * Real.log (Pa.x : ℝ) := by
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlogx1 : 1 ≤ Real.log (Pa.x : ℝ) := le_of_lt (log_x_gt_one Pa)
  have hpow : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hlogx1 (show -Pa.B ≤ 0 by linarith [Pa.hB])
    simpa [Real.rpow_zero] using h
  have hle : Pa.N ≤ (Pa.x : ℝ) ^ ((1 : ℝ)/2) := by
    have h1 := Pa.hNhi
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ)/2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ)/2) := by
      simpa using mul_le_mul_of_nonneg_left hpow
        (Real.rpow_nonneg (le_of_lt hxpos) ((1:ℝ)/2))
    linarith
  have hlogN : Real.log Pa.N ≤ Real.log ((Pa.x : ℝ) ^ ((1 : ℝ)/2)) :=
    Real.log_le_log (by linarith [Pa.hN1]) hle
  have hrw : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ)/2)) = (1/2) * Real.log (Pa.x : ℝ) :=
    Real.log_rpow hxpos ((1:ℝ)/2)
  have := log_x_gt_one Pa
  linarith

/-- `log N + 1 ≤ 2 log x`. -/
lemma log_N_add_one_le (Pa : Work.FITop.Params) :
    Real.log Pa.N + 1 ≤ 2 * Real.log (Pa.x : ℝ) := by
  have h1 := log_N_le_half_log_x Pa
  have h2 := log_x_gt_one Pa
  linarith

/-! ### Absorbing the log-power of §15 into `θ²` -/

/-- **The `(log N)^K` budget.**  For `K ≤ 2·2^20` and `M ≥ 0`,
`θ²·(log N + 1)^K·M ≤ 2^K·M`.  The proof is
`θ²(log N+1)^K ≤ (log x)^{-2A'}(2log x)^K = 2^K (log x)^{K-2A'} ≤ 2^K`, which uses
`K ≤ 2A'` (`A' ≥ 2A + 2^20 ≥ 2^20`) and `log N + 1 ≤ 2 log x`. -/
theorem theta_sq_log_pow_le (Pa : Work.FITop.Params) (K : ℕ)
    (hK : (K : ℝ) ≤ 2 * (2:ℝ)^20) (M : ℝ) (hM : 0 ≤ M) :
    Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ K * M ≤ (2:ℝ)^K * M := by
  have hlogx_ge1 : 1 ≤ Real.log (Pa.x : ℝ) := le_of_lt (log_x_gt_one Pa)
  have hlogx_pos : 0 < Real.log (Pa.x : ℝ) := lt_of_lt_of_le one_pos hlogx_ge1
  have hA'ge : (2:ℝ)^20 ≤ Pa.A' := by nlinarith [Pa.hA', Pa.hA]
  have htheta : Pa.θ ^ 2 = (Real.log (Pa.x : ℝ)) ^ (-(2 * Pa.A')) := by
    rw [Pa.hθ]
    rw [← Real.rpow_natCast ((Real.log (Pa.x:ℝ)) ^ (-Pa.A')) 2]
    rw [← Real.rpow_mul (le_of_lt hlogx_pos)]
    ring_nf
  have hpow_le : (Real.log Pa.N + 1) ^ K ≤ (2 * Real.log (Pa.x : ℝ)) ^ K :=
    pow_le_pow_left₀
      (by linarith [Real.log_nonneg (show (1:ℝ) ≤ Pa.N by linarith [Pa.hN1])])
      (log_N_add_one_le Pa) K
  have hmain : (Real.log (Pa.x : ℝ)) ^ (-(2 * Pa.A')) * (Real.log (Pa.x : ℝ)) ^ K
      = (Real.log (Pa.x : ℝ)) ^ ((K:ℝ) - 2 * Pa.A') := by
    rw [← Real.rpow_natCast (Real.log (Pa.x : ℝ)) K]
    rw [← Real.rpow_add hlogx_pos]
    ring_nf
  have hle_one : (Real.log (Pa.x : ℝ)) ^ ((K:ℝ) - 2 * Pa.A') ≤ 1 := by
    have h1 : (Real.log (Pa.x : ℝ)) ^ ((K:ℝ) - 2 * Pa.A')
        = ((Real.log (Pa.x : ℝ)) ^ (2 * Pa.A' - (K:ℝ)))⁻¹ := by
      rw [← Real.rpow_neg (le_of_lt hlogx_pos) (2 * Pa.A' - (K:ℝ))]
      congr 1; ring
    rw [h1]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hlogx_ge1 (by linarith))
  have hLnn : 0 ≤ (Real.log (Pa.x : ℝ)) ^ (-(2 * Pa.A')) :=
    Real.rpow_nonneg (le_of_lt hlogx_pos) _
  calc Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ K * M
      = (Real.log (Pa.x : ℝ)) ^ (-(2 * Pa.A')) * (Real.log Pa.N + 1) ^ K * M := by
        rw [htheta]
    _ ≤ (Real.log (Pa.x : ℝ)) ^ (-(2 * Pa.A')) * (2 * Real.log (Pa.x : ℝ)) ^ K * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact mul_le_mul_of_nonneg_left hpow_le hLnn
    _ = (2:ℝ)^K * ((Real.log (Pa.x : ℝ)) ^ (-(2 * Pa.A'))
          * (Real.log (Pa.x : ℝ)) ^ K) * M := by
        rw [mul_pow]; ring
    _ = (2:ℝ)^K * (Real.log (Pa.x : ℝ)) ^ ((K:ℝ) - 2 * Pa.A') * M := by rw [hmain]
    _ ≤ (2:ℝ)^K * 1 * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle_one (pow_nonneg (by norm_num) K)) hM
    _ = (2:ℝ)^K * M := by ring

/-! ### The three power comparisons -/

/-- `N^{-1/27} ≤ X^{-1/3}` for `1 ≤ X ≤ N^{1/9}`. -/
lemma X_inv_third_ge (Pa : Work.FITop.Params) (X : ℕ) (hX1 : 1 ≤ X)
    (hX : (X : ℝ) ≤ Pa.N ^ ((1:ℝ)/9)) :
    Pa.N ^ (-(1:ℝ)/27) ≤ (X : ℝ) ^ (-(1:ℝ)/3) := by
  have hN1 : (1:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hNpos : 0 < Pa.N := lt_of_lt_of_le one_pos hN1
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
    linarith
  have hXpow : (X:ℝ) ^ ((1:ℝ)/3) ≤ Pa.N ^ ((1:ℝ)/27) := by
    have h1 : (X:ℝ) ^ ((1:ℝ)/3) ≤ (Pa.N ^ ((1:ℝ)/9)) ^ ((1:ℝ)/3) :=
      Real.rpow_le_rpow (le_of_lt hXpos) hX (by norm_num)
    have h2 : (Pa.N ^ ((1:ℝ)/9)) ^ ((1:ℝ)/3) = Pa.N ^ ((1:ℝ)/27) := by
      rw [← Real.rpow_mul (le_of_lt hNpos)]; norm_num
    linarith
  have h3 : (Pa.N ^ ((1:ℝ)/27))⁻¹ ≤ ((X:ℝ) ^ ((1:ℝ)/3))⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hXpos _)).mpr hXpow
  rw [← Real.rpow_neg (le_of_lt hNpos) (1/27), ← Real.rpow_neg (le_of_lt hXpos) (1/3)] at h3
  simpa [neg_div] using h3

/-- The first bracket term: `X^{-1/2}·N·N ≤ X^{-1/3}N²`. -/
lemma half_le (Pa : Work.FITop.Params) (X : ℕ) (hX1 : 1 ≤ X) :
    (X : ℝ) ^ (-(1:ℝ)/2) * Pa.N * Pa.N ≤ (X : ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2 := by
  have hX1' : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
  have hXpos : (0:ℝ) < (X:ℝ) := lt_of_lt_of_le one_pos hX1'
  have hmono : (X:ℝ) ^ (-(1:ℝ)/2) ≤ (X:ℝ) ^ (-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_le hX1' (by norm_num)
  have hN0 : 0 ≤ Pa.N := by linarith [Pa.hN1]
  have h2 : Pa.N * Pa.N = Pa.N ^ 2 := by ring
  calc (X : ℝ) ^ (-(1:ℝ)/2) * Pa.N * Pa.N
      = (X : ℝ) ^ (-(1:ℝ)/2) * (Pa.N * Pa.N) := by ring
    _ = (X : ℝ) ^ (-(1:ℝ)/2) * Pa.N ^ 2 := by rw [h2]
    _ ≤ (X : ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2 :=
        mul_le_mul_of_nonneg_right hmono (pow_nonneg hN0 2)

/-- The second bracket term: `N^{1/3}·X^{-1/3}·N^{2/3}·N = X^{-1/3}N²`. -/
lemma mid_le (Pa : Work.FITop.Params) (X : ℕ) (hX1 : 1 ≤ X) :
    Pa.N ^ ((1:ℝ)/3) * (X : ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) * Pa.N
      ≤ (X : ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2 := by
  have hN1 : (1:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hNpos : 0 < Pa.N := lt_of_lt_of_le one_pos hN1
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
    linarith
  have hcomb : Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) * Pa.N
      = (X:ℝ)^(-(1:ℝ)/3) * Pa.N ^ (2:ℕ) := by
    have h2 : Pa.N ^ ((1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) * Pa.N = Pa.N ^ (2:ℕ) := by
      rw [← Real.rpow_add hNpos, show (1:ℝ)/3 + 2/3 = 1 by norm_num, Real.rpow_one]
      ring
    calc Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) * Pa.N
        = (X:ℝ)^(-(1:ℝ)/3) * (Pa.N ^ ((1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) * Pa.N) := by ring
      _ = (X:ℝ)^(-(1:ℝ)/3) * Pa.N ^ (2:ℕ) := by rw [h2]
  exact le_of_eq hcomb

/-- The third bracket term: `N^{23/24+ε}·N ≤ X^{-1/3}N²` for `ε ≤ 1/216` (the endpoint
`23/24 + 1/216 + 1 = 2 - 1/27`). -/
lemma tail_le (Pa : Work.FITop.Params) (X : ℕ) (ε : ℝ) (hε : ε ≤ 1/216) (hX1 : 1 ≤ X)
    (hX : (X : ℝ) ≤ Pa.N ^ ((1:ℝ)/9)) :
    Pa.N ^ ((23:ℝ)/24 + ε) * Pa.N ≤ (X : ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2 := by
  have hN1 : (1:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hNpos : 0 < Pa.N := lt_of_lt_of_le one_pos hN1
  have hNinv := X_inv_third_ge Pa X hX1 hX
  have hstep1 : Pa.N ^ ((23:ℝ)/24 + ε) * Pa.N = Pa.N ^ ((47:ℝ)/24 + ε) := by
    have h : Pa.N ^ ((23:ℝ)/24 + ε) * Pa.N ^ (1:ℝ) = Pa.N ^ ((47:ℝ)/24 + ε) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    simpa [Real.rpow_one] using h
  have hstep2 : Pa.N ^ ((47:ℝ)/24 + ε) ≤ Pa.N ^ ((53:ℝ)/27) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hstep3 : Pa.N ^ ((53:ℝ)/27) = Pa.N ^ (-(1:ℝ)/27) * Pa.N ^ 2 := by
    rw [← Real.rpow_natCast Pa.N 2, ← Real.rpow_add hNpos]; norm_num
  have hstep4 : Pa.N ^ (-(1:ℝ)/27) * Pa.N ^ (2:ℕ) ≤ (X:ℝ)^(-(1:ℝ)/3) * Pa.N ^ (2:ℕ) :=
    mul_le_mul_of_nonneg_right hNinv (pow_nonneg (le_of_lt hNpos) 2)
  linarith

/-- The fourth bracket term: `N ≤ X^{-1/3}N²`. -/
lemma one_le_third (Pa : Work.FITop.Params) (X : ℕ) (hX1 : 1 ≤ X)
    (hX : (X : ℝ) ≤ Pa.N ^ ((1:ℝ)/9)) :
    Pa.N ≤ (X : ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2 := by
  have hN1 : (1:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hNpos : 0 < Pa.N := lt_of_lt_of_le one_pos hN1
  have hNinv := X_inv_third_ge Pa X hX1 hX
  have hhalf : Pa.N ≤ Pa.N ^ ((53:ℝ)/27) := by
    nth_rewrite 1 [← Real.rpow_one Pa.N]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h53 : Pa.N ^ ((53:ℝ)/27) = Pa.N ^ (-(1:ℝ)/27) * Pa.N ^ 2 := by
    rw [← Real.rpow_natCast Pa.N 2, ← Real.rpow_add hNpos]; norm_num
  have hmul : Pa.N ^ (-(1:ℝ)/27) * Pa.N ^ 2 ≤ (X:ℝ)^(-(1:ℝ)/3) * Pa.N ^ 2 :=
    mul_le_mul_of_nonneg_right hNinv (pow_nonneg (le_of_lt hNpos) 2)
  linarith

/-! ### The endgame -/

/-- **Endgame absorption.**  If `V` is bounded by the shape produced by the §15 chain,

`V ≤ C·θ²(log N + 1)^K·(X^{-1/2}N + N^{1/3}X^{-1/3}N^{2/3} + N^{23/24+ε} + 1)·N`,

with `K ≤ 2·2^20`, `ε ≤ 1/216`, `1 ≤ X ≤ N^{1/9}`, then `V ≤ 6C2^K(P^{-1} + X^{-1/3})N²`. -/
theorem endgame_absorb (Pa : Work.FITop.Params) (X : ℕ) (V C : ℝ) (K : ℕ) (ε : ℝ)
    (hK : (K : ℝ) ≤ 2 * (2:ℝ)^20) (hε : ε ≤ 1/216) (hX1 : 1 ≤ X)
    (hX : (X : ℝ) ≤ Pa.N ^ ((1:ℝ)/9)) (hC : 0 ≤ C)
    (hV : V ≤ C * (Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ K) *
        ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N)) :
    V ≤ (C * 2^K * 6) * ((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2 := by
  have hN1 : (1:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hNpos : 0 < Pa.N := lt_of_lt_of_le one_pos hN1
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
    linarith
  have hBnn : 0 ≤ (X:ℝ) ^ (-(1:ℝ)/3) := Real.rpow_nonneg (le_of_lt hXpos) _
  have hMnn : 0 ≤ ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N) := by
    have h1 : 0 ≤ (X:ℝ) ^ (-(1:ℝ)/2) * Pa.N :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hXpos) _) (le_of_lt hNpos)
    have h2 : 0 ≤ Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _) hBnn)
        (Real.rpow_nonneg (le_of_lt hNpos) _)
    have h3 : 0 ≤ Pa.N ^ ((23:ℝ)/24 + ε) := Real.rpow_nonneg (le_of_lt hNpos) _
    have h4 : 0 ≤ Pa.N := le_of_lt hNpos
    positivity
  have htheta := theta_sq_log_pow_le Pa K hK _ hMnn
  have hV2 : V ≤ C * ((2:ℝ)^K * ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N)) := by
    calc V ≤ C * (Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ K) *
          ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N) := hV
      _ = C * ((Pa.θ ^ 2 * (Real.log Pa.N + 1) ^ K) *
          ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N)) := by rw [mul_assoc]
      _ ≤ C * ((2:ℝ)^K *
          ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N)) :=
        mul_le_mul_of_nonneg_left htheta hC
  have t1 := half_le Pa X hX1
  have t2 := mid_le Pa X hX1
  have t3 := tail_le Pa X ε hε hX1 hX
  have t4 := one_le_third Pa X hX1 hX
  have hsum : ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N)
        ≤ 4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2) := by
    have e : (((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N
        = ((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N) * Pa.N
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3)) * Pa.N
          + Pa.N ^ ((23:ℝ)/24 + ε) * Pa.N + 1 * Pa.N := by ring
    rw [e]
    linarith
  have hfin : (2:ℝ)^K * ((((X:ℝ) ^ (-(1:ℝ)/2) * Pa.N)
          + (Pa.N ^ ((1:ℝ)/3) * (X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ ((2:ℝ)/3))
          + Pa.N ^ ((23:ℝ)/24 + ε) + 1) * Pa.N)
        ≤ (2:ℝ)^K * (4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) K)
  have goal2 : V ≤ C * ((2:ℝ)^K * (4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2))) :=
    le_trans hV2 (mul_le_mul_of_nonneg_left hfin hC)
  have hE : C * ((2:ℝ)^K * (4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2)))
      = C * (2:ℝ)^K * 4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2) := by ring
  have hG : (C * 2^K * 6) * ((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2
      = C * (2:ℝ)^K * 6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2) := by
    ring
  calc V ≤ C * ((2:ℝ)^K * (4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2))) := goal2
    _ = C * (2:ℝ)^K * 4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2) := hE
    _ ≤ C * (2:ℝ)^K * 6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2) := by
        have h2 : 4 * (X:ℝ) ^ (-(1:ℝ)/3)
            ≤ 6 * ((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) := by
          have h3 : 0 ≤ ((Pa.Pz : ℝ))⁻¹ := by positivity
          linarith
        have hb : 4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2)
            ≤ 6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2) := by
          calc 4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2)
              = (4 * (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2 := by ring
            _ ≤ (6 * ((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3))) * Pa.N ^ 2 :=
                mul_le_mul_of_nonneg_right h2 (pow_nonneg (le_of_lt hNpos) 2)
            _ = 6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2) := by ring
        have hC2 : 0 ≤ C * (2:ℝ)^K := mul_nonneg hC (pow_nonneg (by norm_num) K)
        have hmul : (C * (2:ℝ)^K) * (4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2))
            ≤ (C * (2:ℝ)^K) * (6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hC2
        calc C * (2:ℝ)^K * 4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2)
            = (C * (2:ℝ)^K) * (4 * ((X:ℝ) ^ (-(1:ℝ)/3) * Pa.N ^ 2)) := by ring
          _ ≤ (C * (2:ℝ)^K) * (6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2)) := hmul
          _ = C * (2:ℝ)^K * 6 * (((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2) := by ring
    _ = (C * 2^K * 6) * ((Pa.Pz : ℝ)⁻¹ + (X:ℝ) ^ (-(1:ℝ)/3)) * Pa.N ^ 2 := hG.symm

end Work.FIArea4
