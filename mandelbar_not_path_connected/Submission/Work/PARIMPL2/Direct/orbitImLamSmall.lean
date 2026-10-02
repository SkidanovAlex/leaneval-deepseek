/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# The height bound `λ·|Im uₙ| ≤ 1` along a model orbit

Let `a = iλ` (`λ > 0`), let `h` be the germ of the rotated normal form
`h ζ = τ + h₁ ζ + O(ζ²)` (`ParBounds`), and let `u : ℕ → ℂ` be a model orbit
`u_{j+1} = u_j + modelDisp a h u_j` which stays in the strip
`R/4 + 2 ≤ Re u_j ≤ π/λ − R/4`, whose real part decreases by at least `1/3` per step,
and whose chart points `ζ_j = ecalPt a u_j` satisfy `‖ζ_j‖ ≤ 4/R` and `‖ζ_j‖ < r`.

Then `λ·|Im u_n| ≤ 1`.

## The argument

Write `Φ_j = modelDisp a h u_j`, `ζ_j = ecalPt a u_j`, `x_j = Re u_j`, `y_j = Im u_j`,
`c = h₁ − τ²`.  The proved second-order decomposition
(`modelDisp_im_decomp`, `Direct.modelDispIm...`) gives, on the chart ball,

`Im Φ_j = −Im τ − Im (c ζ_j) + O(λ² + ‖ζ_j‖²)`,

and the componentwise bound `Direct.ecalPtAbsReImLe` turns `Im (c ζ_j)` into
`‖c‖·λ/sin(λx_j)` (using `λ|y_j| ≤ 1`, hence `cosh(λy_j) ≤ 2`, which is exactly the
induction hypothesis).  Summing over `j < m`:

`λ|y_m| ≤ λ|y_0| + λ(m|Im τ| + 2(B+1)·Σ λ/sin(λx_j) + 100λ²m + (2+4B+2A)·Σ‖ζ_j‖²)`.

The two sums are controlled by the *geometry of the strip*:

* `λ/sin(λx_j) ≤ 1/x_j + 1/(π/λ − x_j)` (`Direct.oneDivSinLe`), and since `x_j` decreases
  by `1/3` while `π/λ − x_j` increases by `1/3`, the elementary telescoping bounds
  `Direct.sumInvLeLog` / `Direct.sumInvSqLe` give
  `Σ_{j<n} λ/sin(λx_j) ≤ Csx + Csd` with `Csx`, `Csd` the logarithmic expressions below;
* `‖ζ_j‖² ≤ λ²(1/sin²(λx_j) + 1)` (`Direct.ecalPt_norm_sq_le`), so squaring the previous
  pointwise bound controls `Σ‖ζ_j‖²` by `2(Csx2 + Csd2) + nλ²`.

Finally `|Im τ| ≤ ‖τ−1‖ ≤ λ/(8πR)` (this is where the hypothesis `hτpi` is used) and
`λ(R/4 + 4 + log R)`, `λn·λ/(8πR)`, `100nλ³` are all `O(1/R)`, so the total drift is at
most `1` — the arithmetic is `arith_all` below.
-/
import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.ecalPt_im_eq
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_sq_eq
import Submission.Work.PARIMPL2.Direct.modelDisp_im_decomp
import Submission.Work.PARIMPL2.Direct.ecalPtAbsReImLe
import Submission.Work.PARIMPL2.Direct.sumInvLeLog
import Submission.Work.PARIMPL2.Direct.sumInvSqLe
import Submission.Work.PARIMPL2.Direct.oneDivSinLe

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000

namespace Work.PARIMPL2.Direct

open Complex

/-! ## Elementary auxiliary estimates -/

private lemma cosh_le_two {t : ℝ} (ht : |t| ≤ 1) : Real.cosh t ≤ 2 := by
  have h1 : Real.cosh t ≤ Real.cosh 1 := Real.cosh_le_cosh.mpr (by simpa using ht)
  have h2 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h4 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  linarith


/-- If `sin (λ Re u) > 0` then `u` is not a puncture of the Écalle point map. -/
private lemma ecalE_ne_one_of_sin_pos (lam : ℝ) (u : ℂ)
    (hsin : 0 < Real.sin (lam * u.re)) :
    Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1 := by
  intro h
  rw [Work.Implosion.ecalE] at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2 : 2 * ((lam : ℂ) * Complex.I) * u = Complex.I * (2 * ((lam : ℂ) * u)) := by ring
  rw [h2] at hn
  have h3 : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
      = Complex.I * ((n : ℂ) * (2 * (Real.pi : ℂ))) := by ring
  rw [h3] at hn
  have h4 : 2 * ((lam : ℂ) * u) = (n : ℂ) * (2 * (Real.pi : ℂ)) :=
    mul_left_cancel₀ Complex.I_ne_zero hn
  have h5 : (lam : ℂ) * u = (n : ℂ) * (Real.pi : ℂ) := by
    have h6 : (2:ℂ) * ((lam : ℂ) * u) = (2:ℂ) * ((n : ℂ) * (Real.pi : ℂ)) := by
      rw [h4]; ring
    exact mul_left_cancel₀ two_ne_zero h6
  have hre : lam * u.re = (n : ℝ) * Real.pi := by
    have := congrArg Complex.re h5
    simpa [Complex.mul_re] using this
  rw [hre, Real.sin_int_mul_pi] at hsin
  exact lt_irrefl 0 hsin

/-- Pointwise bound on the chart point: `‖ecalPt (iλ) u‖² ≤ λ²(1/sin²(λ Re u) + 1)`. -/
private lemma ecalPt_norm_sq_le (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (hsin : 0 < Real.sin (lam * u.re)) :
    ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
      ≤ lam ^ 2 * (1 / Real.sin (lam * u.re) ^ 2 + 1) := by
  have hE1 : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1 :=
    ecalE_ne_one_of_sin_pos lam u hsin
  rw [ecalPt_norm_sq_eq lam hlam u hE1]
  set s := Real.sin (lam * u.re) with hs
  set s2 := Real.sinh (lam * u.im) with hs2
  set c2 := Real.cos (lam * u.re) with hc2
  have hs0 : 0 < s := hsin
  have hc21 : c2 ^ 2 ≤ 1 := by
    have hcs := Real.cos_sq_add_sin_sq (lam * u.re)
    rw [← hc2, ← hs] at hcs
    nlinarith [sq_nonneg s, hcs]
  have hden : 0 < s ^ 2 + s2 ^ 2 := by nlinarith [hs0]
  have hkey : (c2 ^ 2 + s2 ^ 2) / (s ^ 2 + s2 ^ 2) ≤ 1 / s ^ 2 + 1 := by
    rw [div_le_iff₀ hden]
    have h2 : (1 / s ^ 2 + 1) * (s ^ 2 + s2 ^ 2) = 1 + s2^2/s^2 + s^2 + s2^2 := by
      field_simp
      try ring
    have h3 : 0 ≤ s2^2/s^2 := div_nonneg (sq_nonneg s2) (by positivity)
    nlinarith [hc21, h2, h3, sq_nonneg s, hs0]
  calc lam ^ 2 * ((c2 ^ 2 + s2 ^ 2) / (s ^ 2 + s2 ^ 2))
      ≤ lam ^ 2 * (1 / s ^ 2 + 1) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = lam ^ 2 * (1 / Real.sin (lam * u.re) ^ 2 + 1) := by rw [hs]


/-- `log w ≤ log R + w/R - 1` for `w, R > 0` (from `log x ≤ x - 1`). -/
private lemma log_le_log_add_div (w R : ℝ) (hw : 0 < w) (hR : 0 < R) :
    Real.log w ≤ Real.log R + w / R - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < w / R by positivity)
  rw [Real.log_div (ne_of_gt hw) (ne_of_gt hR)] at h
  linarith

/-- `log R ≤ R/128 + 4` for `R ≥ 128`. -/
private lemma log_le_div (R : ℝ) (hR : 128 ≤ R) : Real.log R ≤ R / 128 + 4 := by
  have h1 : 0 < R / 128 := by positivity
  have h2 : Real.log (R/128) ≤ R/128 - 1 := Real.log_le_sub_one_of_pos h1
  have h3 : Real.log R = Real.log 128 + Real.log (R/128) := by
    rw [← Real.log_mul (by norm_num : (128:ℝ) ≠ 0) (by positivity : R/128 ≠ 0)]
    congr 1; ring
  have h4 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  rw [h3, h4]; linarith

/-- `λ · log (1 + 4π/(λR)) ≤ 1/(4R)` for `0 < λ`, `λR² ≤ 1`, `R ≥ 128`. -/
private lemma lam_log_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) :
    lam * Real.log (1 + 4 * Real.pi / (lam * R)) ≤ 1 / (4 * R) := by
  have hRpos : 0 < R := by linarith
  have hlamRpos : 0 < lam * R := by positivity
  have hy : 1 ≤ 4 * Real.pi / (lam * R) := by
    rw [le_div_iff₀ hlamRpos]
    have h1 : lam * R ≤ 1 / R := by rw [le_div_iff₀ hRpos]; nlinarith [hlamR]
    have h2 : (1:ℝ)/R ≤ 1 := by rw [div_le_one hRpos]; linarith
    nlinarith [Real.pi_gt_three, h1, h2]
  have hy0 : 0 < 4 * Real.pi / (lam * R) := lt_of_lt_of_le one_pos hy
  have hlog1 : Real.log (1 + 4 * Real.pi / (lam * R))
      ≤ Real.log 2 + Real.log (4 * Real.pi / (lam * R)) := by
    have h : 1 + 4 * Real.pi / (lam * R) ≤ 2 * (4 * Real.pi / (lam * R)) := by linarith
    calc Real.log (1 + 4 * Real.pi / (lam * R))
        ≤ Real.log (2 * (4 * Real.pi / (lam * R))) := Real.log_le_log (by linarith) h
      _ = Real.log 2 + Real.log (4 * Real.pi / (lam * R)) :=
          Real.log_mul (by norm_num) (ne_of_gt hy0)
  have hlogy : Real.log (4 * Real.pi / (lam * R))
      = Real.log 2 + Real.log 2 + Real.log Real.pi - Real.log lam - Real.log R := by
    rw [Real.log_div (by positivity) (ne_of_gt hlamRpos),
      Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos),
      Real.log_mul (ne_of_gt hlam) (ne_of_gt hRpos),
      show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlogRle : Real.log R ≤ R / 128 + 4 := log_le_div R hR
  have hlog2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hlog2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogpi : Real.log Real.pi ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  have hlogpi' : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hloginv : lam * Real.log (1/lam) ≤ 2 * Real.log R / R ^ 2 + 1 / R ^ 2 := by
    have hw : 0 < 1/lam := by positivity
    have hR2 : 0 < R ^ 2 := by positivity
    have h : Real.log (1/lam) ≤ Real.log (R ^ 2) + (1/lam)/R ^ 2 - 1 := by
      have h0 := Real.log_le_sub_one_of_pos (show 0 < (1/lam)/R ^ 2 by positivity)
      rw [Real.log_div (by positivity) (ne_of_gt hR2)] at h0
      linarith
    have hlogR2 : Real.log (R ^ 2) = 2 * Real.log R := by rw [Real.log_pow]; push_cast; ring
    have hmul : lam * Real.log (1/lam)
        ≤ lam * (Real.log (R^2) + (1/lam)/R^2 - 1) := mul_le_mul_of_nonneg_left h hlam.le
    have hsimp : lam * (Real.log (R ^ 2) + (1/lam)/R ^ 2 - 1)
        = lam * Real.log (R^2) + 1/R^2 - lam := by field_simp
    have hb1 : lam * Real.log (R ^ 2) ≤ 2 * Real.log R / R ^ 2 := by
      rw [hlogR2]
      have h1 : lam * (2*Real.log R) ≤ (1/R^2)*(2*Real.log R) :=
        mul_le_mul_of_nonneg_right (by rw [le_div_iff₀ hR2]; linarith [hlamR]) (by linarith)
      have h2 : (1/R^2)*(2*Real.log R) = 2*Real.log R/R^2 := by ring
      linarith [h1, h2.le, h2.ge]
    linarith [hmul, hsimp.le, hsimp.ge, hb1]
  have hlogRinv : lam * Real.log (1/R) ≤ 0 := by
    have h1 : Real.log (1/R) = - Real.log R := by rw [one_div, Real.log_inv]
    rw [h1]
    have := mul_nonneg hlam.le hlogR0
    linarith
  have h9 : lam * (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi)
      ≤ (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi) / R ^ 2 := by
    have hc0 : 0 ≤ Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi := by linarith
    have hlamle : lam ≤ 1/R^2 := by rw [le_div_iff₀ (by positivity)]; linarith [hlamR]
    have h10 := mul_le_mul_of_nonneg_right hlamle hc0
    have h11 : (1/R^2) * (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi)
        = (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi) / R^2 := by ring
    linarith [h10, h11.le, h11.ge]
  have hfin : (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi) / R ^ 2
      + 2 * Real.log R / R ^ 2 + 1 / R ^ 2 ≤ 1 / (4 * R) := by
    have hnum : Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi ≤ 5.1 := by linarith
    have hR2 : (0:ℝ) < R ^ 2 := by positivity
    rw [← add_div, ← add_div]
    rw [div_le_iff₀ hR2]
    have e : (1 / (4 * R)) * R^2 = R/4 := by field_simp
    rw [e]
    nlinarith [hnum, hlogRle, hR]
  calc lam * Real.log (1 + 4 * Real.pi / (lam * R))
      ≤ lam * (Real.log 2 + Real.log (4 * Real.pi / (lam * R))) :=
        mul_le_mul_of_nonneg_left hlog1 hlam.le
    _ = lam * (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi
          - Real.log lam - Real.log R) := by rw [hlogy]; ring
    _ = lam * (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi)
        + lam * Real.log (1/lam) + lam * Real.log (1/R) := by
        rw [show Real.log (1/lam) = -Real.log lam by rw [one_div, Real.log_inv],
          show Real.log (1/R) = -Real.log R by rw [one_div, Real.log_inv]]
        ring
    _ ≤ (Real.log 2 + Real.log 2 + Real.log 2 + Real.log Real.pi) / R^2
        + (2 * Real.log R / R^2 + 1 / R^2) + 0 := by linarith [h9, hloginv, hlogRinv]
    _ ≤ 1 / (4 * R) := by linarith [hfin]

private lemma sum_inv_dec_le (x : ℕ → ℝ) (a s : ℝ) (n : ℕ) (ha : 0 < a) (hs : 0 < s)
    (hb : ∀ j ≤ n, a ≤ x j) (hdec : ∀ j < n, x (j + 1) ≤ x j - s) :
    (∑ j ∈ Finset.range n, 1 / x j) ≤ 1 / a + (1 / s) * Real.log ((a + (n : ℝ) * s) / a) := by
  have hback : ∀ k ≤ n, x n + (k : ℝ) * s ≤ x (n - k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
      have ih' := ih hkn
      have hlt : n - (k + 1) < n := by omega
      have hstep := hdec (n - (k + 1)) hlt
      have hidx : n - (k + 1) + 1 = n - k := by omega
      rw [hidx] at hstep
      have hc : ((k : ℝ) + 1) * s = (k : ℝ) * s + s := by ring
      have : x n + ((k : ℝ) * s + s) ≤ x (n - (k + 1)) := by linarith
      simpa [hc] using this
  have hlow : ∀ j ≤ n, a + ((n - j : ℕ) : ℝ) * s ≤ x j := by
    intro j hj
    have h1 := hback (n - j) (Nat.sub_le n j)
    have h2 : n - (n - j) = j := by omega
    rw [h2] at h1
    have h3 := hb n le_rfl
    linarith
  calc (∑ j ∈ Finset.range n, 1 / x j)
      ≤ ∑ j ∈ Finset.range n, 1 / (a + ((n - j : ℕ) : ℝ) * s) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < n := Finset.mem_range.mp hj
        have hge := hlow j (le_of_lt hj')
        have hx : 0 < x j := lt_of_lt_of_le (by positivity) hge
        have hden : 0 < a + ((n - j : ℕ) : ℝ) * s := by positivity
        rw [one_div, one_div, inv_le_inv₀ hx hden]
        exact hge
    _ = ∑ k ∈ Finset.range n, 1 / (a + ((k : ℝ) + 1) * s) := by
        have h := Finset.sum_range_reflect (fun m : ℕ => 1 / (a + ((n - m : ℕ) : ℝ) * s)) n
        rw [← h]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < n := Finset.mem_range.mp hj
        have hidx : n - (n - 1 - j) = j + 1 := by omega
        rw [hidx]; push_cast; ring
    _ ≤ ∑ k ∈ Finset.range n, 1 / (a + (k : ℝ) * s) := by
        apply Finset.sum_le_sum
        intro k hk
        have hle : a + (k : ℝ) * s ≤ a + ((k : ℝ) + 1) * s := by push_cast; nlinarith
        have h1 : 0 < a + (k : ℝ) * s := by positivity
        have h2 : 0 < a + ((k : ℝ) + 1) * s := by positivity
        rw [one_div, one_div, inv_le_inv₀ h2 h1]
        exact hle
    _ ≤ 1 / a + (1 / s) * Real.log ((a + (n : ℝ) * s) / a) := sumInvLeLog a s n ha hs

private lemma sum_inv_sq_dec_le (x : ℕ → ℝ) (a s : ℝ) (n : ℕ) (ha : 0 < a) (hs : 0 < s)
    (hb : ∀ j ≤ n, a ≤ x j) (hdec : ∀ j < n, x (j + 1) ≤ x j - s) :
    (∑ j ∈ Finset.range n, 1 / (x j) ^ 2) ≤ 1 / a ^ 2 + 1 / (s * a) := by
  have hback : ∀ k ≤ n, x n + (k : ℝ) * s ≤ x (n - k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
      have ih' := ih hkn
      have hlt : n - (k + 1) < n := by omega
      have hstep := hdec (n - (k + 1)) hlt
      have hidx : n - (k + 1) + 1 = n - k := by omega
      rw [hidx] at hstep
      have hc : ((k : ℝ) + 1) * s = (k : ℝ) * s + s := by ring
      have : x n + ((k : ℝ) * s + s) ≤ x (n - (k + 1)) := by linarith
      simpa [hc] using this
  have hlow : ∀ j ≤ n, a + ((n - j : ℕ) : ℝ) * s ≤ x j := by
    intro j hj
    have h1 := hback (n - j) (Nat.sub_le n j)
    have h2 : n - (n - j) = j := by omega
    rw [h2] at h1
    have h3 := hb n le_rfl
    linarith
  calc (∑ j ∈ Finset.range n, 1 / (x j) ^ 2)
      ≤ ∑ j ∈ Finset.range n, 1 / (a + ((n - j : ℕ) : ℝ) * s) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < n := Finset.mem_range.mp hj
        have hge := hlow j (le_of_lt hj')
        have hx : 0 < x j := lt_of_lt_of_le (by positivity) hge
        have hden : 0 < a + ((n - j : ℕ) : ℝ) * s := by positivity
        rw [one_div, one_div, inv_le_inv₀ (pow_pos hx 2) (pow_pos hden 2)]
        exact pow_le_pow_left₀ hden.le hge 2
    _ = ∑ k ∈ Finset.range n, 1 / (a + ((k : ℝ) + 1) * s) ^ 2 := by
        have h := Finset.sum_range_reflect (fun m : ℕ => 1 / (a + ((n - m : ℕ) : ℝ) * s) ^ 2) n
        rw [← h]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < n := Finset.mem_range.mp hj
        have hidx : n - (n - 1 - j) = j + 1 := by omega
        rw [hidx]; push_cast; ring
    _ ≤ ∑ k ∈ Finset.range n, 1 / (a + (k : ℝ) * s) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hle : a + (k : ℝ) * s ≤ a + ((k : ℝ) + 1) * s := by push_cast; nlinarith
        have h1 : 0 < a + (k : ℝ) * s := by positivity
        have h2 : 0 < a + ((k : ℝ) + 1) * s := by positivity
        rw [one_div, one_div, inv_le_inv₀ (pow_pos h2 2) (pow_pos h1 2)]
        exact pow_le_pow_left₀ h1.le hle 2
    _ ≤ 1 / a ^ 2 + 1 / (s * a) := sumInvSqLe a s n ha hs

private noncomputable def Csx (n : ℕ) (R : ℝ) : ℝ :=
  1 / (R / 4 + 2) + 3 * Real.log ((R / 4 + 2 + (n : ℝ) * (1 / 3)) / (R / 4 + 2))

private noncomputable def Csd (n : ℕ) (R : ℝ) : ℝ :=
  1 / (R / 4) + 3 * Real.log ((R / 4 + (n : ℝ) * (1 / 3)) / (R / 4))

private noncomputable def Csx2 (R : ℝ) : ℝ := 1 / (R / 4 + 2) ^ 2 + 1 / ((1 / 3) * (R / 4 + 2))

private noncomputable def Csd2 (R : ℝ) : ℝ := 1 / (R / 4) ^ 2 + 1 / ((1 / 3) * (R / 4))


private lemma arith_all (lam R A B : ℝ) (n : ℕ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hn : (n : ℝ) * lam ≤ 3 * Real.pi) :
    lam * (R / 4 + 4 + Real.log R) + lam * ((n : ℝ) * (lam / (8 * Real.pi * R)))
      + 2 * (B + 1) * (8 / R ^ 3 + 3 / (2 * R))
      + 100 * (n : ℝ) * lam ^ 3
      + (2 + 4 * B + 2 * A) * (48.5 * lam / R + (n : ℝ) * lam ^ 3) ≤ 1 := by
  have hRpos : 0 < R := by linarith
  have hR2 : (0:ℝ) < R^2 := by positivity
  have hR3 : (0:ℝ) < R^3 := by positivity
  have hR4 : (0:ℝ) < R^4 := by positivity
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hlamle : lam ≤ 1/R^2 := by rw [le_div_iff₀ hR2]; linarith [hlamR]
  have hBR : B ≤ 3*R/32 := by
    have h1 : 4*B/R ≤ 3/8 := by
      have h2 : (0:ℝ) ≤ 16*A/R^2 := by positivity
      linarith [hAr]
    rw [div_le_iff₀ hRpos] at h1
    nlinarith
  have hAR : A ≤ 3*R^2/128 := by
    have h1 : 16*A/R^2 ≤ 3/8 := by
      have h2 : (0:ℝ) ≤ 4*B/R := by positivity
      linarith [hAr]
    rw [div_le_iff₀ hR2] at h1
    nlinarith
  have hU : lam * (R/4 + 4 + Real.log R) ≤ 1/10 := by
    have hlog := log_le_div R hR
    have h1 : lam * (R/4 + 4 + Real.log R) ≤ (1/R^2) * (R/4 + 4 + Real.log R) :=
      mul_le_mul_of_nonneg_right hlamle (by linarith)
    have h2 : (1/R^2) * (R/4 + 4 + Real.log R) ≤ (1/R^2) * (R/4 + 4 + (R/128 + 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h3 : (1/R^2) * (R/4 + 4 + (R/128 + 4)) ≤ 1/10 := by
      rw [show (1/R^2) * (R/4 + 4 + (R/128 + 4)) = (R/4 + 4 + (R/128 + 4))/R^2 by ring]
      rw [div_le_iff₀ hR2]
      nlinarith [hR]
    linarith
  have hV : lam * ((n:ℝ) * (lam/(8*Real.pi*R))) ≤ 1/100 := by
    have h1 : lam * ((n:ℝ) * (lam/(8*Real.pi*R))) = ((n:ℝ)*lam) * (lam/(8*Real.pi*R)) := by ring
    rw [h1]
    have h2 : ((n:ℝ)*lam) * (lam/(8*Real.pi*R)) ≤ (3*Real.pi) * (lam/(8*Real.pi*R)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    have h3 : (3*Real.pi) * (lam/(8*Real.pi*R)) = 3*lam/(8*R) := by field_simp
    rw [h3] at h2
    have h4 : 3*lam/(8*R) ≤ 3/(8*R^3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlamle, hRpos, sq_nonneg (R-1)]
    have h5 : 3/(8*R^3) ≤ 1/100 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*R^3)]
      nlinarith [hR]
    linarith
  have hX : 100 * (n:ℝ) * lam^3 ≤ 1/100 := by
    have h2 : 100 * ((n:ℝ)*lam) * lam^2 ≤ 100 * (3*Real.pi) * lam^2 := by
      have hh := mul_le_mul_of_nonneg_right hn (by positivity : (0:ℝ) ≤ lam^2)
      linarith
    have h4 : lam^2 ≤ (1/R^2)^2 := pow_le_pow_left₀ hlam.le hlamle 2
    have h3 : 100 * (3*Real.pi) * lam^2 ≤ 100*3*Real.pi*(1/R^2)^2 := by
      have h4' := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 100*(3*Real.pi))
      linarith [h4']
    have h5 : 100*3*Real.pi*(1/R^2)^2 ≤ 1/100 := by
      have e : (1/R^2)^2 = 1/R^4 := by field_simp
      rw [e, show 100*3*Real.pi*(1/R^4) = 300*Real.pi/R^4 by ring]
      rw [div_le_iff₀ hR4]
      nlinarith [Real.pi_lt_four, hR]
    have h1 : 100*(n:ℝ)*lam^3 = 100 * ((n:ℝ)*lam) * lam^2 := by ring
    linarith [h1.le, h1.ge, h2, h3, h5]
  have hW : 2*(B+1)*(8/R^3 + 3/(2*R)) ≤ 1/2 := by
    have h3 : B+1 ≤ 3*R/32 + 1 := by linarith
    have h1 : 2*(B+1)*(8/R^3 + 3/(2*R)) ≤ 2*(3*R/32+1)*(8/R^3+3/(2*R)) := by
      have h2 : (0:ℝ) ≤ 2*(8/R^3 + 3/(2*R)) := by positivity
      nlinarith [h3, h2]
    have h4 : 2*(3*R/32+1)*(8/R^3+3/(2*R)) = 9/32 + 3/R + 3/(2*R^2) + 16/R^3 := by
      field_simp
      try ring
    rw [h4] at h1
    have h5 : (9:ℝ)/32 + 3/R + 3/(2*R^2) + 16/R^3 ≤ 1/2 := by
      have e : (1/2 - ((9:ℝ)/32 + 3/R + 3/(2*R^2) + 16/R^3)) * R^3
          = R^3/2 - (9*R^3/32 + 3*R^2 + 3*R/2 + 16) := by
        field_simp
        try ring
      have hnn : 0 ≤ (1/2 - ((9:ℝ)/32 + 3/R + 3/(2*R^2) + 16/R^3)) * R^3 := by
        rw [e]; nlinarith [hR]
      have h2 := (mul_nonneg_iff_of_pos_right hR3).mp hnn
      linarith
    linarith [h1, h5]
  have hY : (2+4*B+2*A)*(48.5*lam/R + (n:ℝ)*lam^3) ≤ 1/10 := by
    have h1 : 48.5*lam/R ≤ 48.5/R^3 := by
      rw [div_le_div_iff₀ (by positivity) hR3]
      nlinarith [hlamle, hRpos]
    have h5 : (n:ℝ)*lam^3 ≤ 3*Real.pi/R^4 := by
      have h6 : (n:ℝ)*lam^3 = ((n:ℝ)*lam)*lam^2 := by ring
      rw [h6]
      have h7 : ((n:ℝ)*lam)*lam^2 ≤ (3*Real.pi)*lam^2 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      have h8 : lam^2 ≤ 1/R^4 := by
        have h9 : (1/R^2)^2 = 1/R^4 := by field_simp
        calc lam^2 ≤ (1/R^2)^2 := pow_le_pow_left₀ hlam.le hlamle 2
          _ = 1/R^4 := h9
      have h10 : (0:ℝ) ≤ 3*Real.pi := by positivity
      calc ((n:ℝ)*lam)*lam^2 ≤ (3*Real.pi)*lam^2 := h7
        _ ≤ (3*Real.pi)*(1/R^4) := mul_le_mul_of_nonneg_left h8 h10
        _ = 3*Real.pi/R^4 := by ring
    have h11 : (2+4*B+2*A) ≤ 3*R^2/64 + 3*R/8 + 2 := by nlinarith [hBR, hAR]
    have h13 : 48.5*lam/R + (n:ℝ)*lam^3 ≤ 48.5/R^3 + 3*Real.pi/R^4 := by linarith
    have h14 : (3*R^2/64 + 3*R/8 + 2)*(48.5/R^3 + 3*Real.pi/R^4) ≤ 1/10 := by
      have hA' : 3*R^2/64 + 3*R/8 + 2 ≤ (3*R^2/64) * (9/8) := by nlinarith [hR]
      have hB' : 48.5/R^3 + 3*Real.pi/R^4 ≤ 48.6/R^3 := by
        have hb1 : 3*Real.pi/R^4 ≤ (1/10)/R^3 := by
          rw [div_le_div_iff₀ (by positivity) hR3]
          nlinarith [Real.pi_lt_four, hR]
        have hb2 : 48.5/R^3 + (1/10)/R^3 = 48.6/R^3 := by ring
        linarith
      have hprod : (3*R^2/64 + 3*R/8 + 2)*(48.5/R^3 + 3*Real.pi/R^4)
          ≤ ((3*R^2/64)*(9/8))*(48.6/R^3) :=
        mul_le_mul hA' hB' (by positivity) (by positivity)
      have hfin : ((3*R^2/64)*(9/8))*(48.6/R^3) ≤ 1/10 := by
        rw [show ((3*R^2/64)*(9/8))*(48.6/R^3) = 1312.2/(512*R) by field_simp; ring]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 512*R)]
        nlinarith [hR]
      linarith [hprod, hfin]
    have h12 : (0:ℝ) ≤ 48.5*lam/R + (n:ℝ)*lam^3 := by positivity
    calc (2+4*B+2*A)*(48.5*lam/R + (n:ℝ)*lam^3)
        ≤ (3*R^2/64 + 3*R/8 + 2)*(48.5*lam/R + (n:ℝ)*lam^3) :=
          mul_le_mul_of_nonneg_right h11 h12
      _ ≤ (3*R^2/64 + 3*R/8 + 2)*(48.5/R^3 + 3*Real.pi/R^4) :=
          mul_le_mul_of_nonneg_left h13 (by positivity)
      _ ≤ 1/10 := h14
  linarith [hU, hV, hW, hX, hY]


private lemma modelDisp_im_le_core (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (u : ℂ) (hx1 : R / 4 + 2 ≤ u.re) (hx2 : u.re ≤ Real.pi / lam - R / 4)
    (hz : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r)
    (hy : lam * |u.im| ≤ 1) :
    |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).im|
      ≤ |τ.im| + 2 * (B + 1) * (lam / Real.sin (lam * u.re))
        + 100 * lam ^ 2
        + (2 + 4 * B + 2 * A) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 := by
  have hdecomp := modelDisp_im_decomp lam R hlam hR hlamR h τ h1 A r hA hr hb hτ1 u hz hzr
  set ζ : ℂ := Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u with hζ
  set Φ : ℂ := Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u with hΦ
  set c : ℂ := h1 - τ ^ 2 with hc
  have herr : ‖Φ + (τ + c * ζ)‖ ≤ 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ‖ ^ 2 := by
    have h2 : 2 + 4 * ‖h1‖ + 2 * A ≤ 2 + 4 * B + 2 * A := by linarith [hh1]
    have h3 := mul_le_mul_of_nonneg_right h2 (pow_nonneg (norm_nonneg ζ) 2)
    linarith [hdecomp, h3]
  have hsin : 0 < Real.sin (lam * u.re) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [hlam, hx1]
    · have h2 := mul_le_mul_of_nonneg_left hx2 hlam.le
      have h3 : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
      rw [h3] at h2
      have h4 : 0 < lam * R / 4 := by positivity
      linarith
  have hcosh : Real.cosh (lam * u.im) ≤ 2 := by
    apply cosh_le_two
    rw [abs_mul, abs_of_pos hlam]
    exact hy
  have habs : |ζ.re| ≤ lam / Real.sin (lam * u.re) ∧ |ζ.im| ≤ lam / Real.sin (lam * u.re) := by
    have h := ecalPtAbsReImLe lam hlam u hsin hcosh
    rwa [← hζ] at h
  have hτn : ‖τ‖ = 1 := hb.2.1
  have hcn : ‖c‖ ≤ B + 1 := by
    have h2 : ‖h1 - τ ^ 2‖ ≤ ‖h1‖ + ‖τ ^ 2‖ := norm_sub_le _ _
    rw [norm_pow, hτn] at h2
    simp only [one_pow, norm_one] at h2
    rw [hc]; linarith
  have hΦim : |Φ.im| ≤ ‖Φ + (τ + c * ζ)‖ + |(τ + c * ζ).im| := by
    have h2 : Φ.im = (Φ + (τ + c * ζ)).im - (τ + c * ζ).im := by
      rw [Complex.add_im]; ring
    have hA : |(Φ + (τ + c * ζ)).im - (τ + c * ζ).im|
        ≤ |(Φ + (τ + c * ζ)).im| + |(τ + c * ζ).im| := by
      have h7 := abs_sub_le (Φ + (τ + c * ζ)).im 0 (τ + c * ζ).im
      simpa only [sub_zero, zero_sub, abs_neg] using h7
    have hB : |(Φ + (τ + c * ζ)).im| ≤ ‖Φ + (τ + c * ζ)‖ :=
      Complex.abs_im_le_norm (Φ + (τ + c * ζ))
    rw [h2]
    linarith
  have hτcim : |(τ + c * ζ).im| ≤ |τ.im| + ‖c‖ * (|ζ.im| + |ζ.re|) := by
    rw [Complex.add_im, Complex.mul_im]
    have h3 := abs_add_le τ.im (c.re * ζ.im + c.im * ζ.re)
    have h4 : |c.re * ζ.im + c.im * ζ.re| ≤ |c.re| * |ζ.im| + |c.im| * |ζ.re| := by
      have h5 := abs_add_le (c.re * ζ.im) (c.im * ζ.re)
      rwa [abs_mul, abs_mul] at h5
    have h6 : |c.re| ≤ ‖c‖ := Complex.abs_re_le_norm c
    have h7 : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
    have h8 : |c.re| * |ζ.im| ≤ ‖c‖ * |ζ.im| :=
      mul_le_mul_of_nonneg_right h6 (abs_nonneg ζ.im)
    have h9 : |c.im| * |ζ.re| ≤ ‖c‖ * |ζ.re| :=
      mul_le_mul_of_nonneg_right h7 (abs_nonneg ζ.re)
    linarith
  have hfin : ‖c‖ * (|ζ.im| + |ζ.re|) ≤ (B + 1) * (2 * (lam / Real.sin (lam * u.re))) := by
    have h6 : |ζ.im| + |ζ.re| ≤ 2 * (lam / Real.sin (lam * u.re)) := by linarith [habs.1, habs.2]
    have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
    exact mul_le_mul hcn h6 (by positivity) (by linarith)
  have h4 : (2 + 4 * B + 2 * A) * ‖ζ‖ ^ 2
      = (2 + 4 * B + 2 * A) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 := by rw [hζ]
  linarith [hΦim, herr, hτcim, hfin, h4.le, h4.ge]


/-! ## The target -/

/-- Imaginary parts commute with finite sums. -/
private lemma sum_im_eq (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ s, f j).im = ∑ j ∈ s, (f j).im := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_im, ih]

theorem orbitImLamSmall (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R))
    (n : ℕ) (u : ℕ → ℂ)
    (hu : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j))
    (htop : Real.pi / lam - 2 * R ≤ (u 0).re)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hzn : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ≤ 4 / R)
    (hzr : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ < r)
    (hy0 : |(u 0).im| ≤ R / 4 + 4 + Real.log R) :
    lam * |(u n).im| ≤ 1 := by
  have hRpos : 0 < R := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
  set Φ : ℕ → ℂ := fun j => Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j) with hΦdef
  set ζ : ℕ → ℂ := fun j => Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j) with hζdef
  -- ### the iterate identity
  have hiter : ∀ m ≤ n, u m = u 0 + ∑ j ∈ Finset.range m, Φ j := by
    intro m hm
    induction m with
    | zero => simp
    | succ k ih =>
      have hk : k ≤ n := le_trans (Nat.le_succ k) hm
      have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hm
      rw [Finset.sum_range_succ, ← add_assoc, ← ih hk]
      congr 1
      exact hu k hkn
  -- ### the sine at each real part is positive
  have hsinpos : ∀ j ≤ n, 0 < Real.sin (lam * (u j).re) := by
    intro j hj
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h1 := hx1 j hj
      nlinarith [hlam]
    · have h2 := mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
      have h3 : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
      rw [h3] at h2
      have h4 : 0 < lam * R / 4 := by positivity
      linarith
  -- ### the upper end of the strip moves up by `1/3` per step
  have hdlow : ∀ j ≤ n, R / 4 + (j : ℝ) * (1 / 3) ≤ Real.pi / lam - (u j).re := by
    intro j hj
    induction j with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; linarith [hx2 0 (Nat.zero_le n)]
    | succ k ih =>
      have hk : k ≤ n := le_trans (Nat.le_succ k) hj
      have ih' := ih hk
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hj
      have hd := hdec k hklt
      have hgoal : R / 4 + ((k : ℝ) + 1) * (1 / 3) ≤ Real.pi / lam - (u (k + 1)).re := by
        have h2 : ((k : ℝ) + 1) * (1 / 3) = (k : ℝ) * (1 / 3) + 1 / 3 := by ring
        rw [h2]; linarith
      simpa [Nat.cast_add, Nat.cast_one] using hgoal
  -- ### the pointwise sine estimate
  have hpt : ∀ j < n, lam / Real.sin (lam * (u j).re)
      ≤ 1 / (u j).re + 1 / (Real.pi / lam - (u j).re) := by
    intro j hj
    have ht1 : 0 < lam * (u j).re := by
      have h1 := hx1 j (le_of_lt hj); nlinarith [hlam]
    have ht2 : lam * (u j).re < Real.pi := by
      have h2 := mul_le_mul_of_nonneg_left (hx2 j (le_of_lt hj)) hlam.le
      have h3 : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
      rw [h3] at h2
      have h4 : 0 < lam * R / 4 := by positivity
      linarith
    have hsin := oneDivSinLe (lam * (u j).re) ht1 ht2
    have hmul := mul_le_mul_of_nonneg_left hsin hlam.le
    have e1 : lam * (1 / Real.sin (lam * (u j).re)) = lam / Real.sin (lam * (u j).re) := by ring
    have e2 : lam * (1 / (lam * (u j).re) + 1 / (Real.pi - lam * (u j).re))
        = 1 / (u j).re + 1 / (Real.pi / lam - (u j).re) := by
      have hx0 : (u j).re ≠ 0 := by
        have h1 := hx1 j (le_of_lt hj)
        exact ne_of_gt (by linarith)
      have hpl : Real.pi - lam * (u j).re ≠ 0 := by linarith
      field_simp
      try ring
    rwa [e1, e2] at hmul
  -- ### the two sums
  have hsum1 : (∑ j ∈ Finset.range n, lam / Real.sin (lam * (u j).re))
      ≤ Csx n R + Csd n R := by
    have hstep : (∑ j ∈ Finset.range n, lam / Real.sin (lam * (u j).re))
        ≤ ∑ j ∈ Finset.range n, (1 / (u j).re + 1 / (Real.pi / lam - (u j).re)) :=
      Finset.sum_le_sum (fun j hj => hpt j (Finset.mem_range.mp hj))
    have hsplit : (∑ j ∈ Finset.range n, (1 / (u j).re + 1 / (Real.pi / lam - (u j).re)))
        = (∑ j ∈ Finset.range n, 1 / (u j).re)
          + (∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re)) :=
      Finset.sum_add_distrib
    have h1 : (∑ j ∈ Finset.range n, 1 / (u j).re) ≤ Csx n R := by
      have h := sum_inv_dec_le (fun j => (u j).re) (R / 4 + 2) (1 / 3) n (by linarith)
        (by norm_num) (fun j hj => hx1 j hj) (fun j hj => hdec j hj)
      have e : 1 / (R / 4 + 2) + (1 / (1 / 3)) * Real.log (((R / 4 + 2) + (n : ℝ) * (1 / 3)) / (R / 4 + 2))
          = Csx n R := by rw [Csx]; norm_num
      rwa [← e]
    have h2 : (∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re)) ≤ Csd n R := by
      have hstep2 : (∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re))
          ≤ ∑ j ∈ Finset.range n, 1 / (R / 4 + (j : ℝ) * (1 / 3)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < n := Finset.mem_range.mp hj
        have hge := hdlow j (le_of_lt hj')
        have hden : 0 < R / 4 + (j : ℝ) * (1 / 3) := by positivity
        have hval : 0 < Real.pi / lam - (u j).re := lt_of_lt_of_le hden hge
        rw [one_div, one_div, inv_le_inv₀ hval hden]
        exact hge
      have h := sumInvLeLog (R / 4) (1 / 3) n (by linarith) (by norm_num)
      have e : 1 / (R / 4) + (1 / (1 / 3)) * Real.log (((R / 4) + (n : ℝ) * (1 / 3)) / (R / 4))
          = Csd n R := by rw [Csd]; norm_num
      calc (∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re))
          ≤ ∑ j ∈ Finset.range n, 1 / (R / 4 + (j : ℝ) * (1 / 3)) := hstep2
        _ ≤ 1 / (R / 4) + (1 / (1 / 3)) * Real.log (((R / 4) + (n : ℝ) * (1 / 3)) / (R / 4)) := h
        _ = Csd n R := e
    linarith [hstep, hsplit.le, hsplit.ge, h1, h2]
  have hsum2 : (∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2)
      ≤ 2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2 := by
    have hptn : ∀ j < n, ‖ζ j‖ ^ 2 ≤ lam ^ 2 * (1 / Real.sin (lam * (u j).re) ^ 2 + 1) := by
      intro j hj
      have h := ecalPt_norm_sq_le lam hlam (u j) (hsinpos j (le_of_lt hj))
      simpa [hζdef] using h
    have hptn3 : ∀ j < n, lam ^ 2 * (1 / Real.sin (lam * (u j).re) ^ 2 + 1)
        ≤ 2 * ((1 / (u j).re) ^ 2 + (1 / (Real.pi / lam - (u j).re)) ^ 2) + lam ^ 2 := by
      intro j hj
      have heq : lam ^ 2 * (1 / Real.sin (lam * (u j).re) ^ 2 + 1)
          = lam ^ 2 / Real.sin (lam * (u j).re) ^ 2 + lam ^ 2 := by ring
      rw [heq]
      have h1 := hpt j hj
      have h2 : (lam / Real.sin (lam * (u j).re)) ^ 2
          ≤ (1 / (u j).re + 1 / (Real.pi / lam - (u j).re)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt (div_pos hlam (hsinpos j (le_of_lt hj)))) h1 2
      have e : (lam / Real.sin (lam * (u j).re)) ^ 2
          = lam ^ 2 / Real.sin (lam * (u j).re) ^ 2 := by rw [div_pow]
      have h4 : (1 / (u j).re + 1 / (Real.pi / lam - (u j).re)) ^ 2
          ≤ 2 * ((1 / (u j).re) ^ 2 + (1 / (Real.pi / lam - (u j).re)) ^ 2) := by
        nlinarith [sq_nonneg (1 / (u j).re - 1 / (Real.pi / lam - (u j).re))]
      linarith [h2, e.le, e.ge, h4]
    have hsum3 : (∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2)
        ≤ ∑ j ∈ Finset.range n,
            (2 * ((1 / (u j).re) ^ 2 + (1 / (Real.pi / lam - (u j).re)) ^ 2) + lam ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact le_trans (hptn j (Finset.mem_range.mp hj)) (hptn3 j (Finset.mem_range.mp hj))
    have hsq1 : (∑ j ∈ Finset.range n, (1 / (u j).re) ^ 2) ≤ Csx2 R := by
      have h := sum_inv_sq_dec_le (fun j => (u j).re) (R / 4 + 2) (1 / 3) n (by linarith)
        (by norm_num) (fun j hj => hx1 j hj) (fun j hj => hdec j hj)
      have e : (∑ j ∈ Finset.range n, (1 / (u j).re) ^ 2)
          = ∑ j ∈ Finset.range n, 1 / ((u j).re) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_pow]; norm_num
      rw [e, Csx2]
      exact h
    have hsq2 : (∑ j ∈ Finset.range n, (1 / (Real.pi / lam - (u j).re)) ^ 2) ≤ Csd2 R := by
      have hstep2 : (∑ j ∈ Finset.range n, (1 / (Real.pi / lam - (u j).re)) ^ 2)
          ≤ ∑ j ∈ Finset.range n, (1 / (R / 4 + (j : ℝ) * (1 / 3))) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < n := Finset.mem_range.mp hj
        have hge := hdlow j (le_of_lt hj')
        have hden : 0 < R / 4 + (j : ℝ) * (1 / 3) := by positivity
        have hval : 0 < Real.pi / lam - (u j).re := lt_of_lt_of_le hden hge
        have h1 : 1 / (Real.pi / lam - (u j).re) ≤ 1 / (R / 4 + (j : ℝ) * (1 / 3)) :=
          one_div_le_one_div_of_le hden hge
        exact pow_le_pow_left₀ (by positivity) h1 2
      have h := sumInvSqLe (R / 4) (1 / 3) n (by linarith) (by norm_num)
      have h' : (∑ j ∈ Finset.range n, (1 / (R / 4 + (j : ℝ) * (1 / 3))) ^ 2)
          ≤ 1 / (R / 4) ^ 2 + 1 / ((1 / 3) * (R / 4)) := by
        have e : (∑ j ∈ Finset.range n, (1 / (R / 4 + (j : ℝ) * (1 / 3))) ^ 2)
            = ∑ j ∈ Finset.range n, 1 / (R / 4 + (j : ℝ) * (1 / 3)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_pow]; norm_num
        rw [e]; exact h
      have e2 : 1 / (R / 4) ^ 2 + 1 / ((1 / 3) * (R / 4)) = Csd2 R := by rw [Csd2]
      linarith [hstep2, h', e2.le, e2.ge]
    have hsplit : (∑ j ∈ Finset.range n,
          (2 * ((1 / (u j).re) ^ 2 + (1 / (Real.pi / lam - (u j).re)) ^ 2) + lam ^ 2))
        = 2 * ((∑ j ∈ Finset.range n, (1 / (u j).re) ^ 2)
            + (∑ j ∈ Finset.range n, (1 / (Real.pi / lam - (u j).re)) ^ 2))
          + (n : ℝ) * lam ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
    rw [hsplit] at hsum3
    linarith [hsum3, hsq1, hsq2]
  -- ### numerical facts
  have hnlam : (n : ℝ) * lam ≤ 3 * Real.pi := by
    have h2 : (u 0).re ≤ Real.pi / lam - R / 4 := hx2 0 (Nat.zero_le n)
    have h3 : R / 4 + 2 ≤ (u n).re := hx1 n le_rfl
    have h4 : (n : ℝ) * (1 / 3) ≤ Real.pi / lam - R / 2 - 2 := by
      have h5 : ∀ k ≤ n, (u k).re + (k : ℝ) * (1 / 3) ≤ (u 0).re := by
        intro k hk
        induction k with
        | zero => simp
        | succ j ihj =>
          have hj : j ≤ n := le_trans (Nat.le_succ j) hk
          have ihj' := ihj hj
          have hjlt : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hk
          have hd := hdec j hjlt
          have hgoal : (u (j + 1)).re + ((j : ℝ) + 1) * (1 / 3) ≤ (u 0).re := by
            have h6 : ((j : ℝ) + 1) * (1 / 3) = (j : ℝ) * (1 / 3) + 1 / 3 := by ring
            rw [h6]; linarith
          simpa [Nat.cast_add, Nat.cast_one] using hgoal
      have h6 := h5 n le_rfl
      linarith
    have h7 : (n : ℝ) * (1 / 3) * lam ≤ (Real.pi / lam - R / 2 - 2) * lam :=
      mul_le_mul_of_nonneg_right h4 hlam.le
    have h8 : (Real.pi / lam - R / 2 - 2) * lam = Real.pi - lam * R / 2 - 2 * lam := by
      field_simp
      try ring
    rw [h8] at h7
    have h9 : (0:ℝ) ≤ lam * R / 2 + 2 * lam := by positivity
    nlinarith [h7, h9]
  have himtau : ‖τ - 1‖ ≤ lam / (8 * Real.pi * R) := by
    have h1 : (lam / Real.pi) * ((Real.pi / lam) * ‖τ - 1‖) = ‖τ - 1‖ := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hτpi (by positivity : (0:ℝ) ≤ lam / Real.pi)
    have h3 : (lam / Real.pi) * (1 / (8 * R)) = lam / (8 * Real.pi * R) := by
      field_simp
      try ring
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  have himtau2 : |τ.im| ≤ lam / (8 * Real.pi * R) := by
    have h2 : |τ.im| ≤ ‖τ - 1‖ := by
      have h3 := Complex.abs_im_le_norm (τ - 1)
      rwa [Complex.sub_im, Complex.one_im, sub_zero] at h3
    linarith [h2, himtau]
  -- ### the induction
  have hmain : ∀ m ≤ n, lam * |(u m).im| ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      have hIH : ∀ j < m, lam * |(u j).im| ≤ 1 := fun j hj => ih j hj (le_trans (le_of_lt hj) hm)
      have hstep : ∀ j < m, |(Φ j).im| ≤ |τ.im| + 2 * (B + 1) * (lam / Real.sin (lam * (u j).re))
          + 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 := by
        intro j hj
        have hjn : j < n := lt_of_lt_of_le hj hm
        exact modelDisp_im_le_core lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 (u j)
          (hx1 j (le_of_lt hjn)) (hx2 j (le_of_lt hjn))
          (by simpa [hζdef] using hzn j (le_of_lt hjn))
          (by simpa [hζdef] using hzr j (le_of_lt hjn))
          (hIH j hj)
      have hsub1 : (∑ j ∈ Finset.range m, lam / Real.sin (lam * (u j).re)) ≤ Csx n R + Csd n R := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hm) ?_) hsum1
        intro i hi _
        exact le_of_lt (div_pos hlam (hsinpos i (le_of_lt (Finset.mem_range.mp hi))))
      have hsub2 : (∑ j ∈ Finset.range m, ‖ζ j‖ ^ 2) ≤ 2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2 := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hm) ?_) hsum2
        intro i hi _
        positivity
      have hsumper : (∑ j ∈ Finset.range m, |(Φ j).im|)
          ≤ (m : ℝ) * |τ.im| + 2 * (B + 1) * (Csx n R + Csd n R)
            + 100 * lam ^ 2 * (m : ℝ)
            + (2 + 4 * B + 2 * A) * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2) := by
        have h1 : (∑ j ∈ Finset.range m, |(Φ j).im|)
            ≤ ∑ j ∈ Finset.range m, (|τ.im| + 2 * (B + 1) * (lam / Real.sin (lam * (u j).re))
              + 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) :=
          Finset.sum_le_sum (fun j hj => hstep j (Finset.mem_range.mp hj))
        have hsplit : (∑ j ∈ Finset.range m, (|τ.im| + 2 * (B + 1) * (lam / Real.sin (lam * (u j).re))
              + 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2))
            = (m : ℝ) * |τ.im| + 2 * (B + 1) * (∑ j ∈ Finset.range m, lam / Real.sin (lam * (u j).re))
              + 100 * lam ^ 2 * (m : ℝ)
              + (2 + 4 * B + 2 * A) * (∑ j ∈ Finset.range m, ‖ζ j‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
        rw [hsplit] at h1
        have hB1 : (0:ℝ) ≤ 2 * (B + 1) := by linarith
        have hK : (0:ℝ) ≤ 2 + 4 * B + 2 * A := by linarith
        have h4 := mul_le_mul_of_nonneg_left hsub1 hB1
        have h5 := mul_le_mul_of_nonneg_left hsub2 hK
        linarith [h1, h4, h5]
      -- the height drift
      have h1 : lam * |(u m).im| ≤ lam * |(u 0).im| + lam * (∑ j ∈ Finset.range m, |(Φ j).im|) := by
        have h2 : |(u 0 + ∑ j ∈ Finset.range m, Φ j).im|
            ≤ |(u 0).im| + (∑ j ∈ Finset.range m, |(Φ j).im|) := by
          have h3 : (u 0 + ∑ j ∈ Finset.range m, Φ j).im
              = (u 0).im + (∑ j ∈ Finset.range m, Φ j).im := Complex.add_im _ _
          rw [h3]
          have h4 : |(∑ j ∈ Finset.range m, Φ j).im| ≤ ∑ j ∈ Finset.range m, |(Φ j).im| := by
            rw [sum_im_eq]
            exact Finset.abs_sum_le_sum_abs _ _
          have h5 := abs_add_le (u 0).im (∑ j ∈ Finset.range m, Φ j).im
          linarith
        calc lam * |(u m).im| = lam * |(u 0 + ∑ j ∈ Finset.range m, Φ j).im| := by rw [hiter m hm]
          _ ≤ lam * (|(u 0).im| + ∑ j ∈ Finset.range m, |(Φ j).im|) :=
              mul_le_mul_of_nonneg_left h2 hlam.le
          _ = lam * |(u 0).im| + lam * (∑ j ∈ Finset.range m, |(Φ j).im|) := by ring
      have hdrift : lam * (∑ j ∈ Finset.range m, |(Φ j).im|)
          ≤ 2 * (B + 1) * (8 / R ^ 3 + 3 / (2 * R)) + lam * ((n : ℝ) * (lam / (8 * Real.pi * R)))
            + 100 * (n : ℝ) * lam ^ 3
            + (2 + 4 * B + 2 * A) * (48.5 * lam / R + (n : ℝ) * lam ^ 3) := by
        have hcs : lam * (Csx n R + Csd n R) ≤ 8 / R ^ 3 + 3 / (2 * R) := by
          have hcsx : lam * Csx n R
              ≤ lam * (1 / (R / 4 + 2) + 3 * Real.log (1 + 4 * Real.pi / (lam * R))) := by
            rw [Csx]
            apply mul_le_mul_of_nonneg_left _ hlam.le
            have h1 : Real.log ((R / 4 + 2 + (n : ℝ) * (1 / 3)) / (R / 4 + 2))
                ≤ Real.log (1 + 4 * Real.pi / (lam * R)) := by
              apply Real.log_le_log (by positivity)
              rw [div_le_iff₀ (by positivity : (0:ℝ) < R / 4 + 2)]
              have hn' : (n : ℝ) * (1 / 3) ≤ Real.pi / lam := by
                rw [le_div_iff₀ hlam]
                nlinarith [hnlam]
              have hp : Real.pi / lam ≤ 4 * Real.pi / (lam * R) * (R / 4 + 2) := by
                rw [show 4 * Real.pi / (lam * R) * (R / 4 + 2)
                    = 4 * Real.pi * (R / 4 + 2) / (lam * R) by ring]
                rw [div_le_div_iff₀ hlam (by positivity : (0:ℝ) < lam * R)]
                nlinarith [Real.pi_pos, hR, hlam]
              linarith [hn', hp]
            linarith
          have hcsd : lam * Csd n R
              ≤ lam * (1 / (R / 4) + 3 * Real.log (1 + 4 * Real.pi / (lam * R))) := by
            rw [Csd]
            apply mul_le_mul_of_nonneg_left _ hlam.le
            have h1 : Real.log ((R / 4 + (n : ℝ) * (1 / 3)) / (R / 4))
                ≤ Real.log (1 + 4 * Real.pi / (lam * R)) := by
              apply Real.log_le_log (by positivity)
              rw [div_le_iff₀ (by positivity : (0:ℝ) < R / 4)]
              have hn' : (n : ℝ) * (1 / 3) ≤ Real.pi / lam := by
                rw [le_div_iff₀ hlam]
                nlinarith [hnlam]
              have hp : Real.pi / lam ≤ 4 * Real.pi / (lam * R) * (R / 4) := by
                rw [show 4 * Real.pi / (lam * R) * (R / 4) = Real.pi / lam by field_simp]
              linarith [hn', hp]
            linarith
          have hlog := lam_log_le lam R hlam hR hlamR
          have h1 : 1 / (R / 4 + 2) ≤ 4 / R := by
            rw [div_le_div_iff₀ (by positivity) hRpos]; linarith
          have h2 : 1 / (R / 4) = 4 / R := by ring
          have h4 : lam * Csx n R
              ≤ lam * (4 / R) + 3 * (lam * Real.log (1 + 4 * Real.pi / (lam * R))) := by
            calc lam * Csx n R
                ≤ lam * (1 / (R / 4 + 2) + 3 * Real.log (1 + 4 * Real.pi / (lam * R))) := hcsx
              _ ≤ lam * (4 / R + 3 * Real.log (1 + 4 * Real.pi / (lam * R))) := by
                  apply mul_le_mul_of_nonneg_left _ hlam.le
                  linarith [h1]
              _ = lam * (4 / R) + 3 * (lam * Real.log (1 + 4 * Real.pi / (lam * R))) := by ring
          have h5 : lam * Csd n R
              ≤ lam * (4 / R) + 3 * (lam * Real.log (1 + 4 * Real.pi / (lam * R))) := by
            calc lam * Csd n R
                ≤ lam * (1 / (R / 4) + 3 * Real.log (1 + 4 * Real.pi / (lam * R))) := hcsd
              _ = lam * (4 / R + 3 * Real.log (1 + 4 * Real.pi / (lam * R))) := by rw [h2]
              _ = lam * (4 / R) + 3 * (lam * Real.log (1 + 4 * Real.pi / (lam * R))) := by ring
          have hlamle : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith [hlamR]
          have h6 : lam * (4 / R) ≤ 4 / R ^ 3 := by
            rw [show lam * (4 / R) = 4 * lam / R by ring,
              div_le_div_iff₀ hRpos (by positivity : (0:ℝ) < R^3)]
            nlinarith [hlamle, hRpos]
          have h7 : 3 * (lam * Real.log (1 + 4 * Real.pi / (lam * R))) ≤ 3 * (1 / (4 * R)) := by
            linarith [hlog]
          have h8 : lam * Csx n R ≤ 4 / R ^ 3 + 3 * (1 / (4 * R)) := by linarith [h4, h6, h7]
          have h9 : lam * Csd n R ≤ 4 / R ^ 3 + 3 * (1 / (4 * R)) := by linarith [h5, h6, h7]
          have h10 : (4:ℝ) / R ^ 3 + 3 * (1 / (4 * R)) + (4 / R ^ 3 + 3 * (1 / (4 * R)))
              = 8 / R ^ 3 + 3 / (2 * R) := by
            field_simp
            try ring
          have h3 : lam * (Csx n R + Csd n R) = lam * Csx n R + lam * Csd n R := by ring
          rw [h3]
          linarith [h8, h9, h10]
        have hcs2 : 2 * (Csx2 R + Csd2 R) ≤ 48.5 / R := by
          have h1 : 1 / (R / 4 + 2) ≤ 4 / R := by
            rw [div_le_div_iff₀ (by positivity) hRpos]; linarith
          have h2 : 1 / (R / 4) = 4 / R := by ring
          have h3 : 1 / (R / 4 + 2) ^ 2 ≤ 16 / R ^ 2 := by
            have h4 : (4 / R) ^ 2 = 16 / R ^ 2 := by rw [div_pow]; norm_num
            calc 1 / (R / 4 + 2) ^ 2 = (1 / (R / 4 + 2)) ^ 2 := by rw [div_pow]; norm_num
              _ ≤ (4 / R) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
              _ = 16 / R ^ 2 := h4
          have h5 : 1 / (R / 4) ^ 2 = 16 / R ^ 2 := by rw [div_pow]; norm_num
          have h6 : 1 / ((1 / 3) * (R / 4 + 2)) = 3 / (R / 4 + 2) := by
            rw [show (1:ℝ) / 3 * (R / 4 + 2) = (R / 4 + 2) / 3 by ring, one_div_div]
          have h6' : 3 / (R / 4 + 2) ≤ 12 / R := by
            rw [div_le_div_iff₀ (by positivity) hRpos]; linarith
          have h7 : 1 / ((1 / 3) * (R / 4)) = 12 / R := by
            rw [show (1:ℝ) / 3 * (R / 4) = (R / 4) / 3 by ring, one_div_div]
            rw [show (3:ℝ) / (R / 4) = 12 / R by field_simp; try ring]
          have hR2 : (0:ℝ) < R ^ 2 := by positivity
          have hsum : Csx2 R + Csd2 R ≤ 32 / R ^ 2 + 24 / R := by
            rw [Csx2, Csd2, h6, h5, h7]
            have h11 : (16:ℝ) / R ^ 2 + 12 / R + (16 / R ^ 2 + 12 / R) = 32 / R ^ 2 + 24 / R := by
              field_simp
              try ring
            linarith [h3, h6', h11]
          have hfin : 2 * (32 / R ^ 2 + 24 / R) ≤ 48.5 / R := by
            rw [show 2 * (32 / R ^ 2 + 24 / R) = 64 / R ^ 2 + 48 / R by ring]
            rw [div_add_div _ _ (ne_of_gt hR2) (ne_of_gt hRpos)]
            rw [div_le_div_iff₀ (by positivity) hRpos]
            nlinarith [hR]
          linarith [hsum, hfin]
        have hA1 : lam * (∑ j ∈ Finset.range m, |(Φ j).im|)
            ≤ lam * ((m : ℝ) * |τ.im| + 2 * (B + 1) * (Csx n R + Csd n R)
              + 100 * lam ^ 2 * (m : ℝ)
              + (2 + 4 * B + 2 * A) * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2)) :=
          mul_le_mul_of_nonneg_left hsumper hlam.le
        have hmle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
        have hb1 : lam * ((m : ℝ) * |τ.im|) ≤ lam * ((n : ℝ) * (lam / (8 * Real.pi * R))) := by
          apply mul_le_mul_of_nonneg_left _ hlam.le
          have h20 : (m : ℝ) * |τ.im| ≤ (m : ℝ) * (lam / (8 * Real.pi * R)) :=
            mul_le_mul_of_nonneg_left himtau2 (Nat.cast_nonneg m)
          have h21 : (m : ℝ) * (lam / (8 * Real.pi * R))
              ≤ (n : ℝ) * (lam / (8 * Real.pi * R)) :=
            mul_le_mul_of_nonneg_right hmle (by positivity)
          linarith
        have hb2 : lam * (2 * (B + 1) * (Csx n R + Csd n R))
            ≤ 2 * (B + 1) * (8 / R ^ 3 + 3 / (2 * R)) := by
          have h10 : (0:ℝ) ≤ 2 * (B + 1) := by linarith
          have h11 : lam * (Csx n R + Csd n R) ≤ 8 / R ^ 3 + 3 / (2 * R) := hcs
          nlinarith [h11, h10, hcs]
        have hb3 : lam * (100 * lam ^ 2 * (m : ℝ)) ≤ 100 * (n : ℝ) * lam ^ 3 := by
          have h12 : lam * (100 * lam ^ 2 * (m : ℝ)) = 100 * lam ^ 3 * (m : ℝ) := by ring
          rw [h12]
          have h13 : (0:ℝ) ≤ 100 * lam ^ 3 := by positivity
          have h14 := mul_le_mul_of_nonneg_left hmle h13
          have h15 : 100 * lam ^ 3 * (n : ℝ) = 100 * (n : ℝ) * lam ^ 3 := by ring
          linarith [h14, h15.le, h15.ge]
        have hb4 : lam * ((2 + 4 * B + 2 * A) * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2))
            ≤ (2 + 4 * B + 2 * A) * (48.5 * lam / R + (n : ℝ) * lam ^ 3) := by
          have hK : (0:ℝ) ≤ 2 + 4 * B + 2 * A := by linarith
          have h16 : lam * (2 * (Csx2 R + Csd2 R)) ≤ 48.5 * lam / R := by
            have h17 := mul_le_mul_of_nonneg_left hcs2 hlam.le
            have h18 : lam * (48.5 / R) = 48.5 * lam / R := by ring
            linarith [h17, h18.le, h18.ge]
          have h19 : lam * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2)
              = lam * (2 * (Csx2 R + Csd2 R)) + lam * ((n : ℝ) * lam ^ 2) := by ring
          have h20 : lam * ((n : ℝ) * lam ^ 2) = (n : ℝ) * lam ^ 3 := by ring
          have h21 : lam * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2)
              ≤ 48.5 * lam / R + (n : ℝ) * lam ^ 3 := by
            rw [h19, h20]; linarith [h16]
          have h22 : lam * ((2 + 4 * B + 2 * A) * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2))
              = (2 + 4 * B + 2 * A) * (lam * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2)) := by ring
          rw [h22]
          exact mul_le_mul_of_nonneg_left h21 hK
        have h21 : lam * ((m : ℝ) * |τ.im| + 2 * (B + 1) * (Csx n R + Csd n R)
              + 100 * lam ^ 2 * (m : ℝ)
              + (2 + 4 * B + 2 * A) * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2))
            = lam * ((m : ℝ) * |τ.im|) + lam * (2 * (B + 1) * (Csx n R + Csd n R))
              + lam * (100 * lam ^ 2 * (m : ℝ))
              + lam * ((2 + 4 * B + 2 * A) * (2 * (Csx2 R + Csd2 R) + (n : ℝ) * lam ^ 2)) := by
          ring
        linarith [hA1, hb1, hb2, hb3, hb4, h21.le, h21.ge]
      have harith := arith_all lam R A B n hlam hR hlamR hA hB0 hAr hnlam
      have hfinal : lam * |(u m).im| ≤ 1 := by
        have h10 : lam * |(u 0).im| ≤ lam * (R / 4 + 4 + Real.log R) :=
          mul_le_mul_of_nonneg_left hy0 hlam.le
        linarith [h1, hdrift, h10, harith]
      exact hfinal
  exact hmain n le_rfl

end Work.PARIMPL2.Direct
