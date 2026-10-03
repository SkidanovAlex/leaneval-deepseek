/-
# `FIArea2/R6/Sec9Log6.lean` — the §9 logarithmic factor of (9.1) at the round-6 scale

The per-pair factor `log(2 + 1/(1 - γ²))` of (9.1) is bounded by `4 (log N + 2)` on the polar box.

The round-4/5 library states this as `Work.FIArea2.Count.sec9_log_bound`, but that file carries a
`sorry` (and hence `sorryAx` in the axiom closure of every consumer), so the round-6 assembly
proves it here from scratch.  Only three inputs are used:

* the identity `1 - γ² = |Δ|²/|z₁z₂|²`, valid *without* the hypothesis `Δ ≠ 0` as long as
  `z₁, z₂ ≠ 0` (`one_sub_gamOf_sq_eq_gen`); it gives both `1 - γ² ≥ 0` and
  `1/(1-γ²) = |z₁z₂|²/|Δ|²` when `Δ ≠ 0` (which is forced by `1 - γ² > 0`);
* `|Δ| ≥ 1` for `Δ ≠ 0`;
* the polar-box bound `|z_j|² ≤ (1+θ)N` with `θ ≤ 1`, giving `|z₁z₂|² ≤ 4N²`.

Then `1/(1-γ²) ≤ 4N²`, so `2 + 1/(1-γ²) ≤ 6N²` and `log(2+1/(1-γ²)) ≤ log 6 + 2 log N ≤ 2 + 2 log N`.
-/
import Mathlib
import Submission.Work.FIArea2.Sec6Defs
import Submission.Work.FIArea2.R6.one_sub_gamOf_sq_eq

set_option autoImplicit false

namespace Work.FIArea2.R6

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The elementary algebra: for reals `x,y,D,S,N` with `D = x²+y² = N > 0` and `S² = D`,
`1 - (x/S)² = y²/N`.  (Copy of the private helper of `one_sub_gamOf_sq_eq`.) -/
private lemma key_alg6 (x y D S N : ℝ) (hD : 0 < D) (hS : S ^ 2 = D)
    (hkey : x ^ 2 + y ^ 2 = D) (hN : N = D) :
    1 - (x / S) ^ 2 = y ^ 2 / N := by
  have hSD : (x / S) ^ 2 = x ^ 2 / D := by rw [div_pow, hS]
  rw [hSD, hN]
  have hDne : D ≠ 0 := ne_of_gt hD
  field_simp
  linarith

/-- **`1 - γ² = |Δ|²/|z₁z₂|²` without the hypothesis `Δ ≠ 0`.**  The only requirement is that the
two factors be non-zero (so that `|z₁z₂|² > 0`); when `Δ = 0` both sides vanish.  This is
`one_sub_gamOf_sq_eq` with the non-vanishing of `z₁, z₂` taken as a hypothesis instead of being
read off from `Δ ≠ 0`. -/
theorem one_sub_gamOf_sq_eq_gen (z1 z2 : GaussianInt) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) :
    1 - (Work.FIArea2.gamOf z1 z2) ^ 2
      = (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2
        / ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
  have hN1pos : 0 < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea4.gnorm_pos hz1
  have hN2pos : 0 < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea4.gnorm_pos hz2
  have hDpos : 0 < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) :=
    mul_pos hN1pos hN2pos
  have hND : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    rw [Work.FIArea4.gnorm_mul]; push_cast; ring
  have hkeyZ : ((star z1 * z2).re : ℤ) ^ 2 + ((star z1 * z2).im : ℤ) ^ 2
      = (Work.FIPlan.gnorm (z1 * z2) : ℤ) := by
    have h1 : ((star z1 * z2).re : ℤ) ^ 2 + ((star z1 * z2).im : ℤ) ^ 2
        = (star z1 * z2).norm := by
      rw [Zsqrtd.norm_def]; ring
    have h2 : (star z1 * z2).norm = (z1 * z2).norm := by
      rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, ← Zsqrtd.norm_mul]
    rw [h1, h2]
    simp [Work.FIPlan.gnorm]
  have hkeyR : (((star z1 * z2).re : ℤ) : ℝ) ^ 2 + (((star z1 * z2).im : ℤ) : ℝ) ^ 2
      = ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    have h := congrArg (fun t : ℤ => (t : ℝ)) hkeyZ
    push_cast at h
    simpa using h
  have hAbs2 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2
      = (((star z1 * z2).im : ℤ) : ℝ) ^ 2 := by
    have h : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) ^ 2
        = (((star z1 * z2).im : ℤ)) ^ 2 := by
      rw [Work.FIPlan.absDelta, Work.FIPlan.Delta]
      simpa [sq] using Int.natAbs_mul_self (star z1 * z2).im
    have h2 := congrArg (fun t : ℤ => (t : ℝ)) h
    push_cast at h2
    simpa using h2
  have hkeyD : (((star z1 * z2).re : ℤ) : ℝ) ^ 2 + (((star z1 * z2).im : ℤ) : ℝ) ^ 2
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    rw [hkeyR, hND]
  unfold Work.FIArea2.gamOf
  rw [hAbs2]
  exact key_alg6 (((star z1 * z2).re : ℤ) : ℝ) (((star z1 * z2).im : ℤ) : ℝ)
    (((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
    (Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))
    ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
    hDpos (Real.sq_sqrt (le_of_lt hDpos)) hkeyD hND

/-- `log 6 ≤ 2`. -/
private lemma log_six_le_two : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 6)]
  have h := Real.exp_one_gt_d9
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [h, Real.exp_pos 1]

/-- **The §9 logarithmic factor at the round-6 scale.**  On the polar box (5.14) with `θ ≤ 1` and
`N ≥ 1`,

  `log (2 + 1/(1 - γ²)) ≤ 4 (log N + 2)`   (`γ = gamOf z₁ z₂`).

If `1 - γ² = 0` the left side is `log 2 ≤ 8`; otherwise `1 - γ² = |Δ|²/|z₁z₂|²` with
`|Δ| ≥ 1` and `|z₁z₂|² ≤ 4N²`, so `1/(1-γ²) ≤ 4N²` and the logarithm is `≤ log(6N²)`. -/
theorem sec9_log_bound6 (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hN1 : 1 ≤ Pa.N)
    (hn1 : Pa.N < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
    (hn1' : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N)
    (hn2 : Pa.N < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
    (hn2' : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N)
    (hθ : Pa.θ ≤ 1) :
    Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) ≤ 4 * (Real.log Pa.N + 2) := by
  have hNpos : 0 < Pa.N := lt_of_lt_of_le (by norm_num) hN1
  have hlogN' : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hz1 : z1 ≠ 0 := by
    intro h
    rw [h, Work.FIArea4.gnorm_zero] at hn1
    simp at hn1
    linarith
  have hz2 : z2 ≠ 0 := by
    intro h
    rw [h, Work.FIArea4.gnorm_zero] at hn2
    simp at hn2
    linarith
  have hprod : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ≤ 4 * Pa.N ^ 2 := by
    rw [Work.FIArea4.gnorm_mul, Nat.cast_mul]
    have h1θ : (0 : ℝ) ≤ 1 + Pa.θ := by linarith [Pa.hθ0]
    have h2N : (0 : ℝ) ≤ Pa.N := le_of_lt hNpos
    have hA : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := by nlinarith
    have hB : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by nlinarith
    calc ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)
        ≤ (2 * Pa.N) * (2 * Pa.N) :=
          mul_le_mul hA hB (by positivity) (by nlinarith [hNpos])
      _ = 4 * Pa.N ^ 2 := by ring
  have hid := one_sub_gamOf_sq_eq_gen z1 z2 hz1 hz2
  have hnonneg : 0 ≤ 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 := by
    rw [hid]; positivity
  by_cases hcase : 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 ≤ 0
  · have hz : 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 = 0 := le_antisymm hcase hnonneg
    rw [hz, div_zero, add_zero]
    have hlt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  · push_neg at hcase
    have hΔ0 : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
      intro hd
      have hz0 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2 = 0 := by rw [hd]; simp
      rw [hid, hz0, zero_div] at hcase
      exact lt_irrefl 0 hcase
    have ht : 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)
        = ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2 := by
      rw [hid, one_div, inv_div]
    have hDpos : (0 : ℕ) < Work.FIPlan.absDelta z1 z2 := Nat.pos_of_ne_zero hΔ0
    have hD2 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hDpos
      nlinarith
    have hbdd : 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) ≤ 4 * Pa.N ^ 2 := by
      rw [ht]
      calc ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2
          ≤ ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) / 1 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hD2
        _ ≤ 4 * Pa.N ^ 2 := by rw [div_one]; exact hprod
    have htnn : 0 ≤ 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) := by rw [ht]; positivity
    have harg : 2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) ≤ 6 * Pa.N ^ 2 := by
      nlinarith [hbdd, hNpos, sq_nonneg Pa.N]
    have hpos : 0 < 2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) := by linarith
    have h6 : Real.log (6 * Pa.N ^ 2) = Real.log 6 + 2 * Real.log Pa.N := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    calc Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
        ≤ Real.log (6 * Pa.N ^ 2) := Real.log_le_log hpos harg
      _ = Real.log 6 + 2 * Real.log Pa.N := h6
      _ ≤ 4 * (Real.log Pa.N + 2) := by linarith [log_six_le_two]

end

end Work.FIArea2.R6
