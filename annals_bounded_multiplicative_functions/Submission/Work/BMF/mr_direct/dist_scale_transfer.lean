import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct.contDist_sq_le
import Submission.Work.BMF.mr_direct.D_mono
import Submission.Work.BMF.mr_direct.nat_cpow_I_norm_le
import Submission.Commons.NumberTheory.Mertens.mertens_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Transfer of the pretentious distance between comparable scales

`Work.BMF.mr_direct.dist_scale_transfer` turns a lower bound for the pretentious distance
`𝔻 g (n ↦ n^{iu})` at a *single* scale `Y` into a lower bound at every scale in the window
`[Y^{1/4}/16, 16 Y]`, at the price of replacing the constant `B ≥ 8` by `√(B²/2)`.

The proof combines two ingredients:

* `contDist_sq_le` (continuity of the squared distance when the truncation is lowered) and
  `D_mono` (monotonicity), which reduce the claim to an explicit bound for the sum `∑ 1/p`
  over the primes in `(x, Y]`;
* Mertens' second theorem in the explicit form provided by
  `Commons.NumberTheory.Mertens`: the Abel identity
  `∑_{p ≤ x} 1/p = (∑_{p ≤ x} log p / p)/log x + ∫₂ˣ (∑_{p ≤ t} log p/p)/(t log²t) dt`
  together with Chebyshev's upper bound `∑_{p ≤ x} log p/p ≤ log 4 (1 + log x)`.

Since `Y ≤ (16x)⁴`, the ratio `log Y / log x` is at most `12`, so the excess
`∑_{x < p ≤ Y} 1/p` is bounded by `log 4 (1 + log 12) + 1 ≤ 9`, far below the `B²/4 ≥ 16`
available when `B ≥ 8`.
-/

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open scoped ComplexConjugate
open Commons.NumberTheory.Mertens

noncomputable section

/-! ## Elementary numerical estimates -/

private lemma log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

private lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  have hh := Real.log_pow (2 : ℝ) 2
  norm_num at hh
  exact hh

private lemma log_sixteen_eq : Real.log 16 = 4 * Real.log 2 := by
  have hh := Real.log_pow (2 : ℝ) 4
  norm_num at hh
  exact hh

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [log_four_eq]; linarith

private lemma log_twelve_le_three : Real.log 12 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 12)]
  have h : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
    have := Real.exp_nat_mul (1 : ℝ) 3
    simpa using this
  rw [h]
  have h1 : (12 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
  have h2 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  linarith

private lemma log_twentyfour_le_four : Real.log 24 ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 24)]
  have h : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
    have := Real.exp_nat_mul (1 : ℝ) 4
    simpa using this
  rw [h]
  have h1 : (24 : ℝ) < (2.7182818283 : ℝ) ^ 4 := by norm_num
  have h2 : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
  linarith

/-! ## Nonnegativity of `𝔻` -/

private lemma D_nonneg' (f g : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (X : ℝ) :
    0 ≤ BoundedMultiplicativeFunctions.𝔻 f g X := by
  unfold BoundedMultiplicativeFunctions.𝔻
  refine Real.rpow_nonneg (Finset.sum_nonneg ?_) _
  intro p hp
  have h1 : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (f p), norm_nonneg (g p), hf p, hg p]
  have h2 : (f p * conj (g p)).re ≤ 1 := le_trans (Complex.re_le_norm _) h1
  exact div_nonneg (by linarith) (Nat.cast_nonneg p)

/-! ## The prime-reciprocal excess via the Abel identity -/

/-- The Abel identity for the difference of the reciprocal-prime sums. -/
private lemma primeRecips_sub_eq {x Y : ℝ} (hx : 2 ≤ x) (hxY : x ≤ Y) :
    primeRecips Y - primeRecips x
      = (logDiv Y / Real.log Y - logDiv x / Real.log x)
        + ∫ t in x..Y, logDiv t / (t * (Real.log t) ^ 2) := by
  have hxY2 : 2 ≤ Y := le_trans hx hxY
  have hYid := primeRecips_eq_logDiv_div_log_add_integral hxY2
  have hxid := primeRecips_eq_logDiv_div_log_add_integral hx
  have hi1 : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x :=
    intervalIntegrable_logDiv_div_id_log_sq_gen (by norm_num) hx
  have hi2 : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume x Y :=
    intervalIntegrable_logDiv_div_id_log_sq_gen hx hxY
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith

/-- The integral `∫_x^Y (1 + log t)/(t log²t) dt = (1/log x − 1/log Y) + log(log Y/log x)`. -/
private lemma integral_one_add_log_split {x Y : ℝ} (hx : 2 ≤ x) (hxY : x ≤ Y) :
    (∫ t in x..Y, (1 + Real.log t) / (t * (Real.log t) ^ 2))
      = (1 / Real.log x - 1 / Real.log Y)
        + (Real.log (Real.log Y) - Real.log (Real.log x)) := by
  have hxY2 : 2 ≤ Y := le_trans hx hxY
  have hA := integral_one_add_log_div_id_log_sq hxY2
  have hB := integral_one_add_log_div_id_log_sq hx
  have hi1 : IntervalIntegrable ((fun t : ℝ => (1 + Real.log t) / (t * (Real.log t) ^ 2)))
      MeasureTheory.volume 2 x :=
    intervalIntegrable_one_add_log_div_id_log_sq_gen (by norm_num) hx
  have hi2 : IntervalIntegrable ((fun t : ℝ => (1 + Real.log t) / (t * (Real.log t) ^ 2)))
      MeasureTheory.volume x Y :=
    intervalIntegrable_one_add_log_div_id_log_sq_gen hx hxY
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith

/-- Mertens-type difference bound: for `2 ≤ x ≤ Y`,
`∑_{x < p ≤ Y} 1/p ≤ log 4 + log 4/log x + log 4 · log(log Y / log x)`. -/
private lemma primeRecips_sub_le {x Y : ℝ} (hx : 2 ≤ x) (hxY : x ≤ Y) :
    primeRecips Y - primeRecips x ≤ Real.log 4 + Real.log 4 / Real.log x
      + Real.log 4 * Real.log (Real.log Y / Real.log x) := by
  have hxY2 : 2 ≤ Y := le_trans hx hxY
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  -- bound on the upper boundary term
  have hbY : logDiv Y / Real.log Y ≤ Real.log 4 * (1 + 1 / Real.log Y) := by
    have hle := logDiv_le_log4_mul_one_add_log hxY2
    have hd := div_le_div_of_nonneg_right hle hlogY.le
    have heq : Real.log 4 * (1 + Real.log Y) / Real.log Y
        = Real.log 4 * (1 + 1 / Real.log Y) := by
      field_simp
      ring
    linarith [hd, heq.symm ▸ hd]
  -- the lower boundary term is nonpositive
  have hbx : 0 ≤ logDiv x / Real.log x := div_nonneg (logDiv_nonneg x) hlogx.le
  -- bound on the integral
  have hint : (∫ t in x..Y, logDiv t / (t * (Real.log t) ^ 2))
      ≤ Real.log 4 * ((1 / Real.log x - 1 / Real.log Y)
          + (Real.log (Real.log Y) - Real.log (Real.log x))) := by
    have hmono : (∫ t in x..Y, logDiv t / (t * (Real.log t) ^ 2))
        ≤ ∫ t in x..Y, Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := by
      refine intervalIntegral.integral_mono_on hxY
        (intervalIntegrable_logDiv_div_id_log_sq_gen hx hxY)
        ((intervalIntegrable_one_add_log_div_id_log_sq_gen hx hxY).const_mul _) ?_
      intro t ht
      have ht2 : 2 ≤ t := le_trans hx ht.1
      have ht0 : 0 < t := by linarith
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
      have hpos : 0 < t * (Real.log t) ^ 2 := by positivity
      have hle := logDiv_le_log4_mul_one_add_log ht2
      calc logDiv t / (t * (Real.log t) ^ 2)
          ≤ Real.log 4 * (1 + Real.log t) / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right hle hpos.le
        _ = Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := by ring
    calc (∫ t in x..Y, logDiv t / (t * (Real.log t) ^ 2))
        ≤ ∫ t in x..Y, Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := hmono
      _ = Real.log 4 * ∫ t in x..Y, (1 + Real.log t) / (t * (Real.log t) ^ 2) := by
            rw [intervalIntegral.integral_const_mul]
      _ = Real.log 4 * ((1 / Real.log x - 1 / Real.log Y)
            + (Real.log (Real.log Y) - Real.log (Real.log x))) := by
            rw [integral_one_add_log_split hx hxY]
  have hmain := primeRecips_sub_eq hx hxY
  have hfin : primeRecips Y - primeRecips x
      ≤ Real.log 4 * (1 + 1 / Real.log Y)
        + Real.log 4 * ((1 / Real.log x - 1 / Real.log Y)
            + (Real.log (Real.log Y) - Real.log (Real.log x))) := by
    rw [hmain]
    linarith [hbY, hbx, hint]
  calc primeRecips Y - primeRecips x
      ≤ Real.log 4 * (1 + 1 / Real.log Y)
        + Real.log 4 * ((1 / Real.log x - 1 / Real.log Y)
            + (Real.log (Real.log Y) - Real.log (Real.log x))) := hfin
    _ = Real.log 4 + Real.log 4 / Real.log x
        + Real.log 4 * (Real.log (Real.log Y) - Real.log (Real.log x)) := by ring
    _ = Real.log 4 + Real.log 4 / Real.log x
        + Real.log 4 * Real.log (Real.log Y / Real.log x) := by
        rw [Real.log_div (ne_of_gt hlogY) (ne_of_gt hlogx)]

/-- Numeric form on the window: if `4 ≤ x ≤ Y` and `log Y ≤ 4 log (16x)`, then
`log 4 + log 4/log x + log 4 · log(log Y/log x) ≤ 16`. -/
private lemma log_bound_large {x Y : ℝ} (hx : 4 ≤ x) (hxY : x ≤ Y)
    (hlogY : Real.log Y ≤ 4 * Real.log (16 * x)) :
    Real.log 4 + Real.log 4 / Real.log x + Real.log 4 * Real.log (Real.log Y / Real.log x)
      ≤ 16 := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith
  have hlog4x : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hquot : Real.log 4 / Real.log x ≤ 1 := (div_le_one hlogx).mpr hlog4x
  have hlog2 : 2 * Real.log 2 ≤ Real.log x := by rw [← log_four_eq]; exact hlog4x
  have hlogY' : Real.log Y ≤ 12 * Real.log x := by
    have h16 : Real.log (16 * x) = 4 * Real.log 2 + Real.log x := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hxpos), log_sixteen_eq]
    rw [h16] at hlogY
    nlinarith [hlogY, hlog2]
  have hratio : Real.log Y / Real.log x ≤ 12 := by
    rw [div_le_iff₀ hlogx]; linarith
  have hratio_pos : 0 < Real.log Y / Real.log x := div_pos (Real.log_pos (by linarith)) hlogx
  have hratio_ge : 1 ≤ Real.log Y / Real.log x := by
    rw [le_div_iff₀ hlogx]
    have := Real.log_le_log hxpos hxY
    linarith
  have hlogratio : Real.log (Real.log Y / Real.log x) ≤ 3 :=
    le_trans (Real.log_le_log hratio_pos hratio) log_twelve_le_three
  have hlogratio_nn : 0 ≤ Real.log (Real.log Y / Real.log x) := Real.log_nonneg hratio_ge
  have hprod : Real.log 4 * Real.log (Real.log Y / Real.log x) ≤ 2 * 3 :=
    mul_le_mul log_four_le_two hlogratio hlogratio_nn (by norm_num)
  linarith [log_four_le_two]

/-- The reciprocal-prime sum is at most `16` as soon as `log Y ≤ 24`. -/
private lemma primeRecips_le_sixteen_of_log {Y : ℝ} (hY2 : 2 ≤ Y) (hlogY : Real.log Y ≤ 24) :
    primeRecips Y ≤ 16 := by
  have h := primeRecips_le_log4_mul_loglog_add hY2
  have hll : Real.log (Real.log Y) ≤ 4 := by
    have hpos : 0 < Real.log Y := Real.log_pos (by linarith)
    have h1 : Real.log (Real.log Y) ≤ Real.log 24 := Real.log_le_log hpos hlogY
    linarith [log_twentyfour_le_four]
  have hconst : Real.log 4 * (1 + 2 / Real.log 2) = Real.log 4 + 4 := by
    have hlog2nz : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
    rw [log_four_eq]
    field_simp
    ring
  rw [hconst] at h
  have h1 : Real.log 4 * Real.log (Real.log Y) ≤ 8 := by
    have h2 := mul_le_mul_of_nonneg_left hll log_four_pos.le
    nlinarith [h2, log_four_le_two]
  linarith [log_four_le_two]

/-! ## The transfer theorem -/

theorem dist_scale_transfer (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (B M Y : ℝ) (hB : 8 ≤ B)
    (hY : 16 ^ 4 ≤ Y)
    (hhyp : ∀ u : ℝ, |u| ≤ M → B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) :
    ∀ x : ℝ, Y ^ (1/4:ℝ) / 16 ≤ x → x ≤ 16 * Y → ∀ u : ℝ, |u| ≤ M →
      Real.sqrt (B ^ 2 / 2) ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x := by
  intro x hxlow hxupp u hu
  set ψ : ℕ → ℂ := fun n => (n : ℂ) ^ (Complex.I * u) with hψdef
  have hψ : ∀ n, ‖ψ n‖ ≤ 1 := fun n => nat_cpow_I_norm_le n u
  have hBpos : 0 < B := by linarith
  have hY65536 : (16 : ℝ) ^ 4 ≤ Y := hY
  have hYpos : 0 < Y := by norm_num at hY65536; linarith
  -- `Y^{1/4} ≥ 16`
  have hsqrt16 : (16 : ℝ) ≤ Y ^ (1/4 : ℝ) := by
    have hpow : ((16 : ℝ) ^ 4) ^ (1/4 : ℝ) ≤ Y ^ (1/4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hY (by norm_num)
    have hval : ((16 : ℝ) ^ 4) ^ (1/4 : ℝ) = 16 := by
      rw [← Real.rpow_natCast (16 : ℝ) 4]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num
    linarith [hpow, hval.symm ▸ hpow]
  have hx1 : 1 ≤ x := by linarith [hxlow, hsqrt16]
  have hxpos : 0 < x := by linarith
  -- `log Y ≤ 4 log (16x)`
  have hlogYbd : Real.log Y ≤ 4 * Real.log (16 * x) := by
    have h1 : Y ^ (1/4 : ℝ) ≤ 16 * x := by linarith [hxlow]
    have hlogY1 : Real.log (Y ^ (1/4 : ℝ)) = (1/4) * Real.log Y := Real.log_rpow hYpos (1/4)
    have hle : Real.log (Y ^ (1/4 : ℝ)) ≤ Real.log (16 * x) :=
      Real.log_le_log (Real.rpow_pos_of_pos hYpos _) h1
    have hYeq : Real.log Y = 4 * Real.log (Y ^ (1/4 : ℝ)) := by rw [hlogY1]; ring
    linarith [hle, hYeq]
  have hDY : B ≤ BoundedMultiplicativeFunctions.𝔻 g ψ Y := by
    rw [hψdef]; exact hhyp u hu
  have hDY2 : B ^ 2 ≤ BoundedMultiplicativeFunctions.𝔻 g ψ Y ^ 2 := by
    have hnn := D_nonneg' g ψ hg hψ Y
    nlinarith
  by_cases hxY : x ≤ Y
  · -- the interesting case: lower the truncation from `Y` to `x`
    have hsub : ⌊x⌋₊.primesLE ⊆ ⌊Y⌋₊.primesLE := Nat.primesLE_mono (Nat.floor_mono hxY)
    have hsdiff : (∑ p ∈ (⌊Y⌋₊.primesLE \ ⌊x⌋₊.primesLE), (1 : ℝ) / (p : ℝ))
        = primeRecips Y - primeRecips x := by
      unfold primeRecips
      have h := Finset.sum_sdiff (s₁ := ⌊x⌋₊.primesLE) (s₂ := ⌊Y⌋₊.primesLE)
        (f := fun p => (1 : ℝ) / (p : ℝ)) hsub
      linarith
    have hS16 : (∑ p ∈ (⌊Y⌋₊.primesLE \ ⌊x⌋₊.primesLE), (1 : ℝ) / (p : ℝ)) ≤ 16 := by
      rw [hsdiff]
      rcases lt_or_ge x 4 with hx4 | hx4
      · -- `x < 4`: the whole range lies in the numerically controlled region
        have hY2 : 2 ≤ Y := by norm_num at hY65536; linarith
        have hlogY24 : Real.log Y ≤ 24 := by
          have h16 : Real.log (16 * x) = 4 * Real.log 2 + Real.log x := by
            rw [Real.log_mul (by norm_num) (ne_of_gt hxpos), log_sixteen_eq]
          have hlogx4 : Real.log x ≤ Real.log 4 := Real.log_le_log hxpos (le_of_lt hx4)
          have hlog2 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            linarith
          have hx4' : Real.log x ≤ 2 * Real.log 2 := by rw [← log_four_eq]; exact hlogx4
          rw [h16] at hlogYbd
          nlinarith [hlogYbd, hx4', hlog2]
        have hxnn : 0 ≤ primeRecips x := by
          unfold primeRecips
          exact Finset.sum_nonneg (fun p _ => by positivity)
        have hY16 := primeRecips_le_sixteen_of_log hY2 hlogY24
        linarith
      · -- `4 ≤ x`: use the Abel/Mertens difference bound
        exact le_trans (primeRecips_sub_le (by linarith) hxY) (log_bound_large hx4 hxY hlogYbd)
    have hquarter : (16 : ℝ) ≤ B ^ 2 / 4 := by nlinarith
    have hS : (∑ p ∈ (⌊Y⌋₊.primesLE \ ⌊x⌋₊.primesLE), (1 : ℝ) / (p : ℝ)) ≤ B ^ 2 / 4 :=
      le_trans hS16 hquarter
    have hcd := contDist_sq_le g ψ hg hψ hxY
    have hDx2 : B ^ 2 / 2 ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x ^ 2 := by
      have h2 : 2 * (∑ p ∈ (⌊Y⌋₊.primesLE \ ⌊x⌋₊.primesLE), (1 : ℝ) / (p : ℝ)) ≤ B ^ 2 / 2 := by
        linarith
      linarith
    have hDxnn : 0 ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x := D_nonneg' g ψ hg hψ x
    have hfinal : Real.sqrt (B ^ 2 / 2) ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x := by
      rw [Real.sqrt_le_iff]
      exact ⟨hDxnn, hDx2⟩
    rw [hψdef] at hfinal
    exact hfinal
  · -- `x > Y`: monotonicity in the scale
    have hxY' : Y ≤ x := le_of_lt (lt_of_not_ge hxY)
    have hmono := D_mono g ψ hg hψ hxY'
    have hBle : B ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x := le_trans hDY hmono
    have hsqrtB : Real.sqrt (B ^ 2 / 2) ≤ B := by
      rw [Real.sqrt_le_iff]
      exact ⟨hBpos.le, by nlinarith⟩
    have hfinal : Real.sqrt (B ^ 2 / 2) ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x :=
      le_trans hsqrtB hBle
    rw [hψdef] at hfinal
    exact hfinal

end

end Work.BMF.mr_direct
