import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17g.segment_primitive
import Submission.Work.C17I.JP_shared
import Submission.Work.C17I.J_data_low
import Submission.Work.C17I.J_data_high

/-!
# The package of the six antiderivatives `J₀,…,J₅` at the cusp

This file proves `Work.C17I.J_package`.  Everything is built on
* `Work.C17g.segment_primitive`: on the convex ball `B` the segment integral of a holomorphic
  function is a primitive;
* `Work.C17I.J_data_low` / `Work.C17I.J_data_high`: for each `i : Fin 6` the rational function
  `yQ ^ (i-4) · dyQ` is a quotient `P/Q` with `Q` non-vanishing on any set avoiding `0,1`;
* `Work.C17I.JP_shared.ratFunc_eval_eq_div`: a quotient presentation computes the value of
  `num/denom`;
* the auxiliary value identities `Jpkg_eval_yQ_pow_mul_dyQ_nonneg/neg` below, which evaluate
  `yQ ^ k · dyQ` for an arbitrary integer exponent `k` (the fourth conjunct of the statement
  quantifies over `i : ℤ`, not only over `Fin 6`).
-/

namespace Work.C17I

open MeasureTheory Set intervalIntegral
open Polynomial

noncomputable section

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! ## The quotient presentations of `yQ` and `dyQ` -/

theorem Jpkg_yQ_eq_alg : Work.C17.yQ
    = algebraMap (Polynomial ℚ) (RatFunc ℚ) ((X : Polynomial ℚ)^2)
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) ((X : Polynomial ℚ) - 1) := by
  rw [Work.C17.yQ, Work.C17.xQ]
  simp only [map_pow, RatFunc.algebraMap_X, map_sub, map_one]

theorem Jpkg_dyQ_eq_alg : Work.C17.dyQ
    = algebraMap (Polynomial ℚ) (RatFunc ℚ) ((X : Polynomial ℚ)^2 - 2*X)
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) (((X : Polynomial ℚ) - 1)^2) := by
  rw [Work.C17.dyQ, Work.C17.xQ]
  simp only [map_pow, RatFunc.algebraMap_X, map_sub, map_mul, map_ofNat, map_one]

theorem Jpkg_X_sub_one_ne_zero : ((X : Polynomial ℚ) - 1) ≠ 0 := by
  simpa using (monic_X_sub_C (1 : ℚ)).ne_zero

/-! ## The value of `yQ ^ k · dyQ` for an arbitrary integer exponent -/

/-- For `k ≥ 0` the value of `yQ ^ k · dyQ` at a point `z ≠ 1` is `yC z ^ k · y'(z)`. -/
theorem Jpkg_eval_yQ_pow_mul_dyQ_nonneg (k : ℤ) (hk : 0 ≤ k) {U : Set ℂ}
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) :
    ∀ z ∈ U, (((Work.C17.yQ ^ k) * Work.C17.dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
        / (((Work.C17.yQ ^ k) * Work.C17.dyQ).denom.eval₂ (algebraMap ℚ ℂ) z)
      = (Work.C17.yC z) ^ k * ((z ^ 2 - 2 * z) / (z - 1) ^ 2) := by
  intro z hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h1 z hz)
  set a := k.toNat with ha
  set P : Polynomial ℚ := ((X : Polynomial ℚ)^2)^a * ((X : Polynomial ℚ)^2 - 2*X) with hP
  set Q : Polynomial ℚ := ((X : Polynomial ℚ) - 1)^(a + 2) with hQ
  have hr : Work.C17.yQ ^ k * Work.C17.dyQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) P / algebraMap (Polynomial ℚ) (RatFunc ℚ) Q := by
    rw [Jpkg_yQ_eq_alg, Jpkg_dyQ_eq_alg, hP, hQ, ha]
    rw [← Int.toNat_of_nonneg hk, zpow_natCast, div_pow, div_mul_div_comm]
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, pow_add]
    congr 1 <;> ring
  have hQne : Q ≠ 0 := by
    rw [hQ]
    exact pow_ne_zero _ Jpkg_X_sub_one_ne_zero
  have hQz : Q.eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
    rw [hQ]
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub,
      Polynomial.eval₂_one]
    exact pow_ne_zero _ hz1
  show RatFunc.eval (algebraMap ℚ ℂ) z (Work.C17.yQ ^ k * Work.C17.dyQ) = _
  rw [ratFunc_eval_eq_div (r := Work.C17.yQ ^ k * Work.C17.dyQ) (P := P) (Q := Q) hQne hr hQz]
  rw [hP, hQ]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
  rw [Work.C17.yC,
    show k = (a : ℤ) from (Int.toNat_of_nonneg hk).symm,
    zpow_natCast, div_pow, ← pow_mul]
  field_simp
  ring

/-- For `k < 0` the value of `yQ ^ k · dyQ` at a point `z ≠ 0, 1` is `yC z ^ k · y'(z)`. -/
theorem Jpkg_eval_yQ_pow_mul_dyQ_neg (k : ℤ) (hk : k < 0) {U : Set ℂ}
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) :
    ∀ z ∈ U, (((Work.C17.yQ ^ k) * Work.C17.dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
        / (((Work.C17.yQ ^ k) * Work.C17.dyQ).denom.eval₂ (algebraMap ℚ ℂ) z)
      = (Work.C17.yC z) ^ k * ((z ^ 2 - 2 * z) / (z - 1) ^ 2) := by
  intro z hz
  have hz0 : z ≠ 0 := h0 z hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h1 z hz)
  set m := (-k).toNat with hm
  set P : Polynomial ℚ := ((X : Polynomial ℚ) - 1)^m * ((X : Polynomial ℚ)^2 - 2*X) with hP
  set Q : Polynomial ℚ := ((X : Polynomial ℚ)^2)^m * ((X : Polynomial ℚ) - 1)^2 with hQ
  have hk' : k = -((m : ℤ)) := by
    rw [hm]; have := Int.toNat_of_nonneg (show (0:ℤ) ≤ -k by omega); omega
  have hr : Work.C17.yQ ^ k * Work.C17.dyQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) P / algebraMap (Polynomial ℚ) (RatFunc ℚ) Q := by
    rw [Jpkg_yQ_eq_alg, Jpkg_dyQ_eq_alg, hP, hQ, hk']
    rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div, div_pow, div_mul_div_comm]
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
  have hQne : Q ≠ 0 := by
    rw [hQ]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero 2 Polynomial.X_ne_zero))
      (pow_ne_zero _ Jpkg_X_sub_one_ne_zero)
  have hQz : Q.eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
    rw [hQ]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub,
      Polynomial.eval₂_one]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero 2 hz0)) (pow_ne_zero _ hz1)
  show RatFunc.eval (algebraMap ℚ ℂ) z (Work.C17.yQ ^ k * Work.C17.dyQ) = _
  rw [ratFunc_eval_eq_div (r := Work.C17.yQ ^ k * Work.C17.dyQ) (P := P) (Q := Q) hQne hr hQz]
  rw [hP, hQ]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
  rw [Work.C17.yC, hk', zpow_neg, zpow_natCast, ← inv_pow, inv_div, div_pow, ← pow_mul]
  field_simp

/-! ## The ball avoids `0` and `1` -/

theorem Jpkg_ball_ne_zero_ne_one (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : 2 * δ ≤ Work.C17.xsOf m n) (hδ2 : 2 * δ ≤ 1 - Work.C17.xsOf m n) :
    (∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ, z ≠ 0) ∧
    (∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ, z ≠ 1) := by
  have hxs0 := Work.C17.xsOf_pos m n hm hlt
  have hxs1 := Work.C17.xsOf_lt_one m n hm hlt
  constructor
  · intro z hz h
    rw [Metric.mem_ball, dist_eq_norm] at hz
    subst h
    have hval : ‖((0 : ℂ) - ((Work.C17.xsOf m n : ℝ) : ℂ))‖ = Work.C17.xsOf m n := by
      have h' : ((0 : ℂ) - ((Work.C17.xsOf m n : ℝ) : ℂ))
          = (((0 : ℝ) - Work.C17.xsOf m n : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_zero]
      rw [h']
      exact (calc ‖(((0 : ℝ) - Work.C17.xsOf m n : ℝ) : ℂ)‖ = |(0:ℝ) - Work.C17.xsOf m n| :=
              RCLike.norm_ofReal _
        _ = Work.C17.xsOf m n := by rw [zero_sub, abs_neg, abs_of_nonneg (le_of_lt hxs0)])
    rw [hval] at hz
    linarith
  · intro z hz h
    rw [Metric.mem_ball, dist_eq_norm] at hz
    subst h
    have hval : ‖((1 : ℂ) - ((Work.C17.xsOf m n : ℝ) : ℂ))‖ = 1 - Work.C17.xsOf m n := by
      have h' : ((1 : ℂ) - ((Work.C17.xsOf m n : ℝ) : ℂ))
          = (((1 : ℝ) - Work.C17.xsOf m n : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_one]
      rw [h']
      exact (calc ‖(((1 : ℝ) - Work.C17.xsOf m n : ℝ) : ℂ)‖ = |(1:ℝ) - Work.C17.xsOf m n| :=
              RCLike.norm_ofReal _
        _ = 1 - Work.C17.xsOf m n := abs_of_nonneg (by linarith))
    rw [hval] at hz
    linarith

/-! ## The package of antiderivatives -/

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# The package of the six antiderivatives `J₀,…,J₅` at the cusp

For `y₁ : ℂ → ℂ` holomorphic on `B = ball (x_s) δ` (`x_s = Work.C17.xsOf m n`) and `z ≠ 1`, let
`y = z²/(z-1) = yC z`.  The claim produces `J : Fin 6 → ℂ → ℂ` with, for every `i : Fin 6`:
`J i` holomorphic on `B`, `J i x_s = 0`, and
`J i' z = ((yQ ^ ((i:ℤ)-4) * dyQ).num.eval₂ ℚ ℂ z) / (…denom…) * y₁ z` there.

Mathematically `J i` is the antiderivative vanishing at `x_s` of `y^{i-4} · y' · y₁`
(`yQ = x²/(x-1)`, `dyQ = (x²-2x)/(x-1)²` are the `RatFunc ℚ` models of `y` and `y'`), which exists
because `B` is convex: use `Work.C17g.segment_primitive` (proved) with the base point `x_s`.

The needed facts about `RatFunc.num`/`RatFunc.denom`:
* `RatFunc.num_div_denom` and `RatFunc.denom_ne_zero`;
* the denominator does not vanish on `B`: the poles of `yQ^k · dyQ` are at `x = 0` and `x = 1`
  (reduced forms: `yQ · dyQ = x²(x-2)/(x-1)³`, `dyQ = x(x-2)/(x-1)²`,
  `yQ⁻¹dyQ = (x-2)/(x(x-1))`, `yQ⁻²dyQ = (x-2)/x³`, `yQ⁻³dyQ = (x-1)(x-2)/x⁵`,
  `yQ⁻⁴dyQ = (x-1)²(x-2)/x⁷`), and `0, 1 ∉ B` because `δ ≤ x_s/2` and `δ ≤ (1-x_s)/2`
  (hypotheses `hδ1`, `hδ2`), with `0 < x_s < 1`;
* the *value* identity, which is what the downstream computation uses:
  `(num.eval₂ z)/(denom.eval₂ z) = (yC z) ^ ((i:ℤ)-4) * ((z^2 - 2*z)/(z-1)^2)` for `z ∈ B`
  (note `yC z ≠ 0` there since `z ≠ 0`, and `z ≠ 1`).

`hgap` is only used to ensure `x_s > 0` (`Work.CLift.LocationSing`/`Work.CLoc` or direct estimates
on `xsOf m n`).

Helper auxiliary results may be added above the claim; do not change the claim. -/

theorem J_package (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n)
    {y1 : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ ≤ Work.C17.xsOf m n)
    (hδ2 : 2 * δ ≤ 1 - Work.C17.xsOf m n)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ)) :
    ∃ J : Fin 6 → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (J i) (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ)) ∧
      (∀ i, J i ((Work.C17.xsOf m n : ℂ)) = 0) ∧
      (∀ i, ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ,
        HasDerivAt (J i)
          ((((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
            / (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).denom.eval₂ (algebraMap ℚ ℂ) z)
            * y1 z) z) ∧
      (∀ i, ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ,
        (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
            / (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).denom.eval₂ (algebraMap ℚ ℂ) z)
          = (Work.C17.yC z) ^ ((i : ℤ) - 4) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2)) := by
  classical
  obtain ⟨hne0, hne1⟩ := Jpkg_ball_ne_zero_ne_one m n hm hlt hδ hδ1 hδ2
  set B : Set ℂ := Metric.ball ((Work.C17.xsOf m n : ℂ)) δ with hB
  have hne0' : ∀ z ∈ B, z ≠ 0 := fun z hz => hne0 z (hB ▸ hz)
  have hne1' : ∀ z ∈ B, z ≠ 1 := fun z hz => hne1 z (hB ▸ hz)
  have hconv : Convex ℝ B := hB ▸ convex_ball ((Work.C17.xsOf m n : ℂ)) δ
  have hopen : IsOpen B := hB ▸ Metric.isOpen_ball
  have hmem : ((Work.C17.xsOf m n : ℂ)) ∈ B := by
    rw [hB, Metric.mem_ball, dist_self]; exact hδ
  have hdata : ∀ i : Fin 6, ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (∀ z ∈ B, Q.eval₂ (algebraMap ℚ ℂ) z ≠ 0) ∧
      Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) P / algebraMap (Polynomial ℚ) (RatFunc ℚ) Q ∧
      (∀ z ∈ B, P.eval₂ (algebraMap ℚ ℂ) z / Q.eval₂ (algebraMap ℚ ℂ) z
        = Work.C17.yC z ^ ((i : ℤ) - 4) * ((z ^ 2 - 2 * z) / (z - 1) ^ 2)) := by
    intro i
    rcases Nat.lt_or_ge ((i : ℕ)) 3 with h | h
    · exact J_data_low i (by omega) hne0' hne1'
    · exact J_data_high i h hne0' hne1'
  choose P Q hQne hQnz hr hval using hdata
  let f : Fin 6 → ℂ → ℂ := fun i w =>
    RatFunc.eval (algebraMap ℚ ℂ) w (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ) * y1 w
  have hfdiff : ∀ i : Fin 6, DifferentiableOn ℂ (f i) B := by
    intro i
    have hmul : DifferentiableOn ℂ
        (fun z => (P i).eval₂ (algebraMap ℚ ℂ) z / (Q i).eval₂ (algebraMap ℚ ℂ) z * y1 z) B :=
      ((differentiableOn_eval₂ (P i) B).div (differentiableOn_eval₂ (Q i) B) (hQnz i)).mul hy1d
    refine DifferentiableOn.congr hmul ?_
    intro z hz
    have hE := ratFunc_eval_eq_div (r := Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)
      (P := P i) (Q := Q i) (hQne i) (hr i) (hQnz i z hz)
    show RatFunc.eval (algebraMap ℚ ℂ) z (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ) * y1 z
      = (fun z => (P i).eval₂ (algebraMap ℚ ℂ) z / (Q i).eval₂ (algebraMap ℚ ℂ) z * y1 z) z
    rw [hE]
  have hJ : ∀ i : Fin 6,
      DifferentiableOn ℂ (fun z => (z - ((Work.C17.xsOf m n : ℂ))) • ∫ t in (0 : ℝ)..1,
        f i (((Work.C17.xsOf m n : ℂ)) + t • (z - ((Work.C17.xsOf m n : ℂ))))) B ∧
      ∀ z ∈ B, HasDerivAt (fun z => (z - ((Work.C17.xsOf m n : ℂ))) • ∫ t in (0 : ℝ)..1,
        f i (((Work.C17.xsOf m n : ℂ)) + t • (z - ((Work.C17.xsOf m n : ℂ))))) (f i z) z :=
    fun i => Work.C17g.segment_primitive (S := B) hconv hopen hmem (hfdiff i)
  refine ⟨fun i z => (z - ((Work.C17.xsOf m n : ℂ))) • ∫ t in (0 : ℝ)..1,
      f i (((Work.C17.xsOf m n : ℂ)) + t • (z - ((Work.C17.xsOf m n : ℂ)))), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hJ i).1
  · intro i
    simp
  · intro i z hz
    show HasDerivAt _ (f i z) z
    exact (hJ i).2 z hz
  · intro i z hz
    rcases lt_or_ge i 4 with h | h
    · exact Jpkg_eval_yQ_pow_mul_dyQ_neg (i - 4) (by omega) hne0' hne1' z hz
    · exact Jpkg_eval_yQ_pow_mul_dyQ_nonneg (i - 4) (by omega) hne0' hne1' z hz

end

end Work.C17I
