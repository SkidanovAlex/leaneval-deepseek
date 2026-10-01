import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs

open MeasureTheory
open scoped BigOperators

namespace Work.ZeroDensity.LogFree

/-!
# Elementary facts about the duality-damping weight `gfun`

`gfun X U' n = e^{-n/X} - e^{-n/U'}` (HB §11, the damping factor of the duality count)
satisfies, for `0 < U' ≤ X` and `X ≥ 1`:

* it is nonnegative;
* the quotients `gfun X U' n / n` are antitone in `n`;
* the partial sums of `gfun X U' n / n` are bounded by `log (2X) + 2`.

The middle point is the antitonicity of `x ↦ (e^{-ax} - e^{-bx})/x` on `(0,∞)` for
`0 ≤ a ≤ b`, which follows from the integral representation
`(e^{-ax} - e^{-bx})/x = ∫_u in a..b, e^{-x u}`.  The last point uses the logarithmic
power series bound `∑_{n ≥ 1} e^{-an}/n ≤ -log (1 - e^{-a})` together with `1 - e^{-a} ≥ a/2`
for `0 < a ≤ 1`.
-/

/-- `∫_a^b e^{-xu} du = (e^{-ax} - e^{-bx})/x` for `x ≠ 0`. -/
private lemma integral_exp_neg_mul_gfun (a b x : ℝ) (hx : x ≠ 0) :
    ∫ u in a..b, Real.exp (-(x * u)) = (Real.exp (-(a * x)) - Real.exp (-(b * x))) / x := by
  have key : ∫ u in a..b, Real.exp ((-x) * u) = (-x)⁻¹ * ∫ v in (-x)*a..(-x)*b, Real.exp v := by
    rw [intervalIntegral.integral_comp_mul_left (fun v : ℝ => Real.exp v) (by simpa using hx)]
    simp
  rw [show (fun u => Real.exp (-(x*u))) = (fun u => Real.exp ((-x) * u)) by ext u; rw [neg_mul]]
  rw [key, integral_exp]
  field_simp
  ring

/-- For `0 ≤ a ≤ b` the function `x ↦ (e^{-ax} - e^{-bx})/x` is antitone on `(0,∞)`. -/
lemma expNegDiv_antitone_gfun {a b s t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 < s)
    (hst : s ≤ t) :
    (Real.exp (-(a * t)) - Real.exp (-(b * t))) / t ≤
      (Real.exp (-(a * s)) - Real.exp (-(b * s))) / s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  rw [← integral_exp_neg_mul_gfun a b t (ne_of_gt ht),
    ← integral_exp_neg_mul_gfun a b s (ne_of_gt hs)]
  refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
  · exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).intervalIntegrable
      (μ := volume) a b
  · exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).intervalIntegrable
      (μ := volume) a b
  · intro u hu
    exact Real.exp_le_exp.mpr (by nlinarith [hu.1, ha, hs, hst])

/-- `∑_{n=1}^N e^{-an}/n ≤ log (2/a)` for `0 < a ≤ 1`. -/
lemma sum_expNegDiv_le_gfun {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.exp (-(a * n)) / (n : ℝ) ≤ Real.log (2 / a) := by
  set x := Real.exp (-a) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by rw [hxdef, Real.exp_lt_one_iff]; linarith
  have hxabs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  -- the logarithmic power series, shifted by one
  have hHasShift : HasSum (fun n : ℕ => x ^ (n+1) / ((n:ℝ)+1)) (-Real.log (1 - x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hxabs
  have hHas : HasSum (fun n : ℕ => x ^ n / (n : ℝ)) (-Real.log (1 - x)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using hHasShift
  have hsumm : Summable (fun n : ℕ => x ^ n / (n : ℝ)) := hHas.summable
  have htsum : ∑' n : ℕ, x ^ n / (n : ℝ) = -Real.log (1 - x) := hHas.tsum_eq
  -- `1 - e^{-a} ≥ a/2` for `0 < a ≤ 1`
  have hb1 : Real.exp (-a) ≤ 1/(1+a) := by
    rw [Real.exp_neg]
    simpa [one_div, add_comm] using one_div_le_one_div_of_le (show (0:ℝ) < 1 + a by linarith)
      (show (1:ℝ) + a ≤ Real.exp a by linarith [Real.add_one_le_exp a])
  have hmain : a/2 ≤ 1 - Real.exp (-a) := by
    have h2 : a/(1+a) ≤ 1 - Real.exp (-a) := by
      have h3 : 1 - 1/(1+a) = a/(1+a) := by
        field_simp
        ring
      linarith
    have h4 : a/2 ≤ a/(1+a) := by
      have h5 : 0 ≤ a/(1+a) - a/2 := by
        have he : a/(1+a) - a/2 = a*(1-a)/(2*(1+a)) := by
          field_simp
          ring
        rw [he]
        exact div_nonneg (mul_nonneg ha.le (by linarith)) (by positivity)
      linarith
    linarith
  have hmain' : a/2 ≤ 1 - x := by rw [hxdef]; exact hmain
  have h1x : 0 < 1 - x := by linarith
  have hle : 1/(1-x) ≤ 2/a := by
    rw [div_le_div_iff₀ h1x ha]
    linarith
  calc ∑ n ∈ Finset.Icc 1 N, Real.exp (-(a * n)) / (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, x ^ n / (n : ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        congr 2
        rw [show -(a * (n:ℝ)) = (n:ℝ) * (-a) by ring, Real.exp_nat_mul, ← hxdef]
    _ ≤ ∑' n : ℕ, x ^ n / (n : ℝ) := Summable.sum_le_tsum _
        (fun i _ => div_nonneg (pow_nonneg hx0.le i) (Nat.cast_nonneg i)) hsumm
    _ = -Real.log (1 - x) := htsum
    _ = Real.log (1/(1-x)) := by rw [one_div, Real.log_inv]
    _ ≤ Real.log (2/a) := Real.log_le_log (by positivity) hle

theorem gfunWeightFacts (X U' : ℝ) (hU' : 0 < U') (hX : 1 ≤ X) (hle : U' ≤ X) :
    (∀ n : ℕ, 0 ≤ Work.ZeroDensity.LogFree.gfun X U' n) ∧
    (∀ n : ℕ, 1 ≤ n → Work.ZeroDensity.LogFree.gfun X U' (n + 1) / ((n : ℝ) + 1)
      ≤ Work.ZeroDensity.LogFree.gfun X U' n / (n : ℝ)) ∧
    (∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.LogFree.gfun X U' n / (n : ℝ)
      ≤ Real.log (2 * X) + 2) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  -- the antitone form of the middle statement, in `gfun` notation
  have hdivanti : ∀ s t : ℝ, 0 < s → s ≤ t →
      (Real.exp (-(t / X)) - Real.exp (-(t / U'))) / t ≤
        (Real.exp (-(s / X)) - Real.exp (-(s / U'))) / s := by
    intro s t hs hst
    have h := expNegDiv_antitone_gfun (show (0:ℝ) ≤ 1/X by positivity)
      (one_div_le_one_div_of_le hU' hle) hs hst
    simpa only [one_div_mul_eq_div] using h
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [gfun, sub_nonneg]
    exact Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_left (by positivity) hU' hle))
  · intro n hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have h := hdivanti (n:ℝ) ((n:ℝ)+1) hnpos (by linarith)
    simpa only [gfun, Nat.cast_add, Nat.cast_one] using h
  · intro N
    have ha : 0 < 1/X := by positivity
    have ha1 : 1/X ≤ 1 := by
      rw [div_le_one hX0]
      exact hX
    have hsum' := sum_expNegDiv_le_gfun (a := 1/X) ha ha1 N
    have hstep : ∑ n ∈ Finset.Icc 1 N, gfun X U' n / (n:ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 N, Real.exp (-((1/X) * (n:ℝ))) / (n:ℝ) := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by
        have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        exact_mod_cast this
      rw [gfun]
      rw [show (n:ℝ)/X = (1/X) * (n:ℝ) by ring,
        show (n:ℝ)/U' = (1/U') * (n:ℝ) by ring]
      rw [sub_div]
      exact sub_le_self _ (div_nonneg (Real.exp_pos _).le (by linarith))
    calc ∑ n ∈ Finset.Icc 1 N, gfun X U' n / (n:ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 N, Real.exp (-((1/X) * (n:ℝ))) / (n:ℝ) := hstep
      _ ≤ Real.log (2 / (1/X)) := hsum'
      _ = Real.log (2 * X) := by rw [div_eq_mul_inv, one_div, inv_inv]
      _ ≤ Real.log (2 * X) + 2 := le_add_of_nonneg_right (by norm_num)

end Work.ZeroDensity.LogFree
