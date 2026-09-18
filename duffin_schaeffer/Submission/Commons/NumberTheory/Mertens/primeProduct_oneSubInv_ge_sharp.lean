import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.primeRecips_loglog_diff
import Submission.Commons.NumberTheory.Mertens.logDiv_le_log_sub
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum
import Submission.Commons.NumberTheory.Mertens.logDiv_ge_log_sub_sharp

namespace Commons.NumberTheory.Mertens

open Finset Real MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Elementary two-sided bounds for `logDiv` -/

/-- Real version of the first-Mertens upper bound: for `t ≥ 100`,
`Σ_{p ≤ t} (log p)/p ≤ log t - 0.3`. -/
private lemma logDiv_le_log_sub_real (t : ℝ) (ht : 100 ≤ t) :
    logDiv t ≤ Real.log t - 0.3 := by
  have hfloor : 100 ≤ ⌊t⌋₊ := by
    have h := Nat.floor_mono ht
    norm_num at h
    exact h
  have hle := logDiv_le_log_sub ⌊t⌋₊ hfloor
  have hlogle : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t :=
    Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
  have hlogdiv : logDiv t
      = ∑ p ∈ (⌊t⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ) := rfl
  rw [hlogdiv]; linarith

/-! ## The decomposition `logRatioSum = primeRecips + logRatioCorrSum` -/

private lemma logRatioSum_eq (x : ℝ) :
    logRatioSum x = primeRecips x + logRatioCorrSum x := by
  simp only [logRatioSum, primeRecips, logRatioCorrSum, corrTerm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

private lemma logRatioCorrSum_mono : Monotone logRatioCorrSum := by
  intro x y hxy
  simp only [logRatioCorrSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (Nat.floor_mono hxy), hp.2⟩
  · intro p hp _
    exact corrTerm_nonneg (Nat.mem_primesLE.mp hp).2

/-! ## Interval integrability of the elementary kernels -/

private lemma intervalIntegrable_inv_div_log' {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x X := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  rw [Set.uIcc_of_le hxX] at hz
  have hz2 : 2 ≤ z := le_trans hx hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  exact ((continuousAt_id.inv₀ hz0).div (Real.continuousAt_log hz0) hlogz).continuousWithinAt

private lemma intervalIntegrable_inv_div_log_sq' {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x X := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  rw [Set.uIcc_of_le hxX] at hz
  have hz2 : 2 ≤ z := le_trans hx hz.1
  have hz0 : z ≠ 0 := by linarith
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith
  exact ((continuousAt_id.inv₀ hz0).div ((Real.continuousAt_log hz0).pow 2)
    (pow_ne_zero 2 hlogz)).continuousWithinAt

/-! ## The main auxiliary estimate -/

/-- For `x ≥ 100`,
`logRatioSum x - log log x - γ ≤ (73/50) / log x`. -/
private lemma logRatioSum_sub_loglog_sub_gamma_le (x : ℝ) (hx : 100 ≤ x) :
    logRatioSum x - Real.log (Real.log x) - Real.eulerMascheroniConstant
      ≤ (73 / 50) / Real.log x := by
  have hx2 : 2 ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  set B : ℝ := -(3 / 10) with hB
  -- pointwise bounds for `s t = logDiv t - log t - B`
  have hs_le : ∀ t : ℝ, 100 ≤ t → logDiv t - Real.log t - B ≤ 0 := by
    intro t ht
    have := logDiv_le_log_sub_real t ht
    simp only [hB]; linarith
  have hs_ge : ∀ t : ℝ, 100 ≤ t → -(73 / 50) ≤ logDiv t - Real.log t - B := by
    intro t ht
    have h1002 : 2 ≤ t := by linarith
    have := logDiv_ge_log_sub_sharp t h1002
    simp only [hB]; linarith
  -- key finite-`X` inequality
  have key : ∀ X : ℝ, x ≤ X →
      logRatioSum x - Real.log (Real.log x)
        - (logRatioSum X - Real.log (Real.log X)) ≤ (73 / 50) / Real.log x := by
    intro X hxX
    have hX100 : 100 ≤ X := le_trans hx hxX
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hident := primeRecips_loglog_diff (x := x) (X := X) (B₁ := B) hx2 hxX
    -- integrability of the integrand and of the comparison kernel
    have hF : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2))
        volume x X := intervalIntegrable_logDiv_div_id_log_sq_gen hx2 hxX
    have hU : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x X :=
      intervalIntegrable_inv_div_log' hx2 hxX
    have hV : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x X :=
      intervalIntegrable_inv_div_log_sq' hx2 hxX
    have hg : IntervalIntegrable
        (fun t : ℝ => (logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2))
        volume x X := by
      refine IntervalIntegrable.congr ?_ (hF.sub hU |>.sub (hV.const_mul B))
      intro t ht
      rw [Set.uIoc_of_le hxX] at ht
      have ht2 : 2 ≤ t := le_trans hx2 (le_of_lt ht.1)
      have ht0 : t ≠ 0 := by linarith
      have hlogt : Real.log t ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> linarith
      field_simp
    -- pointwise bound on `-g`
    have hpt : ∀ t ∈ Set.Icc x X,
        -((logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2))
          ≤ (73 / 50) * (t⁻¹ / (Real.log t) ^ 2) := by
      intro t ht
      have ht100 : 100 ≤ t := le_trans hx ht.1
      have ht0 : (0 : ℝ) < t := by linarith
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
      have hden : 0 < t * (Real.log t) ^ 2 := by positivity
      have hsgt := hs_ge t ht100
      have hs' : -(logDiv t - Real.log t - B) ≤ 73 / 50 := by linarith
      have hrw : (73 / 50) * (t⁻¹ / (Real.log t) ^ 2)
          = (73 / 50) / (t * (Real.log t) ^ 2) := by
        field_simp
      have hneg : -((logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2))
          = (-(logDiv t - Real.log t - B)) / (t * (Real.log t) ^ 2) := by ring
      rw [hneg, hrw, div_le_div_iff_of_pos_right hden]
      exact hs'
    have hInt : -(∫ t in x..X, (logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2))
        ≤ (73 / 50) * (1 / Real.log x - 1 / Real.log X) := by
      rw [← intervalIntegral.integral_neg]
      have hmono := intervalIntegral.integral_mono_on hxX hg.neg
        (hV.const_mul (73 / 50)) hpt
      have hval : (∫ t in x..X, (73 / 50) * (t⁻¹ / (Real.log t) ^ 2))
          = (73 / 50) * (1 / Real.log x - 1 / Real.log X) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [integral_inv_div_log_sq hx1 (by linarith : (1 : ℝ) < X)]
        ring
      rw [hval] at hmono
      exact hmono
    -- combine
    have hbracket :
        (primeRecips x - Real.log (Real.log x)) - (primeRecips X - Real.log (Real.log X))
          = -(logDiv X - Real.log X - B) / Real.log X
            + (logDiv x - Real.log x - B) / Real.log x
            - ∫ t in x..X, (logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2) := by
      have h := hident
      field_simp at h ⊢
      linarith [h]
    have hterm1 : -(logDiv X - Real.log X - B) / Real.log X ≤ (73 / 50) / Real.log X := by
      have hs := hs_ge X hX100
      have hs' : -(logDiv X - Real.log X - B) ≤ 73 / 50 := by linarith
      have hneg : -(logDiv X - Real.log X - B) / Real.log X
          = (-(logDiv X - Real.log X - B)) / Real.log X := by ring
      rw [hneg, div_le_div_iff_of_pos_right hlogX]
      exact hs'
    have hterm2 : (logDiv x - Real.log x - B) / Real.log x ≤ 0 := by
      have hs := hs_le x hx
      rw [div_le_iff₀ hlogx]
      simpa using hs
    have hcorr : logRatioCorrSum x - logRatioCorrSum X ≤ 0 := by
      have := logRatioCorrSum_mono hxX
      linarith
    have hdecomp : logRatioSum x - Real.log (Real.log x)
        - (logRatioSum X - Real.log (Real.log X))
        = ((primeRecips x - Real.log (Real.log x)) - (primeRecips X - Real.log (Real.log X)))
          + (logRatioCorrSum x - logRatioCorrSum X) := by
      rw [logRatioSum_eq x, logRatioSum_eq X]
      ring
    rw [hdecomp, hbracket]
    have hsum : (73 / 50) / Real.log X + 0 + (73 / 50) * (1 / Real.log x - 1 / Real.log X)
        = (73 / 50) / Real.log x := by
      field_simp
      ring
    linarith [hterm1, hterm2, hInt, hcorr, hsum]
  -- take the limit `X → ∞`
  have hlim : Filter.Tendsto (fun X : ℝ =>
      logRatioSum x - Real.log (Real.log x) - (logRatioSum X - Real.log (Real.log X)))
      Filter.atTop (nhds (logRatioSum x - Real.log (Real.log x)
        - Real.eulerMascheroniConstant)) := by
    have hγ := sum_log_prime_ratio_real_tendsto
    exact tendsto_const_nhds.sub hγ
  refine le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨x, fun X hxX => key X hxX⟩)


/-! ## The target theorem -/

theorem primeProduct_oneSubInv_ge_sharp (y : ℕ) (hy : 100 ≤ y) :
    Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3 / 2) / Real.log (y : ℝ)) / Real.log (y : ℝ)
      ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := by
  have hyR : (100 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy1 : (1 : ℝ) < (y : ℝ) := by linarith
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  -- positivity of each factor and of the product
  have hfac : ∀ p ∈ Nat.primesLE y, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have h1 : (1 : ℝ) / 2 ≤ 1 - (p : ℝ)⁻¹ := by
      have := one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) hp2'
      rw [one_div] at this ⊢
      linarith
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) h1
  have hPpos : 0 < ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := Finset.prod_pos hfac
  -- logarithm of the product
  have hlogP : Real.log (∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹))
      = -logRatioSum (y : ℝ) := by
    have hfacne : ∀ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) ≠ 0 := fun p hp => ne_of_gt (hfac p hp)
    rw [Real.log_prod hfacne]
    have hsum : logRatioSum (y : ℝ)
        = ∑ p ∈ Nat.primesLE y, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
      unfold logRatioSum
      rw [Nat.floor_natCast]
    rw [hsum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
      linarith
    have h1 : 1 - (p : ℝ)⁻¹ = (((p : ℝ) / ((p : ℝ) - 1))⁻¹) := by
      field_simp
    rw [h1, Real.log_inv]
  -- the sharp estimate
  have hcap := logRatioSum_sub_loglog_sub_gamma_le (y : ℝ) hyR
  have hlogPge : -(Real.log (Real.log (y : ℝ)) + Real.eulerMascheroniConstant
        + (73 / 50) / Real.log (y : ℝ)) ≤ Real.log (∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)) := by
    rw [hlogP]; linarith [hcap]
  have hexp : Real.exp (-(Real.log (Real.log (y : ℝ)) + Real.eulerMascheroniConstant
        + (73 / 50) / Real.log (y : ℝ)))
      ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := by
    have := Real.exp_le_exp.mpr hlogPge
    rwa [Real.exp_log hPpos] at this
  -- simplify the exponent
  have hexpv : Real.exp (-(Real.log (Real.log (y : ℝ)) + Real.eulerMascheroniConstant
        + (73 / 50) / Real.log (y : ℝ)))
      = Real.exp (-Real.eulerMascheroniConstant)
          * Real.exp (-((73 / 50) / Real.log (y : ℝ))) / Real.log (y : ℝ) := by
    rw [show -(Real.log (Real.log (y : ℝ)) + Real.eulerMascheroniConstant
          + (73 / 50) / Real.log (y : ℝ))
        = -Real.log (Real.log (y : ℝ)) + -Real.eulerMascheroniConstant
          + -((73 / 50) / Real.log (y : ℝ)) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hlogy]
    ring
  rw [hexpv] at hexp
  -- compare `73/50 ≤ 3/2`
  have hstep : Real.exp (-(3 / 2) / Real.log (y : ℝ))
      ≤ Real.exp (-((73 / 50) / Real.log (y : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [show -((73 / 50) / Real.log (y : ℝ)) = (-(73 / 50)) / Real.log (y : ℝ) by ring]
    exact div_le_div_of_nonneg_right (by norm_num : -(3 / 2 : ℝ) ≤ -(73 / 50)) (le_of_lt hlogy)
  calc Real.exp (-Real.eulerMascheroniConstant)
        * Real.exp (-(3 / 2) / Real.log (y : ℝ)) / Real.log (y : ℝ)
      ≤ Real.exp (-Real.eulerMascheroniConstant)
        * Real.exp (-((73 / 50) / Real.log (y : ℝ))) / Real.log (y : ℝ) := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
        · exact le_of_lt hlogy
    _ ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := hexp

end

end Commons.NumberTheory.Mertens
