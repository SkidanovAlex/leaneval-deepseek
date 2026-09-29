import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_mul
import Submission.Commons.FieldTheory.RatFunc.ordInfT_div
import Submission.Commons.FieldTheory.RatFunc.ordInfT_eq_top_iff
import Submission.Commons.FieldTheory.RatFunc.intDegree_pow

open Polynomial

namespace Commons.FieldTheory.RatFunc

/-- `intDegree` is additive for integer powers of a nonzero rational function. -/
private lemma intDegree_zpow {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) (n : ℤ) :
    (x ^ n).intDegree = n * x.intDegree := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, intDegree_pow hx m]
  · rw [zpow_neg, zpow_natCast, RatFunc.intDegree_inv, intDegree_pow hx m]
    push_cast; ring

/-- `ordInfT` is additive for integer powers of a nonzero rational function. -/
private lemma ordInfT_zpow {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) (n : ℤ) :
    ordInfT (x ^ n) = (n : WithTop ℤ) * ordInfT x := by
  rw [ordInfT_eq_coe_intDegree (zpow_ne_zero n hx), ordInfT_eq_coe_intDegree hx,
    intDegree_zpow hx n, WithTop.coe_mul]

/-- **Leading term at `∞` of a rational function of degree `0`.**  If `z ≠ 0` and
`ordInfT z = 0` then the leading coefficient of `z` at `∞` is
`r = (z.num).leadingCoeff / (z.denom).leadingCoeff ≠ 0`, and either `z` is the constant `r`, or
the residual `z - r` has order at most `-1` at `∞`.  This is the `N = 0` case of
`ordInfT_exists_leading_term_corrected`. -/
private lemma ordInfT_exists_leading_term_corrected_zero {K : Type*} [Field K] {z : RatFunc K}
    (hz : z ≠ 0) (hz0 : ordInfT z = 0) :
    ∃ r : K, r ≠ 0 ∧ (z = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r) ∨
      ordInfT (z - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r))
        ≤ ((-1 : ℤ) : WithTop ℤ)) := by
  have hp : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hq : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hmz : (Polynomial.natDegree z.num : ℤ) - (Polynomial.natDegree z.denom : ℤ) = 0 := by
    have h : (RatFunc.intDegree z : WithTop ℤ) = 0 := by
      rw [← ordInfT_eq_coe_intDegree hz]; exact hz0
    have h' : RatFunc.intDegree z = 0 := by simpa using h
    simpa [RatFunc.intDegree] using h'
  have hm : Polynomial.natDegree z.num = Polynomial.natDegree z.denom := by omega
  -- The candidate leading coefficient at `∞`.
  set r : K := z.num.leadingCoeff / z.denom.leadingCoeff with hrdef
  have hr : r ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
    (Polynomial.leadingCoeff_ne_zero.mpr hq)
  refine ⟨r, hr, ?_⟩
  -- The residual numerator `P = num - r·denom`; its two leading terms cancel.
  set P : Polynomial K := z.num - Polynomial.C r * z.denom with hPdef
  have hnum : z.num = Polynomial.C r * z.denom →
      z = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r) := by
    intro hnum
    conv_lhs => rw [← RatFunc.num_div_denom z]
    rw [hnum, map_mul]
    exact mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero hq)
  by_cases hP : P = 0
  · -- The residual vanishes: `z` is the constant `r`.
    left
    apply hnum
    have : z.num - Polynomial.C r * z.denom = 0 := by rw [← hPdef]; exact hP
    exact sub_eq_zero.mp this
  · -- The residual is nonzero with strictly smaller degree.
    right
    have hzcr : z - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        = algebraMap (Polynomial K) (RatFunc K) P
            / algebraMap (Polynomial K) (RatFunc K) z.denom := by
      conv_lhs => rw [← RatFunc.num_div_denom z]
      rw [hPdef, map_sub, map_mul, sub_div,
        mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero hq)]
    have hPne : P ≠ 0 := hP
    have hCr : Polynomial.C r * z.denom ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr hr) hq
    -- The two polynomials `C r * denom` and `num` have the same leading coefficient.
    have hlc : (Polynomial.C r * z.denom).leadingCoeff = z.num.leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul' (by rw [Polynomial.leadingCoeff_C]; exact mul_ne_zero hr (Polynomial.leadingCoeff_ne_zero.mpr hq)), Polynomial.leadingCoeff_C, hrdef, div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hq)]
    have hd : Polynomial.degree (Polynomial.C r * z.denom) = Polynomial.degree z.num := by
      rw [Polynomial.degree_eq_natDegree hCr, Polynomial.degree_eq_natDegree hp,
        Polynomial.natDegree_C_mul hr, hm]
    have hdeg_lt : Polynomial.degree P < Polynomial.degree (Polynomial.C r * z.denom) := by
      rw [hPdef]
      have h := Polynomial.degree_sub_lt_left hd.symm hp hlc.symm
      rwa [← hd] at h
    have hPdeg : Polynomial.natDegree P < Polynomial.natDegree z.denom := by
      have h := Polynomial.natDegree_lt_natDegree hPne hdeg_lt
      rwa [Polynomial.natDegree_C_mul hr] at h
    have hval : ordInfT (algebraMap (Polynomial K) (RatFunc K) P
          / algebraMap (Polynomial K) (RatFunc K) z.denom)
        = (((Polynomial.natDegree P : ℤ) - (Polynomial.natDegree z.denom : ℤ)) : WithTop ℤ) := by
      rw [ordInfT_eq_coe_intDegree
            (div_ne_zero (RatFunc.algebraMap_ne_zero hPne) (RatFunc.algebraMap_ne_zero hq)),
        RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hPne) (RatFunc.algebraMap_ne_zero hq),
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
      norm_cast
    rw [hzcr, hval]
    have hle : ((Polynomial.natDegree P : ℤ) - (Polynomial.natDegree z.denom : ℤ)) ≤ (-1 : ℤ) := by
      have : (Polynomial.natDegree P : ℤ) < (Polynomial.natDegree z.denom : ℤ) := by
        exact_mod_cast hPdeg
      linarith
    exact WithTop.coe_le_coe.mpr hle

/-- **Corrected form of `ordInfT_exists_leading_term`**: every nonzero rational function has a leading term at `∞`.

Let `x ≠ 0` in `K(X)` and `N = ordInfT x` (the *degree* of `x` at infinity,
`FieldTheory/RatFunc/ordInfT_def`: `N = x.num.natDegree - x.denom.natDegree`).  Then the leading
term of `x` at `∞` is `r·X^N` with `r = (x.num).leadingCoeff / (x.denom).leadingCoeff ≠ 0`, and
either `x` is *exactly* that monomial, or the residual `x - r·X^N` has order at most `N - 1` at `∞`.
The exceptional case cannot be removed: for `x = r·X^N` the residual is `0` and
`ordInfT 0 = ⊤ ≰ (N-1 : WithTop ℤ)`.

Warning (this is why the original statement failed): at `∞` the function `ordInfT` is
*degree*-like (`ordInfT (f+g) ≤ max`), so the residual has *strictly smaller* order — the opposite
of the situation at a finite point `α`, where `exists_leading_term` proves
`(N+1 : ℤ) ≤ ordAtT α (b - r·(X-α)^N)`.

Proof sketch: multiply by `X^(-N)` to reduce to the case `N = 0` (ordInfT is additive on nonzero
arguments).  So let `z ≠ 0` with `ordInfT z = 0`, `z = p/q`, `natDegree p = natDegree q = m`, and
`r = p.leadingCoeff / q.leadingCoeff ≠ 0`.  Then `z - r = (p - C r * q)/q`; either `p - C r * q = 0`
(giving `z = r`), or `natDegree (p - C r * q) < m` (the two leading terms cancel because
`leadingCoeff (C r * q) = r * q.leadingCoeff = p.leadingCoeff`), giving
`ordInfT (z - r) ≤ (m-1) - m = -1`.  Multiplying back by `X^N` gives the claim. -/
theorem ordInfT_exists_leading_term_corrected {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0)
    (N : ℤ) (hN : Commons.FieldTheory.RatFunc.ordInfT x = (N : WithTop ℤ)) :
    ∃ r : K, r ≠ 0 ∧
      (x = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
            * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ N ∨
        Commons.FieldTheory.RatFunc.ordInfT (x - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
            * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ N)
          ≤ ((N - 1 : ℤ) : WithTop ℤ)) := by
  -- Reduce to the degree-zero case by dividing by `X^N`.
  set t : RatFunc K := algebraMap (Polynomial K) (RatFunc K) Polynomial.X with htdef
  have ht : t ≠ 0 := by rw [htdef]; exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have htN : t ^ N ≠ 0 := zpow_ne_zero N ht
  have htN_ord : ordInfT (t ^ N) = (N : WithTop ℤ) := by
    rw [ordInfT_zpow ht N]
    have : ordInfT t = (1 : WithTop ℤ) := by
      rw [htdef, ordInfT_eq_coe_intDegree (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero),
        RatFunc.intDegree_polynomial, Polynomial.natDegree_X]
      norm_num
    rw [this, mul_one]
  set z : RatFunc K := x / t ^ N with hzdef
  have hz : z ≠ 0 := div_ne_zero hx htN
  have hz0 : ordInfT z = 0 := by
    rw [hzdef, ordInfT_div hx htN, hN, htN_ord]
    simp
  obtain ⟨r, hr, hcase⟩ := ordInfT_exists_leading_term_corrected_zero hz hz0
  refine ⟨r, hr, ?_⟩
  rcases hcase with hzc | hzle
  · -- `z` is the constant `r`, so `x = r · X^N`.
    left
    have hxeq : x = z * t ^ N := by rw [hzdef, div_mul_cancel₀ x htN]
    rw [hxeq, hzc, htdef]
  · -- The residual `z - r` has order at most `-1`; multiply back by `X^N`.
    right
    have hzcr : z - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r) ≠ 0 := by
      intro h0
      have htop : ordInfT (z - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)) = ⊤ := by
        rw [h0]; simp [ordInfT]
      rw [htop] at hzle
      exact absurd hzle (not_le.mpr (WithTop.coe_lt_top (-1)))
    have hxeq : x - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ N
        = (z - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)) * t ^ N := by
      rw [htdef, hzdef, sub_mul, div_mul_cancel₀ x htN]
    rw [hxeq, ordInfT_mul hzcr htN, htN_ord]
    calc ordInfT (z - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)) + (N : WithTop ℤ)
        ≤ ((-1 : ℤ) : WithTop ℤ) + (N : WithTop ℤ) := add_le_add hzle le_rfl
      _ = ((N - 1 : ℤ) : WithTop ℤ) := by rw [← WithTop.coe_add]; congr 1; ring

end Commons.FieldTheory.RatFunc
