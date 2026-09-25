import Mathlib.Algebra.Order.Star.Real

/-!
# Monotonicity bracket for the `caXi2_lower` chain

This file proves `Commons.Analysis.Log.caXi2_lower_bracket_mono`, the little
monotonicity comparison used in the Lagarias-criterion development to compare
the "bracket" at `s` with the one at `smax`.

Writing `A := L√2/(4p³)`, `η(σ) := √2σ/(2p)`, `φ(σ) := σ/(1+η(σ))`, the right
hand side is `A·(φ(smax) - φ(s))` and the elementary identity
`smax(1+η(s)) - s(1+η(smax)) = smax - s` turns it into
`A·(smax - s)/((1+etamax)(1+eta))`.  The left hand side is at most
`Dup·(smax² - s²)/2 = (smax - s)·Dup·(smax+s)/2`, so everything reduces to the
single numerical bound `Dup*smax*(1+etamax)²*4p³ ≤ L√2`, which holds with an
enormous margin under the stated hypotheses.
-/

set_option linter.unusedVariables false

namespace Commons.Analysis.Log

/-- The algebraic core: if `Dup*smax*(1+etamax)^2*(4*p^3) ≤ L√2` then the
bracket inequality holds.  (Positivity of the (relative) denominators is all
that is needed; the numerical content is isolated in `bracket_num`.) -/
private lemma bracket_aux (L p s smax eta etamax Dup : ℝ)
    (hp : 0 < p) (hs : 0 ≤ s) (hss : s ≤ smax)
    (heta : eta = Real.sqrt 2 * s/(2*p)) (hetamax : etamax = Real.sqrt 2 * smax/(2*p))
    (hDup0 : 0 ≤ Dup)
    (hnum : Dup*smax*(1+etamax)^2*(4*p^3) ≤ L*Real.sqrt 2) :
    (smax^2 - s^2)*Dup/2 - (smax^4 - s^4)*Dup/3
      ≤ smax*L*Real.sqrt 2/(4*p^3*(1+etamax)) - s*L*Real.sqrt 2/(4*p^3*(1+eta)) := by
  have hsmax_nn : 0 ≤ smax := le_trans hs hss
  have hq : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have heta_nn : 0 ≤ eta := by rw [heta]; positivity
  have hetamax_nn : 0 ≤ etamax := by rw [hetamax]; positivity
  have heta_le : eta ≤ etamax := by
    rw [heta, hetamax]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hss hq) (by positivity : (0:ℝ) ≤ 2*p)
  have h1e_pos : 0 < 1 + etamax := by linarith
  have h1s_pos : 0 < 1 + eta := by linarith
  have h1s_le : 1 + eta ≤ 1 + etamax := by linarith
  have hp3pos : 0 < 4*p^3 := by positivity
  -- the right hand side, factored through the elementary identity
  have hW : smax*L*Real.sqrt 2/(4*p^3*(1+etamax)) - s*L*Real.sqrt 2/(4*p^3*(1+eta))
      = (smax - s) * (L*Real.sqrt 2/(4*p^3*(1+etamax)*(1+eta))) := by
    rw [heta, hetamax]
    have e : (0:ℝ) < 1 + Real.sqrt 2 * smax / (2*p) := by positivity
    have e2 : (0:ℝ) < 1 + Real.sqrt 2 * s / (2*p) := by positivity
    field_simp
    ring
  have hA : Dup*smax ≤ L*Real.sqrt 2/(4*p^3*(1+etamax)^2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*p^3*(1+etamax)^2)]
    nlinarith [hnum]
  have hA' : Dup*smax*(4*p^3*(1+etamax)^2) ≤ L*Real.sqrt 2 := by
    rw [← le_div_iff₀ (by positivity : (0:ℝ) < 4*p^3*(1+etamax)^2)]
    exact hA
  have hB : Dup*(smax+s)/2 ≤ L*Real.sqrt 2/(4*p^3*(1+etamax)*(1+eta)) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*p^3*(1+etamax)*(1+eta))]
    have hle1 : Dup*(smax+s)/2 ≤ Dup*smax := by
      have := mul_nonneg hDup0 (sub_nonneg.mpr hss)
      nlinarith
    have hDupSmax_nn : 0 ≤ Dup*smax := mul_nonneg hDup0 hsmax_nn
    have hle2 : 4*p^3*(1+etamax)*(1+eta) ≤ 4*p^3*(1+etamax)^2 := by
      have h3 : 4*p^3*(1+etamax)*(1+eta) ≤ 4*p^3*(1+etamax)*(1+etamax) :=
        mul_le_mul_of_nonneg_left h1s_le (by positivity)
      nlinarith [h3]
    have step1 : Dup*(smax+s)/2 * (4*p^3*(1+etamax)*(1+eta))
        ≤ Dup*smax*(4*p^3*(1+etamax)*(1+eta)) :=
      mul_le_mul_of_nonneg_right hle1 (by positivity)
    have step2 : Dup*smax*(4*p^3*(1+etamax)*(1+eta))
        ≤ Dup*smax*(4*p^3*(1+etamax)^2) :=
      mul_le_mul_of_nonneg_left hle2 hDupSmax_nn
    linarith [hA']
  have hLHS_le : (smax^2 - s^2)*Dup/2 - (smax^4 - s^4)*Dup/3 ≤ Dup*(smax^2 - s^2)/2 := by
    have h4 : s^4 ≤ smax^4 := pow_le_pow_left₀ hs hss 4
    have hpos : 0 ≤ (smax^4 - s^4)*Dup := mul_nonneg (sub_nonneg.mpr h4) hDup0
    nlinarith [hpos]
  have hfac2 : Dup*(smax^2 - s^2)/2 = (smax - s)*(Dup*(smax+s)/2) := by ring
  rw [hW] at *
  rw [hfac2] at hLHS_le
  have hmul : (smax - s)*(Dup*(smax+s)/2)
      ≤ (smax - s)*(L*Real.sqrt 2/(4*p^3*(1+etamax)*(1+eta))) :=
    mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hss)
  linarith [hLHS_le, hmul]

/-- The numerical bound `Dup*smax*(1+etamax)^2*(4*p^3) ≤ L√2` under the
concrete constants of the `caXi2_lower` development.  All bounds are extremely
loose (`≈2.86·(L+2c) ≤ L³` against `L³√2`), so a coarse chain suffices. -/
private lemma bracket_num (L p s smax eta etamax Dup : ℝ)
    (hL : 7.333 ≤ L) (hp : 0 < p) (hp1 : p ≤ 1) (hs : 0 < s) (hss : s ≤ smax)
    (heta : eta = Real.sqrt 2 * s/(2*p)) (hetamax : etamax = Real.sqrt 2 * smax/(2*p))
    (hDup : Dup ≤ (L + 2*(3465736/10^7))/2) (hDup0 : 0 ≤ Dup)
    (hsmax : smax * L^2 ≤ (117252/10^5)^2)
    (heub : etamax ≤ (141422/10^5)*((117252/10^5)^2)/(2*(1 - (3465736/10^7)/7.333)*(7.333)^2)) :
    Dup*smax*(1+etamax)^2*(4*p^3) ≤ L*Real.sqrt 2 := by
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hsmax_nn : 0 ≤ smax := le_trans hs.le hss
  have hS2 : ((117252:ℝ)/10^5)^2 ≤ 11/8 := by norm_num
  have hS2nn : 0 ≤ ((117252:ℝ)/10^5)^2 := by norm_num
  have hE1 : etamax ≤ 1/50 := by
    have hbig : (141422:ℝ)/10^5 * ((117252:ℝ)/10^5)^2
        /(2*(1 - (3465736:ℝ)/10^7/7.333)*(7.333)^2) ≤ 1/50 := by norm_num
    linarith
  have hEnn : 0 ≤ etamax := by rw [hetamax]; positivity
  have hK : (1+etamax)^2 ≤ (51/50)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith : 1+etamax ≤ 51/50) 2
  have hp3le : p^3 ≤ 1 := pow_le_one₀ hp.le hp1
  have hp4 : 4*p^3 ≤ 4 := by nlinarith [hp3le]
  have hq1 : (1:ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hds : Dup*smax*L^2 ≤ Dup*((117252:ℝ)/10^5)^2 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsmax hDup0
  have hmain : (L + 2*((3465736:ℝ)/10^7))/2 * (11/8) * (51/50)^2 * 4 ≤ L^3 * Real.sqrt 2 := by
    have hL2 : (7.333:ℝ)^2 ≤ L^2 := by nlinarith
    have hL3low : (7.333:ℝ)^2 * L ≤ L^3 := by
      have := mul_le_mul_of_nonneg_left hL2 hLnn
      nlinarith [this]
    have hL3q : L^3 ≤ L^3 * Real.sqrt 2 := by
      have := mul_le_mul_of_nonneg_left hq1 (pow_nonneg hLnn 3)
      nlinarith [this]
    have heq : (L + 2*((3465736:ℝ)/10^7))/2 * (11/8) * (51/50)^2 * 4
        = (28611/10000)*(L + 2*((3465736:ℝ)/10^7)) := by ring
    rw [heq]
    nlinarith [hL, hL3low, hL3q]
  have key : Dup*smax*(1+etamax)^2*(4*p^3)*L^2 ≤ L^3*Real.sqrt 2 := by
    calc Dup*smax*(1+etamax)^2*(4*p^3)*L^2
        = (Dup*smax*L^2)*((1+etamax)^2*(4*p^3)) := by ring
      _ ≤ (Dup*((117252:ℝ)/10^5)^2)*((1+etamax)^2*(4*p^3)) :=
            mul_le_mul_of_nonneg_right hds (by positivity)
      _ ≤ (Dup*((117252:ℝ)/10^5)^2)*((51/50)^2*4) := by
            have h1n : 0 ≤ Dup*((117252:ℝ)/10^5)^2 := by positivity
            have h2 : (1+etamax)^2*(4*p^3) ≤ (51/50)^2*4 := by
              calc (1+etamax)^2*(4*p^3) ≤ (51/50)^2 * (4*p^3) :=
                    mul_le_mul_of_nonneg_right hK (by positivity)
                _ ≤ (51/50)^2 * 4 := mul_le_mul_of_nonneg_left hp4 (by norm_num)
            exact mul_le_mul_of_nonneg_left h2 h1n
      _ ≤ ((L + 2*((3465736:ℝ)/10^7))/2 * (11/8)) * ((51/50)^2*4) := by
            have h3 : Dup*((117252:ℝ)/10^5)^2 ≤ ((L + 2*((3465736:ℝ)/10^7))/2)*(11/8) := by
              calc Dup*((117252:ℝ)/10^5)^2
                    ≤ ((L + 2*((3465736:ℝ)/10^7))/2)*((117252:ℝ)/10^5)^2 :=
                      mul_le_mul_of_nonneg_right hDup hS2nn
                _ ≤ ((L + 2*((3465736:ℝ)/10^7))/2)*(11/8) :=
                      mul_le_mul_of_nonneg_left hS2 (by positivity)
            exact mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ L^3*Real.sqrt 2 := by nlinarith [hmain]
  have hL2pos : 0 < L^2 := by positivity
  have heq2 : L^3*Real.sqrt 2/L^2 = L*Real.sqrt 2 := by
    field_simp
  have hfin : Dup*smax*(1+etamax)^2*(4*p^3) ≤ L^3*Real.sqrt 2/L^2 :=
    (le_div_iff₀ hL2pos).mpr key
  rw [heq2] at hfin
  exact hfin

theorem caXi2_lower_bracket_mono (L p s smax eta etamax Dup : ℝ)
    (hL : 7.333 ≤ L) (hp : 0 < p) (hp1 : p ≤ 1) (hs : 0 < s) (hss : s ≤ smax)
    (heta : eta = Real.sqrt 2 * s/(2*p)) (hetamax : etamax = Real.sqrt 2 * smax/(2*p))
    (hDup : Dup ≤ (L + 2*(3465736/10^7))/2) (hDup0 : 0 ≤ Dup)
    (hsmax : smax * L^2 ≤ (117252/10^5)^2)
    (heub : etamax ≤ (141422/10^5)*((117252/10^5)^2)/(2*(1 - (3465736/10^7)/7.333)*(7.333)^2)) :
    (smax^2 - s^2)*Dup/2 - (smax^4 - s^4)*Dup/3
      ≤ smax*L*Real.sqrt 2/(4*p^3*(1+etamax)) - s*L*Real.sqrt 2/(4*p^3*(1+eta)) := by
  have hnum := bracket_num L p s smax eta etamax Dup hL hp hp1 hs hss heta hetamax hDup hDup0 hsmax heub
  exact bracket_aux L p s smax eta etamax Dup hp hs.le hss heta hetamax hDup0 hnum

end Commons.Analysis.Log