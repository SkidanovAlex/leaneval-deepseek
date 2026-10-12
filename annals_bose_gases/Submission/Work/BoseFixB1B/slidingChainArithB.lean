import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.slidingChainArithB` — the (pure-real) arithmetic of the sliding
# Bogoliubov chain

Holder: the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

## Why this module exists

The sliding Bogoliubov port — FS `lm:appbogolubov` at the sliding box, in the spelling
`Work.BoseFixB1B.SlidingBogPort` (`Submission/Work/BoseFixB1B/perBoxFTotalInterfaces.lean`) — is
the corpus's single named remaining *analytic* input, and it is what both routes to
`Work.BoseFixB1B.lowCountBound` bottom out in.  Its own module
(`Submission/Work/BoseFixB1B/slidingBogPort_holds.lean`) derives it from the proved chain
`Work.BoseFixB1S.chainIntegralQdep` and has **exactly one** gap: the private pure-real lemma
`slidingChainArith_local`.  This module proves that lemma (in the `hVX` spelling of that file), so
that the port's owner can close the port by replacing one `sorry` by an application of
`slidingChainArithB`.

## The mathematics (all steps elementary; the constants are free)

Write `n₁ := N+1`, `n₂ := N+2`, `p := π`.  With `D > 0`, `η ≥ 0`, `8K ≤ 1+η`, `2K_s PM = K D`,
`4K_sκ² ≤ C`, `0 ≤ S ≤ n₁`, `0 ≤ Xw ≤ κ²V`, `0 < X_p ≤ 1`, `c⁶ = (av⁶)⁻¹X_p⁹³⁶`,
`X_p³²³ = μ(av)³`, `V X_p⁴⁷¹ ≤ (av)³`, `C ≥ 4κ²K_s²av/(9p⁴(1+η)D)`, the claim is

  `0 ≤ ½(1+η)D(n₂n₁/V²)Xw − S Xw(c³K_s av/(3p²V) + 4n₂K_s PM/V²)
        + (C−4K_sκ²)av(μ + n₁/V)Q + C av μ`.

The last two terms are non-negative, and the two negative terms balance against the leading one:

* `4K_s PM = 2KD ≤ D(1+η)/4` (from `8K ≤ 1+η`), so the second negative term is at most half of the
  leading term;
* `c³ = X_p⁴⁶⁸/(av)³` (from `c⁶` and `c > 0`), hence `A := S Xw c³K_s av/(3p²V) ≤
  n₁XwK_sX_p⁴⁶⁸/(3p²(av)²V)`.

It remains to compare the surplus `≥ Xw n₁ n₂ D(1+η)/(4V²)` (which is `∝ D`) with `A`, and the two
remaining hypotheses settle it:

* if `4K_s av X_p⁻³ ≤ 3p²Dn₂(1+η)`, then — using `V c³ ≤ X_p⁻³`, the exact form of `V X_p⁴⁷¹ ≤
  (av)³` — one has `V c³K_s av/(3p²) ≤ Dn₂(1+η)/4`, so the leading term pays everything;
* otherwise `D < 4K_s av X_p⁻³/(3p²n₂(1+η))`, hence `C ≥ 4κ²K_s²av/(9p⁴(1+η)D) >
  κ²K_s n₂X_p³/(3p²)` and therefore `C av μ = C X_p³²³/(av)² > κ²K_s n₂X_p³²⁶/(3p²(av)²) ≥
  n₁κ²K_sX_p⁴⁶⁸/(3p²(av)²) ≥ A` (using `Xw ≤ κ²V` and `X_p ≤ 1`).
-/

noncomputable section

namespace Work.BoseFixB1B

open scoped Real

set_option autoImplicit false
set_option maxHeartbeats 1600000

private lemma pow471 (Xp : ℝ) : Xp ^ 471 = Xp ^ 468 * Xp ^ 3 := by ring

private lemma pow468 (Xp : ℝ) : Xp ^ 468 = Xp ^ 326 * Xp ^ 142 := by ring

private lemma pow326 (Xp : ℝ) : Xp ^ 326 = Xp ^ 3 * Xp ^ 323 := by ring

private lemma powsix (av : ℝ) : (av ^ 3)⁻¹ * (av ^ 3)⁻¹ = (av ^ 6)⁻¹ := by
  rw [← mul_inv]; ring

/-- **The arithmetic of the sliding Bogoliubov chain** (hypothesis shape of
`slidingChainArith_local` in `Submission/Work/BoseFixB1B/slidingBogPort_holds.lean`).  All
constants are free; the content is the trade-off described in the module docstring. -/
theorem slidingChainArithB {N : ℕ} {av V c Xp Xw S K Ks PM κ D η C μ Θ Q : ℝ}
    (hN : 1 ≤ N) (hav : 0 < av) (hV : 0 < V) (hD : 0 < D) (hμ : 0 < μ) (hc : 0 < c)
    (hKs : 0 < Ks) (hXw : 0 ≤ Xw) (hXp0 : 0 ≤ Xp) (hXp1 : Xp ≤ 1) (hκ : 0 ≤ κ) (hQ : 0 ≤ Q)
    (hS : S ≤ (N : ℝ) + 1) (hS0 : 0 ≤ S)
    (hΘ : Θ = 4 * c ^ 3 * V * Ks * av / (3 * Real.pi ^ 2 * (1 + η) * D))
    (hc6 : c ^ 6 = (av ^ 6)⁻¹ * Xp ^ 936)
    (hVX : V * Xp ^ 471 ≤ av ^ 3)
    (hXwle : Xw ≤ κ ^ 2 * V)
    (hXpPow : Xp ^ 323 = μ * av ^ 3)
    (hKsPM : 2 * Ks * PM = K * D) (hηK : 8 * K ≤ 1 + η) (hη0 : 0 ≤ η)
    (hCκ : 4 * Ks * κ ^ 2 ≤ C)
    (hCint : 4 * κ ^ 2 * Ks ^ 2 * av / (9 * Real.pi ^ 4 * (1 + η) * D) ≤ C) :
    0 ≤ (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
        - S * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)
            + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2)
        + (C - 4 * Ks * κ ^ 2) * av * (μ + (((N : ℝ) + 1) / V)) * Q
        + C * av * μ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hXppos : 0 < Xp := by
    by_contra h
    push Not at h
    have h0 : Xp = 0 := le_antisymm h hXp0
    rw [h0] at hXpPow
    simp only [zero_pow (by norm_num : (323 : ℕ) ≠ 0)] at hXpPow
    nlinarith [mul_pos hμ (pow_pos hav 3)]
  have hXp3 : 0 < Xp ^ 3 := by positivity
  have hη1 : 0 < 1 + η := by linarith
  have hn1 : 0 < (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hn2 : 0 < (N : ℝ) + 1 + 1 := by linarith
  have hn21 : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1 + 1) := by linarith
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  -- ## (1) `c³ = X_p⁴⁶⁸/(av)³`
  have hc3 : c ^ 3 = Xp ^ 468 * (av ^ 3)⁻¹ := by
    have hsq1 : (Xp ^ 468 * (av ^ 3)⁻¹) * (Xp ^ 468 * (av ^ 3)⁻¹) = c ^ 3 * c ^ 3 := by
      have h1 : (Xp ^ 468 * (av ^ 3)⁻¹) * (Xp ^ 468 * (av ^ 3)⁻¹)
          = Xp ^ 936 * ((av ^ 3)⁻¹ * (av ^ 3)⁻¹) := by ring
      rw [h1, powsix]
      have h3 : c ^ 3 * c ^ 3 = c ^ 6 := by ring
      rw [h3, hc6]
      ring
    have hprod : (Xp ^ 468 * (av ^ 3)⁻¹ - c ^ 3) * (Xp ^ 468 * (av ^ 3)⁻¹ + c ^ 3) = 0 := by
      nlinarith [hsq1]
    have hsum : 0 < Xp ^ 468 * (av ^ 3)⁻¹ + c ^ 3 := by
      have hc3pos : 0 < c ^ 3 := by positivity
      have hnn : 0 ≤ Xp ^ 468 * (av ^ 3)⁻¹ := by positivity
      linarith
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  -- ## (2) `c³ av = X_p⁴⁶⁸/(av)²`
  have hc3av : c ^ 3 * av = Xp ^ 468 * (av ^ 2)⁻¹ := by
    rw [hc3]
    field_simp
  -- ## (3) `V c³ ≤ X_p⁻³`
  have hVc3 : V * c ^ 3 ≤ (Xp ^ 3)⁻¹ := by
    rw [pow471] at hVX
    have hVX' : V * Xp ^ 468 * Xp ^ 3 ≤ av ^ 3 := by
      have : V * (Xp ^ 468 * Xp ^ 3) = V * Xp ^ 468 * Xp ^ 3 := by ring
      rwa [this] at hVX
    have h1 : V * Xp ^ 468 ≤ av ^ 3 / Xp ^ 3 := (le_div_iff₀ hXp3).mpr hVX'
    have h2 : V * Xp ^ 468 * (av ^ 3)⁻¹ ≤ (av ^ 3 / Xp ^ 3) * (av ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (av ^ 3 / Xp ^ 3) * (av ^ 3)⁻¹ = (Xp ^ 3)⁻¹ := by
      rw [div_eq_mul_inv]
      field_simp
    have h4 : V * (Xp ^ 468 * (av ^ 3)⁻¹) = V * Xp ^ 468 * (av ^ 3)⁻¹ := by ring
    rw [hc3, h4]
    exact le_trans h2 h3.le
  -- ## (4) `av μ = X_p³²³/(av)²`
  have havm : av * μ = Xp ^ 323 * (av ^ 2)⁻¹ := by
    rw [hXpPow]
    field_simp
  -- ## (5) the two credit terms are non-negative
  have hCt1 : 0 ≤ (C - 4 * Ks * κ ^ 2) * av * (μ + (((N : ℝ) + 1) / V)) * Q := by
    have h1 : 0 ≤ C - 4 * Ks * κ ^ 2 := by linarith [hCκ]
    have h3 : 0 ≤ μ + (((N : ℝ) + 1) / V) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav.le) h3) hQ
  have hCt2 : 0 ≤ C * av * μ := by
    have h1 : 0 ≤ C := by
      have : 0 ≤ Ks * κ ^ 2 := by positivity
      linarith [hCκ]
    exact mul_nonneg (mul_nonneg h1 hav.le) hμ.le
  -- ## (6) `4 K_s PM ≤ D(1+η)/4`
  have h4KsPM : 4 * Ks * PM ≤ D * (1 + η) / 4 := by
    have h4 : 4 * Ks * PM = 2 * (2 * Ks * PM) := by ring
    rw [h4, hKsPM]
    nlinarith [hηK, hD.le]
  -- ## (7) `B ≤ n₁ Xw n₂ D(1+η)/(4V²)`
  have hBle : S * Xw * (4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2)
      ≤ ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2)) := by
    have hcoef : 4 * Ks * PM / V ^ 2 ≤ D * (1 + η) / (4 * V ^ 2) := by
      rw [div_le_div_iff₀ hV2 (by positivity : (0 : ℝ) < 4 * V ^ 2)]
      nlinarith [h4KsPM]
    have hstep : S * Xw * (4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2)
        ≤ S * Xw * (((N : ℝ) + 1 + 1) * (D * (1 + η) / (4 * V ^ 2))) := by
      have hsh : 4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2
          = ((N : ℝ) + 1 + 1) * (4 * Ks * PM / V ^ 2) := by ring
      rw [hsh]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcoef (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1 + 1)))
        (by positivity : (0 : ℝ) ≤ S * Xw)
    have hfin : S * Xw * (((N : ℝ) + 1 + 1) * (D * (1 + η) / (4 * V ^ 2)))
        ≤ ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * (D * (1 + η) / (4 * V ^ 2))) := by
      have h4 : S * Xw ≤ ((N : ℝ) + 1) * Xw := mul_le_mul hS le_rfl hXw (by positivity)
      have hc : 0 ≤ ((N : ℝ) + 1 + 1) * (D * (1 + η) / (4 * V ^ 2)) := by positivity
      exact mul_le_mul_of_nonneg_right h4 hc
    have hshape : ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * (D * (1 + η) / (4 * V ^ 2)))
        = ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2)) := by ring
    linarith [hstep, hfin, hshape.le, hshape.ge]
  -- ## (8) the leading term dominates `B`
  have hT1B : 0 ≤ (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
      - S * Xw * (4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2) := by
    have heq2 : 2 * (((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2)))
        = (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw := by
      ring_nf
    have hT1nn : 0 ≤ (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw := by
      positivity
    linarith [hBle, heq2, hT1nn]
  -- ## (9) the two cases
  set A : ℝ := S * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)) with hAdef
  set B : ℝ := S * Xw * (4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2) with hBdef
  have hApay : 0 ≤ (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
      - A - B + C * av * μ := by
    by_cases hcase : 4 * Ks * av * (Xp ^ 3)⁻¹
        ≤ 3 * Real.pi ^ 2 * D * ((N : ℝ) + 1 + 1) * (1 + η)
    · -- ## case A: the mass row pays the `c³`-term
      have hAcle : 4 * V * c ^ 3 * Ks * av
          ≤ 3 * Real.pi ^ 2 * D * ((N : ℝ) + 1 + 1) * (1 + η) := by
        have h1 : 4 * V * c ^ 3 * Ks * av ≤ 4 * Ks * av * (Xp ^ 3)⁻¹ := by
          have h2 : V * c ^ 3 * (Ks * av) ≤ (Xp ^ 3)⁻¹ * (Ks * av) :=
            mul_le_mul_of_nonneg_right hVc3 (by positivity : 0 ≤ Ks * av)
          nlinarith [h2]
        linarith [h1, hcase]
      have hdiv : c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)
          ≤ ((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2) := by
        rw [div_le_div_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2 * V)
          (by positivity : (0 : ℝ) < 4 * V ^ 2)]
        have hmul := mul_le_mul_of_nonneg_right hAcle (by positivity : (0 : ℝ) ≤ V)
        linarith [hmul]
      have hA1 : A ≤ ((N : ℝ) + 1) * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)) := by
        rw [hAdef]
        have h1 : S * Xw ≤ ((N : ℝ) + 1) * Xw := mul_le_mul hS le_rfl hXw (by positivity)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have hA2 : ((N : ℝ) + 1) * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V))
          ≤ ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2)) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      have hB' : B ≤ ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2)) := by
        rw [hBdef]; exact hBle
      have heq : ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2))
            + ((N : ℝ) + 1) * Xw * (((N : ℝ) + 1 + 1) * D * (1 + η) / (4 * V ^ 2))
          = (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw := by
        field_simp
        try ring
      linarith [hA1, hA2, hB', heq.le, heq.ge, hCt2]
    · -- ## case B: the `C a μ` term pays the `c³`-term
      have hcaseB : 3 * Real.pi ^ 2 * ((N : ℝ) + 1 + 1) * (1 + η) * D
          < 4 * Ks * av * (Xp ^ 3)⁻¹ := by
        have := not_le.mp hcase
        linarith [this]
      -- (B1) `4κ²K_s²av ≤ C·9π⁴(1+η)D`, cleared
      have hCint' : 4 * κ ^ 2 * Ks ^ 2 * av
          ≤ C * (9 * Real.pi ^ 4 * (1 + η) * D) := by
        rw [div_le_iff₀ (by positivity : 0 < 9 * Real.pi ^ 4 * (1 + η) * D)] at hCint
        linarith [hCint]
      -- (B2) `C ≥ κ²K_s n₂ X_p³/(3π²)`
      have hCbig : κ ^ 2 * Ks * ((N : ℝ) + 1 + 1) * Xp ^ 3 / (3 * Real.pi ^ 2) ≤ C := by
        have hmul : κ ^ 2 * Ks * Xp ^ 3 * (3 * Real.pi ^ 2 * ((N : ℝ) + 1 + 1) * (1 + η) * D)
            ≤ 4 * κ ^ 2 * Ks ^ 2 * av := by
          have h1 := mul_le_mul_of_nonneg_left hcaseB.le (by positivity : 0 ≤ κ ^ 2 * Ks * Xp ^ 3)
          have h2 : κ ^ 2 * Ks * Xp ^ 3 * (4 * Ks * av * (Xp ^ 3)⁻¹) = 4 * κ ^ 2 * Ks ^ 2 * av := by
            field_simp
            try ring
          linarith [h1, h2.le, h2.ge]
        have hstep : κ ^ 2 * Ks * ((N : ℝ) + 1 + 1) * Xp ^ 3 / (3 * Real.pi ^ 2)
            ≤ 4 * κ ^ 2 * Ks ^ 2 * av / (9 * Real.pi ^ 4 * (1 + η) * D) := by
          rw [div_le_div_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)
            (by positivity : 0 < 9 * Real.pi ^ 4 * (1 + η) * D)]
          have hm := mul_le_mul_of_nonneg_right hmul (by positivity : (0 : ℝ) ≤ 3 * Real.pi ^ 2)
          linarith [hm]
        linarith [hstep, hCint]
      -- (B3) the power comparison `n₁ X_p⁴⁶⁸ ≤ n₂ X_p³ X_p³²³`
      have hXp142 : Xp ^ 142 ≤ 1 := pow_le_one₀ hXp0 hXp1
      have hkey2 : ((N : ℝ) + 1) * Xp ^ 468 ≤ ((N : ℝ) + 1 + 1) * Xp ^ 3 * Xp ^ 323 := by
        rw [pow468, pow326]
        have hm := mul_le_mul_of_nonneg_left hXp142
          (by positivity : 0 ≤ ((N : ℝ) + 1) * (Xp ^ 3 * Xp ^ 323))
        have hn := mul_le_mul_of_nonneg_right hn21 (by positivity : 0 ≤ Xp ^ 3 * Xp ^ 323)
        linarith [hm, hn]
      have hC3 : κ ^ 2 * Ks * ((N : ℝ) + 1 + 1) * Xp ^ 3 ≤ C * (3 * Real.pi ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_right hCbig (by positivity : (0 : ℝ) ≤ 3 * Real.pi ^ 2)
        have heq : κ ^ 2 * Ks * ((N : ℝ) + 1 + 1) * Xp ^ 3 / (3 * Real.pi ^ 2) * (3 * Real.pi ^ 2)
            = κ ^ 2 * Ks * ((N : ℝ) + 1 + 1) * Xp ^ 3 := by
          field_simp
        linarith [h1, heq.le, heq.ge]
      have hchain : ((N : ℝ) + 1) * Xp ^ 468 * (κ ^ 2 * Ks)
          ≤ (C * (3 * Real.pi ^ 2)) * Xp ^ 323 := by
        have hmult : ((N : ℝ) + 1) * Xp ^ 468 * (κ ^ 2 * Ks)
            ≤ ((N : ℝ) + 1 + 1) * Xp ^ 3 * Xp ^ 323 * (κ ^ 2 * Ks) :=
          mul_le_mul_of_nonneg_right hkey2 (by positivity)
        have hmult2 : ((N : ℝ) + 1 + 1) * Xp ^ 3 * Xp ^ 323 * (κ ^ 2 * Ks)
            ≤ (C * (3 * Real.pi ^ 2)) * Xp ^ 323 := by
          have hmm := mul_le_mul_of_nonneg_right hC3 (by positivity : (0 : ℝ) ≤ Xp ^ 323)
          linarith [hmm]
        exact le_trans hmult hmult2
      -- (B4) `A ≤ C a μ`
      have hA1 : A ≤ ((N : ℝ) + 1) * κ ^ 2 * Ks * Xp ^ 468 * (av ^ 2)⁻¹ / (3 * Real.pi ^ 2) := by
        rw [hAdef, le_div_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)]
        have hSW : S * Xw ≤ ((N : ℝ) + 1) * (κ ^ 2 * V) := mul_le_mul hS hXwle hXw (by positivity)
        have h1' : S * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)) * (3 * Real.pi ^ 2)
            ≤ ((N : ℝ) + 1) * (κ ^ 2 * V) * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V))
                * (3 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSW (by positivity))
            (by positivity)
        have h2' : ((N : ℝ) + 1) * (κ ^ 2 * V) * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V))
              * (3 * Real.pi ^ 2)
            = ((N : ℝ) + 1) * κ ^ 2 * Ks * Xp ^ 468 * (av ^ 2)⁻¹ := by
          have hca : c ^ 3 * Ks * av = (c ^ 3 * av) * Ks := by ring
          rw [hca, hc3av]
          field_simp
          try ring
        linarith [h1', h2'.le, h2'.ge]
      have hA2 : ((N : ℝ) + 1) * κ ^ 2 * Ks * Xp ^ 468 * (av ^ 2)⁻¹ / (3 * Real.pi ^ 2)
          ≤ C * (Xp ^ 323 * (av ^ 2)⁻¹) := by
        rw [div_le_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)]
        have h3 := mul_le_mul_of_nonneg_right hchain (by positivity : (0 : ℝ) ≤ (av ^ 2)⁻¹)
        linarith [h3]
      have hCm : C * av * μ = C * (Xp ^ 323 * (av ^ 2)⁻¹) := by
        rw [mul_assoc, havm]
      have hAle : A ≤ C * av * μ := by
        rw [hCm]
        linarith [hA1, hA2]
      linarith [hAle, hT1B, hBdef]
  -- ## (10) the final assembly
  have hsplit : S * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)
        + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2) = A + B := by
    rw [hAdef, hBdef]; ring
  rw [hsplit]
  linarith [hApay, hCt1, hAdef, hBdef]

/-- **The `Vc`-spelling** of `slidingChainArithB` (the statement of
`Submission/Work/BoseFixB1B/slidingChainArith.lean`: `V ≤ Vc`, `Vc = av³X_p⁻⁴⁷¹` instead of
`V X_p⁴⁷¹ ≤ (av)³`).  Derived from `slidingChainArithB` by the `zpow` conversion
`X_p⁻⁴⁷¹ = (X_p⁴⁷¹)⁻¹`. -/
theorem slidingChainArithBVc {N : ℕ} {av V Vc c Xp Xw S K Ks PM κ D η C μ Θ Q : ℝ}
    (hN : 1 ≤ N) (hav : 0 < av) (hV : 0 < V) (hD : 0 < D) (hμ : 0 < μ) (hc : 0 < c)
    (hKs : 0 < Ks) (hXw : 0 ≤ Xw) (hXp0 : 0 ≤ Xp) (hXp1 : Xp ≤ 1) (hκ : 0 ≤ κ) (hQ : 0 ≤ Q)
    (hS : S ≤ (N : ℝ) + 1) (hS0 : 0 ≤ S)
    (hΘ : Θ = 4 * c ^ 3 * V * Ks * av / (3 * Real.pi ^ 2 * (1 + η) * D))
    (hc6 : c ^ 6 = (av ^ 6)⁻¹ * Xp ^ 936)
    (hVc : V ≤ Vc) (hVcval : Vc = av ^ 3 * Xp ^ (-471 : ℤ))
    (hXwle : Xw ≤ κ ^ 2 * V)
    (hXpPow : Xp ^ 323 = μ * av ^ 3)
    (hKsPM : 2 * Ks * PM = K * D) (hηK : 8 * K ≤ 1 + η) (hη0 : 0 ≤ η)
    (hCκ : 4 * Ks * κ ^ 2 ≤ C)
    (hCint : 4 * κ ^ 2 * Ks ^ 2 * av / (9 * Real.pi ^ 4 * (1 + η) * D) ≤ C) :
    0 ≤ (1 / 2) * (1 + η) * D * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
        - S * Xw * (c ^ 3 * Ks * av / (3 * Real.pi ^ 2 * V)
            + 4 * ((N : ℝ) + 1 + 1) * Ks * PM / V ^ 2)
        + (C - 4 * Ks * κ ^ 2) * av * (μ + (((N : ℝ) + 1) / V)) * Q
        + C * av * μ := by
  have hXppos : 0 < Xp := by
    by_contra h
    push Not at h
    have h0 : Xp = 0 := le_antisymm h hXp0
    rw [h0] at hXpPow
    simp only [zero_pow (by norm_num : (323 : ℕ) ≠ 0)] at hXpPow
    nlinarith [mul_pos hμ (pow_pos hav 3)]
  have hVX : V * Xp ^ 471 ≤ av ^ 3 := by
    have h1 : Xp ^ (-471 : ℤ) = (Xp ^ 471)⁻¹ := by simp [zpow_neg]
    rw [h1] at hVcval
    have h2 : V ≤ av ^ 3 * (Xp ^ 471)⁻¹ := by rw [← hVcval]; exact hVc
    calc V * Xp ^ 471 ≤ (av ^ 3 * (Xp ^ 471)⁻¹) * Xp ^ 471 :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt (pow_pos hXppos 471))
      _ = av ^ 3 := by field_simp
  exact slidingChainArithB hN hav hV hD hμ hc hKs hXw hXp0 hXp1 hκ hQ hS hS0 hΘ hc6 hVX
    hXwle hXpPow hKsPM hηK hη0 hCκ hCint

end Work.BoseFixB1B
