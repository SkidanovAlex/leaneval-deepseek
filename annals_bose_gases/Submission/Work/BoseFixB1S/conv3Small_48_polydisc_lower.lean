import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chiSmallBase_pair_cube_lower_conv48
import Submission.Work.BoseFixB1S.oneD_pow96_integral_le_conv48
import Submission.Work.SmallBoxTBWord.chiSmallNormSq_eq_choose
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open Submission.BoseGases

/-! # `Work.BoseFixB1S.conv3Small_48_polydisc_lower`

Target file `Submission/Work/BoseFixB1S/conv3Small_48_polydisc_lower.lean`, namespace
`Work.BoseFixB1S`.  Needed imports (the file should start with them): `Mathlib`,
`Submission.Work.DLSmallKernels`, `Submission.Work.ChiSmall`.

The **provable** polydisc lower bound for the small-scale self-convolution at the corpus's
regularity `M = 48 = Work.BoseBox.mValue` (the only value the corpus ever instantiates:
`fsParams` sets `M := mValue`; note `Work.BoseBox.mValue = 48` by `rfl`).

This is the sharpened replacement for the corpus's `Work.SmallBoxSliding.smallConvLower`
(`= (((√2/2)^3)^M)^2·(1/4)^3 = 2^{-3M-6}`, exponentially small), which is what the already
proved `Work.BoseFixB1S.wSmall1Pair_fibre_le_chiM_sharp` carries in its constant.  For the
corpus's `M` the polydisc bound is far better: the true value at the polydisc corner is
`conv3Small 48 ((1/16,1/16,1/16)) = 0.626^3 = 0.245`, so `1/10000` has margin `2.4·10^3`.
A `conv3Small M ≥ c₀` bound *uniform in `M`* is FALSE (at `M = 2000` the corner value is
`4.1·10^{-9}`), which is why the target `wSmall1Pair_fibre_le_chiM_moderate` (an `M`-uniform
constant) fails as stated; the present claim is its correct, provable surrogate.

CLAIM: for every `z` with `|z.ofLp j| ≤ 1/16` (the `ℓ∞` polydisc reached by the hypothesis
`R0 ≤ (ℓ d)/16` of the fibre bound), `1/10000 ≤ conv3Small 48 z`.

## PROOF (as formalised below)

Write `S := chiSmallNormSq 48 = ∫ (chiSmallBase 48)²`, `B := chiSmallBase 48`, and
`L := conv48L = 1 - (1/2)·(3.1416·5/96)² = 126286519/128000000`
(`Submission/Work/BoseFixB1S/conv48Consts.lean`, where `zeta1d_ge_conv48L` gives `ζ(s) ≥ L`
for `|s| ≤ 5/96` and `conv48L_pow288_ge` gives `L^288 ≥ 1/81`).

1. **Unfold.** `chiSmall 48 = B / √S`, so `conv3Small 48 z = S⁻¹ · ∫ y, B y · B (z − y)`
   (`conv3Small48_eq_inv_mul`).
2. **The normalisation.** `S = (∫ ζ^96)³`
   (`Work.SmallBoxTBWord.chiSmallNormSq_eq_cube_zeta1d_integral`) and `∫ ζ^96 ≤ 1/7`
   (`Work.BoseFixB1S.oneD_pow96_integral_le_conv48`), hence `S ≤ 1/343`
   (`chiSmallNormSq48_le_343`).
3. **The box.** On `K := {y | |(y − z/2)_j| ≤ 1/48}` (volume `(1/24)³ = 1/13824`) both `y_j`
   and `(z−y)_j` range in `|·| ≤ 1/32 + 1/48 = 5/96`, so `B y · B (z−y) ≥ L^{288}` there and
   `∫_K y, B y B (z−y) ≥ L^{288}/13824` (`Work.BoseFixB1S.chiSmallBase_pair_cube_lower_conv48`);
   since the integrand is nonnegative, `∫ y, B y B (z−y) ≥ L^{288}/13824` too
   (`setIntegral_le_integral`).
4. **Finale.** `conv3Small 48 z ≥ 343 · (1/81) · (1/13824) = 343/1119744 ≈ 3.06·10⁻⁴ ≥ 1/10000`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Normalisation bound**: `chiSmallNormSq 48 ≤ 1/343`.

`chiSmallNormSq M = (∫ ζ^{2M})³` (`Work.SmallBoxTBWord.chiSmallNormSq_eq_cube_zeta1d_integral`)
together with `∫ ζ^96 ≤ 1/7` (`Work.BoseFixB1S.oneD_pow96_integral_le_conv48`). -/
lemma chiSmallNormSq48_le_343 : chiSmallNormSq 48 ≤ 1 / 343 := by
  have hfact := Work.SmallBoxTBWord.chiSmallNormSq_eq_cube_zeta1d_integral 48
  have h1 : (∫ y : ℝ, zeta1d y ^ 96) ≤ 1 / 7 := oneD_pow96_integral_le_conv48
  have hnn : 0 ≤ ∫ y : ℝ, zeta1d y ^ (2 * 48) :=
    integral_nonneg (fun y => pow_nonneg (zeta1d_nonneg y) _)
  have h3 : (∫ y : ℝ, zeta1d y ^ (2 * 48)) ^ 3 ≤ (1 / 7 : ℝ) ^ 3 := by
    refine pow_le_pow_left₀ hnn ?_ 3
    simpa using h1
  calc chiSmallNormSq 48 = (∫ y : ℝ, zeta1d y ^ (2 * 48)) ^ 3 := hfact
    _ ≤ (1 / 7 : ℝ) ^ 3 := h3
    _ = 1 / 343 := by norm_num

/-- Unfolding of the self-convolution: `conv3Small 48 z = S⁻¹ · ∫ y, B y · B (z−y)` with
`S := chiSmallNormSq 48`, from `chiSmall = chiSmallBase / √S` and `(√S)·(√S) = S`. -/
lemma conv3Small48_eq_inv_mul (z : EuclideanSpace ℝ (Fin 3)) :
    conv3Small 48 z
      = (chiSmallNormSq 48)⁻¹
        * ∫ y : EuclideanSpace ℝ (Fin 3),
            chiSmallBase 48 y * chiSmallBase 48 (z - y) := by
  have hSpos : 0 < chiSmallNormSq 48 := chiSmallNormSq_pos (by norm_num)
  have hsq : Real.sqrt (chiSmallNormSq 48) * Real.sqrt (chiSmallNormSq 48)
      = chiSmallNormSq 48 := by
    rw [← sq, Real.sq_sqrt (le_of_lt hSpos)]
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin 3), chiSmall 48 y * chiSmall 48 (z - y)
      = (chiSmallNormSq 48)⁻¹ * (chiSmallBase 48 y * chiSmallBase 48 (z - y)) := by
    intro y
    dsimp only [chiSmall]
    rw [div_mul_div_comm, hsq, div_eq_mul_inv, mul_comm]
  dsimp only [conv3Small]
  rw [show (∫ y : EuclideanSpace ℝ (Fin 3), chiSmall 48 y * chiSmall 48 (z - y))
        = ∫ y : EuclideanSpace ℝ (Fin 3),
            (chiSmallNormSq 48)⁻¹ * (chiSmallBase 48 y * chiSmallBase 48 (z - y)) from
      integral_congr_ae (ae_of_all _ hpoint)]
  rw [MeasureTheory.integral_const_mul]

/-- The base integrand of the self-convolution is integrable: it is continuous with compact
support (contained in the support of `chiSmallBase 48`). -/
lemma integrable_conv48_integrand (z : EuclideanSpace ℝ (Fin 3)) :
    Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => chiSmallBase 48 y * chiSmallBase 48 (z - y))
      volume := by
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => chiSmallBase 48 y * chiSmallBase 48 (z - y)) :=
    (chiSmallBase_continuous 48).mul
      ((chiSmallBase_continuous 48).comp (continuous_const.sub continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.mono (chiSmallBase_hasCompactSupport (M := 48) (by norm_num)) ?_
  intro y hy
  exact Function.mem_support.mpr (fun h => hy (by simp [h]))

theorem conv3Small_48_polydisc_lower (z : EuclideanSpace ℝ (Fin 3))
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 16) :
    (1 / 10000 : ℝ) ≤ conv3Small 48 z := by
  have hSpos : 0 < chiSmallNormSq 48 := chiSmallNormSq_pos (by norm_num)
  have hSle : chiSmallNormSq 48 ≤ 1 / 343 := chiSmallNormSq48_le_343
  -- integrability and nonnegativity of the base integrand
  have hFint : Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => chiSmallBase 48 y * chiSmallBase 48 (z - y))
      volume := integrable_conv48_integrand z
  have hFnn : 0 ≤ᵐ[volume]
      (fun y : EuclideanSpace ℝ (Fin 3) => chiSmallBase 48 y * chiSmallBase 48 (z - y)) :=
    ae_of_all _ (fun y => mul_nonneg (chiSmallBase_nonneg 48 y) (chiSmallBase_nonneg 48 (z - y)))
  -- the box, and the passage to the full integral
  have hKbox : conv48L ^ 288 * (1 / 13824)
      ≤ ∫ y in {y : EuclideanSpace ℝ (Fin 3) |
            ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48},
          chiSmallBase 48 y * chiSmallBase 48 (z - y) :=
    chiSmallBase_pair_cube_lower_conv48 z hz
  have hmono : (∫ y in {y : EuclideanSpace ℝ (Fin 3) |
            ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48},
          chiSmallBase 48 y * chiSmallBase 48 (z - y))
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), chiSmallBase 48 y * chiSmallBase 48 (z - y) :=
    MeasureTheory.setIntegral_le_integral hFint hFnn
  have hbase : conv48L ^ 288 * (1 / 13824)
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), chiSmallBase 48 y * chiSmallBase 48 (z - y) :=
    le_trans hKbox hmono
  -- the reciprocal normalisation
  have hSinv : (343 : ℝ) ≤ (chiSmallNormSq 48)⁻¹ := by
    have h := one_div_le_one_div_of_le hSpos hSle
    have h343 : (1 : ℝ) / (1 / 343) = 343 := by norm_num
    rw [h343] at h
    rwa [one_div] at h
  -- arithmetic
  have hpow : (1 / 81 : ℝ) ≤ conv48L ^ 288 := conv48L_pow288_ge
  have harith : (1 / 10000 : ℝ) ≤ 343 * ((1 / 81) * (1 / 13824)) := by norm_num
  have hchain : 343 * ((1 / 81) * (1 / 13824)) ≤ 343 * (conv48L ^ 288 * (1 / 13824)) := by
    have h1 : (1 / 81) * (1 / 13824) ≤ conv48L ^ 288 * (1 / 13824) :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hstep1 : 343 * (conv48L ^ 288 * (1 / 13824))
      ≤ (chiSmallNormSq 48)⁻¹ * (conv48L ^ 288 * (1 / 13824)) :=
    mul_le_mul_of_nonneg_right hSinv (by positivity)
  have hstep2 : (chiSmallNormSq 48)⁻¹ * (conv48L ^ 288 * (1 / 13824))
      ≤ (chiSmallNormSq 48)⁻¹
          * ∫ y : EuclideanSpace ℝ (Fin 3), chiSmallBase 48 y * chiSmallBase 48 (z - y) :=
    mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (le_of_lt hSpos))
  calc (1 / 10000 : ℝ) ≤ 343 * ((1 / 81) * (1 / 13824)) := harith
    _ ≤ 343 * (conv48L ^ 288 * (1 / 13824)) := hchain
    _ ≤ (chiSmallNormSq 48)⁻¹ * (conv48L ^ 288 * (1 / 13824)) := hstep1
    _ ≤ (chiSmallNormSq 48)⁻¹
          * ∫ y : EuclideanSpace ℝ (Fin 3), chiSmallBase 48 y * chiSmallBase 48 (z - y) := hstep2
    _ = conv3Small 48 z := (conv3Small48_eq_inv_mul z).symm

end

end Work.BoseFixB1S
