import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BandSdefs` — the band constants of the low-density potential bound

This module fixes the three constants that the low-density band bound
`Work.BoseFixB1.bandPotLower_lowDensity` uses, and proves their elementary
properties (nonnegativity, the square identity, and the pointwise domination of
the small-box cutoff `χ_{B(u)}` by `bandS` **on the band**).

* `bandG v h = ∫ |g₀|` — the `L¹`-mass of the renormalised potential;
* `bandS M ℓ d μ = √(chiSmallBandDecay M d · (2μ^{-1/3}/ℓ)^{2M})` — the band's
  `χ`-scale: on `bandSet ℓ d μ` the cutoff satisfies `χ_{B(u)}(x) ≤ bandS`
  (`chiSmallB_le_bandS`, from `chiSmallB_badband_sup_decay`);
* `bandK v h M = 2·(smallConvLower M)⁻¹·bandG v h` — the fibre-kernel constant
  (`|∫_y w_{1,B(u)}(x,y)dy| ≤ bandK·bandS·χ_{B(u)}(x)` on the band).

These are the constants of the target's error term: the pointwise lower bound
for `qLHSwordB` on the band is `−(μ·(bandK·bandS²·n)·‖Φ‖²)`, and the band
arithmetic (`bandS_arith`) bounds `μ²(ℓd)³bandS²` by `2^{2M}chiSupAbs²(chiSmallDecay M)²μ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `L¹`-mass `∫|g₀|` of the renormalised potential. -/
def bandG (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin 3), |g0 v h z|

/-- **The band `χ`-scale.**  On the bad band `bandSet ℓ d μ` the small-box cutoff satisfies
`χ_{B(u)}(x)² ≤ chiSmallBandDecay M d · (2μ^{-1/3}/ℓ)^{2M}` (`chiSmallB_badband_sup_decay`), so
its square root `bandS` dominates `χ_{B(u)}(x)` pointwise (`chiSmallB_le_bandS`) and
`bandS²` is exactly the decay constant. -/
def bandS (M : ℕ) (ℓ d μ : ℝ) : ℝ :=
  Real.sqrt (chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M))

/-- The fibre-kernel constant `2(smallConvLower M)⁻¹∫|g₀|`. -/
def bandK (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (M : ℕ) : ℝ :=
  2 * (smallConvLower M)⁻¹ * bandG v h

/-! ## Elementary properties -/

lemma bandG_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} :
    0 ≤ bandG v h := by
  rw [bandG]
  exact integral_nonneg fun z => abs_nonneg _

lemma bandK_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (M : ℕ) :
    0 ≤ bandK v h M :=
  mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (le_of_lt (smallConvLower_pos M))))
    bandG_nonneg

lemma bandS_nonneg (M : ℕ) (ℓ d μ : ℝ) : 0 ≤ bandS M ℓ d μ := Real.sqrt_nonneg _

/-- **`bandS²` is the decay constant** (`0 < ℓ`, `0 < d`, `0 < μ`). -/
lemma bandS_sq {M : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) :
    bandS M ℓ d μ ^ 2 = chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) := by
  rw [bandS, Real.sq_sqrt]
  exact mul_nonneg (chiSmallBandDecay_nonneg M hd)
    (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _)))
      (le_of_lt hℓ)) _)

/-- **The cutoff is dominated by `bandS` on the band.** -/
lemma chiSmallB_le_bandS {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hμ : 0 < μ) {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ bandSet ℓ d μ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    chiSmallB M ℓ d u x ≤ bandS M ℓ d μ := by
  have hrad : 0 ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) :=
    mul_nonneg (chiSmallBandDecay_nonneg M hd)
      (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _)))
        (le_of_lt hℓ)) _)
  have hsq := chiSmallB_badband_sup_decay (M := M) hM hℓ hd hμ (u := u) (x := x)
    (by rwa [bandSet_eq_chiSmallBadBand] at hu)
  rw [bandS]
  exact (Real.le_sqrt (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x) hrad).mpr hsq

end Work.BoseFixB1
