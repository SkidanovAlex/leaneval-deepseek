import Mathlib
import Submission.Work.Analysis.HoleVoidCost.integralFderivNormSqLeSum
import Submission.Work.BoseFixB1B.PerBoxSmoothHolds
import Submission.Work.BoseFixB1S.csIntegralSqLe
import Submission.Work.BoseFixB1S.flatArmSlidingDefs
import Submission.Work.BoseFixB1S.mfZeroHoleFixB1S
import Submission.Work.SmallBoxA0.PolarSphere.integral_eq_sphere_radius
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.HoleVoidCost.chiBGradGe`

The **localisation-gradient (Poincaré) lower bound** for the sliding window
`χ_{B(u)} = chiB ℓ d u` (`Submission.Work.DLInfra`): there is a constant `c > 0` with

    `c · (∫ χ_{B(u)}²) / (ℓ·d)²  ≤  ∫ ∑_k (∂_k χ_{B(u)})²`

for every `ℓ, d > 0`, `u ∈ ℝ³`.

## Why it is true (and why `(ℓd)` is the right scale)

`chiB ℓ d u z = χ(z/ℓ)·χ(z/(ℓd) − u)`, and `χ = chiScale` vanishes outside the closed cube
`acube (ℓd)` of the *second* factor.  Hence `χ_{B(u)}` is supported in a coordinate cube of side
`ℓ·d` — whose points are all within `ℓd·√3/2 ≤ ℓd` of its centre — and the Poincaré/Friedrichs
inequality for a function supported in a set of diameter `≲ ℓd` gives exactly

    `∫ f² ≤ C·(ℓd)²·∫ ‖∇f‖²`.

So the whole content is the classical Poincaré inequality at the small-box scale: no property of
`χ` beyond `C¹`, compact support and the support cube is used.

## Route

* `integral_sq_le_of_support_subset_cube` — the general Poincaré inequality, proved from
  Mathlib's Gagliardo–Nirenberg–Sobolev inequality
  `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le` with `p = q = 2`, `n = 3` and support set the
  cube `acube (2R)` (whose volume is exactly `(2R)³`, so the GNS constant
  `(volume s)^{1/3}·K` is exactly `2R·K`).
* `support_chiB_subset_cube` — the support of `χ_{B(u)}` lies in the cube `(ℓd)•u + acube (ℓd)`.
* `gradConst` — the universal GNS constant `SNormLESNormFDerivOfEqConst ℝ volume 2`.
* `chiBGradGe` — the assembly, with `c = 1/(gradConst² + 1)`.
-/

open MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 4000000

-- `ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of `Submission.Work.BoseKinLoc.Defs`
-- (`notation "ℝ³" => EuclideanSpace ℝ (Fin 3)`), which is in this file's import cone.

namespace Work.Analysis.HoleVoidCost

/-- The universal constant of the Gagliardo–Nirenberg–Sobolev inequality in `ℝ³`
(`MeasureTheory.SNormLESNormFDerivOfEqConst ℝ volume 2`), as a real number. -/
noncomputable def gradConst : ℝ :=
  (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ³))
    (2 : NNReal) : ℝ)

lemma gradConst_nonneg : 0 ≤ gradConst := by
  rw [gradConst]; positivity

/-- **The volume of a translate of the coordinate cube.**  For `L ≥ 0` and `c : ℝ³`,
the set `{z | z - c ∈ acube L}` is the translate `c + acube L` of the cube of side `L`, hence
has volume `L³`. -/
lemma volume_sub_acube (c : ℝ³) {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (ℝ³))
        {z : ℝ³ | z - c ∈ Submission.BoseGases.acube L}
      = ENNReal.ofReal (L ^ 3) := by
  have hs_eq : {z : ℝ³ | z - c ∈ Submission.BoseGases.acube L}
      = (fun z : ℝ³ => (-c) + z) ⁻¹'
          Submission.BoseGases.acube L := by
    ext z; simp [sub_eq_add_neg, add_comm]
  rw [hs_eq, MeasureTheory.measure_preimage_add]
  exact Submission.BoseGases.acube_volume L hL

/-- **The GNS constant, unfolded.**  For `p = q = 2` in dimension `3` the exponent
`1/q - 1/p'` of `eLpNormLESNormFDerivOfLeConst` is `1/3`, so the constant read off the
Gagliardo–Nirenberg–Sobolev inequality is the `(volume)^{1/3}`-multiple of
`SNormLESNormFDerivOfEqConst ℝ volume 2`. -/
lemma const_eq (s : Set (ℝ³)) :
    MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (ℝ³))
        s (2 : NNReal) (2 : NNReal)
      = (volume s).toNNReal ^ ((1 : ℝ) / 3)
        * MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
            (volume : Measure (ℝ³)) (2 : NNReal) := by
  rw [MeasureTheory.eLpNormLESNormFDerivOfLeConst]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]
  have h2 : (3 : NNReal)⁻¹ ≤ (2 : NNReal)⁻¹ := by
    rw [← NNReal.coe_le_coe]; norm_num
  have h3 : ((2 : NNReal)⁻¹ - (3 : NNReal)⁻¹)⁻¹ = 6 := by
    rw [← NNReal.coe_inj, NNReal.coe_inv, NNReal.coe_sub h2, NNReal.coe_inv, NNReal.coe_inv]
    norm_num
  rw [h3]
  rw [show (↑(2 : NNReal) : ℝ) = 2 by norm_num]
  norm_num

lemma NNReal_cube_cbrt (x : NNReal) : (x ^ 3) ^ ((1 : ℝ) / 3) = x := by
  nth_rewrite 1 [← NNReal.rpow_natCast x 3]
  rw [← NNReal.rpow_mul]
  norm_num

lemma Real_cube_cbrt {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ ((1 : ℝ) / 3) = x := by
  nth_rewrite 1 [← Real.rpow_natCast x 3]
  rw [← Real.rpow_mul hx]
  norm_num

/-- **Poincaré (Friedrichs) inequality for a function supported in a coordinate cube of side
`2R`.**  If `f : ℝ³ → ℝ` is `C¹` with compact support contained in `c + acube (2R)`, then

    `∫ f² ≤ (2R)²·gradConst²·∫ ‖∇f‖²`.

The proof is Mathlib's Gagliardo–Nirenberg–Sobolev inequality
(`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`) at `p = q = 2`, whose constant for a support
set of volume `(2R)³` is exactly `(2R)·gradConst`; the inequality is then squared and converted
from `eLpNorm` to the Bochner integral. -/
theorem integral_sq_le_of_support_subset_cube (f : ℝ³ → ℝ)
    (hcd : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) (c : ℝ³)
    (R : ℝ) (hR : 0 < R)
    (hsupp : Function.support f ⊆
      {z : ℝ³ | z - c ∈ Submission.BoseGases.acube (2 * R)}) :
    ∫ z, (f z) ^ 2 ≤ (2 * R) ^ 2 * gradConst ^ 2 * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := by
  have h2R : 0 < 2 * R := by linarith
  have h2Rnn : (0 : ℝ) ≤ 2 * R := le_of_lt h2R
  set s : Set (ℝ³) :=
    {z : ℝ³ | z - c ∈ Submission.BoseGases.acube (2 * R)} with hsdef
  have hmem : ∀ z, z ∈ s ↔ z - c ∈ Submission.BoseGases.acube (2 * R) := by
    intro z; simp [hsdef]
  have hsupps : Function.support f ⊆ s := fun z hz => (hmem z).mpr (hsupp hz)
  have hvol : (volume : Measure (ℝ³)) s = ENNReal.ofReal ((2 * R) ^ 3) := by
    rw [hsdef]; exact volume_sub_acube c h2Rnn
  have hvolnn : (volume s).toNNReal = Real.toNNReal ((2 * R) ^ 3) := by
    rw [hvol, ENNReal.ofReal, ENNReal.toNNReal_coe]
  -- `s` is bounded (it sits in the ball of radius `3R` about `c`)
  have hbdd : Bornology.IsBounded s := by
    refine (Metric.isBounded_closedBall (x := c) (r := 3 * R)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzc : z - c ∈ Submission.BoseGases.acube (2 * R) := (hmem z).mp hz
    rw [Submission.BoseGases.mem_acube_iff] at hzc
    rw [EuclideanSpace.norm_eq]
    have hsum : (∑ i : Fin 3, ‖(z - c).ofLp i‖ ^ 2) ≤ 3 * R ^ 2 := by
      calc (∑ i : Fin 3, ‖(z - c).ofLp i‖ ^ 2)
          ≤ ∑ _i : Fin 3, R ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [Real.norm_eq_abs]
            have hi := hzc i
            rw [Set.mem_Icc] at hi
            have hRi : |(z - c).ofLp i| ≤ R := by
              rw [abs_le]; constructor <;> linarith [hi.1, hi.2]
            exact pow_le_pow_left₀ (abs_nonneg _) hRi 2
        _ = 3 * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    calc Real.sqrt (∑ i : Fin 3, ‖(z - c).ofLp i‖ ^ 2)
        ≤ Real.sqrt (3 * R ^ 2) := Real.sqrt_le_sqrt hsum
      _ ≤ 3 * R := by
          rw [Real.sqrt_le_iff]
          exact ⟨by linarith, by nlinarith [hR]⟩
  -- the Gagliardo–Nirenberg–Sobolev inequality
  have hpq : (↑((2 : NNReal)⁻¹) : ℝ) - (↑(Module.finrank ℝ (ℝ³)))⁻¹
      ≤ (↑(2 : NNReal))⁻¹ := by
    rw [finrank_euclideanSpace_fin]; norm_num
  set C : NNReal := MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ
    (volume : Measure (ℝ³)) s (2 : NNReal) (2 : NNReal) with hCdef
  set K2 : NNReal := MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
    (volume : Measure (ℝ³)) (2 : NNReal) with hK2def
  have hC : C = Real.toNNReal ((2 * R) ^ 3) ^ ((1 : ℝ) / 3) * K2 := by
    rw [hCdef, const_eq s, hvolnn, ← hK2def]
  have hGNS := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le
    (μ := (volume : Measure (ℝ³))) hcd hsupps
    (show (1 : NNReal) ≤ 2 by norm_num)
    (by rw [finrank_euclideanSpace_fin]; norm_num)
    hpq hbdd
  -- integrability of the two integrands
  have hf2i : Integrable (fun z : ℝ³ => (f z) ^ 2) :=
    (hcd.continuous.pow 2).integrable_of_hasCompactSupport
      (hcs.mono (fun z hz => by
        simp only [Function.mem_support] at hz ⊢
        exact fun h => hz (by simp [Pi.pow_apply, h])))
  have hfdi : Integrable (fun z : ℝ³ => ‖fderiv ℝ f z‖ ^ 2) :=
    ((hcd.continuous_fderiv (by simp)).norm.pow 2).integrable_of_hasCompactSupport
      ((hcs.fderiv ℝ).mono (fun z hz => by
        simp only [Function.mem_support] at hz ⊢
        exact fun h => hz (by simp [Pi.pow_apply, h])))
  have hf2nn : 0 ≤ᵐ[(volume : Measure (ℝ³))]
      (fun z : ℝ³ => (f z) ^ 2) :=
    ae_of_all _ (fun z => sq_nonneg (f z))
  have hfdnn : 0 ≤ᵐ[(volume : Measure (ℝ³))]
      (fun z : ℝ³ => ‖fderiv ℝ f z‖ ^ 2) :=
    ae_of_all _ (fun z => sq_nonneg _)
  -- rewrite the two `eLpNorm ^ 2`s as Bochner integrals
  have hLHS : (MeasureTheory.eLpNorm f (2 : NNReal)
        (volume : Measure (ℝ³))) ^ (((2 : NNReal) : ℝ))
      = ENNReal.ofReal (∫ z : ℝ³, (f z) ^ 2) := by
    rw [MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)]
    have h1 : (∫⁻ z : ℝ³, ‖f z‖ₑ ^ (((2 : NNReal) : ℝ)))
        = ∫⁻ z : ℝ³, ENNReal.ofReal ((f z) ^ 2) := by
      refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show ‖f z‖ₑ ^ (((2 : NNReal) : ℝ)) = ENNReal.ofReal ((f z) ^ 2)
      rw [Real.enorm_eq_ofReal_abs,
        show (((2 : NNReal) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (abs_nonneg (f z)), sq_abs]
    rw [h1]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf2i hf2nn).symm
    all_goals first | fun_prop | (apply Continuous.aestronglyMeasurable; fun_prop) | (apply Continuous.aemeasurable; fun_prop) | (apply Continuous.measurable; fun_prop) | measurability
  have hRHS : (MeasureTheory.eLpNorm (fderiv ℝ f) (2 : NNReal)
        (volume : Measure (ℝ³))) ^ (((2 : NNReal) : ℝ))
      = ENNReal.ofReal (∫ z : ℝ³, ‖fderiv ℝ f z‖ ^ 2) := by
    rw [MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)]
    have h1 : (∫⁻ z : ℝ³, ‖fderiv ℝ f z‖ₑ ^ (((2 : NNReal) : ℝ)))
        = ∫⁻ z : ℝ³, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
      refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show ‖fderiv ℝ f z‖ₑ ^ (((2 : NNReal) : ℝ))
        = ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)
      rw [← ofReal_norm (fderiv ℝ f z),
        show (((2 : NNReal) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (norm_nonneg (fderiv ℝ f z))]
    rw [h1]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfdi hfdnn).symm
    all_goals first | fun_prop | (apply Continuous.aestronglyMeasurable; fun_prop) | (apply Continuous.aemeasurable; fun_prop) | (apply Continuous.measurable; fun_prop) | measurability
  -- square the GNS inequality and convert
  have hsq := ENNReal.rpow_le_rpow hGNS (show (0 : ℝ) ≤ ((2 : NNReal) : ℝ) by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ ((2 : NNReal) : ℝ) by positivity)] at hsq
  rw [hLHS, hRHS] at hsq
  have hCC : (↑(C : ℝ≥0∞)) ^ (((2 : NNReal) : ℝ)) = ENNReal.ofReal ((C : ℝ) ^ 2) := by
    rw [show (((2 : NNReal) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow]
  rw [hCC, ← ENNReal.ofReal_mul (by positivity)] at hsq
  have hAB : ∫ z : ℝ³, (f z) ^ 2
      ≤ (C : ℝ) ^ 2 * ∫ z : ℝ³, ‖fderiv ℝ f z‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsq
  -- the constant is `2R·gradConst`
  have hCreal : (C : ℝ) = 2 * R * gradConst := by
    have hcube : Real.toNNReal ((2 * R) ^ 3) = (Real.toNNReal (2 * R)) ^ 3 := by
      apply NNReal.coe_inj.mp
      rw [Real.coe_toNNReal ((2 * R) ^ 3) (by positivity), NNReal.coe_pow,
        Real.coe_toNNReal (2 * R) h2Rnn]
    have hK2c : (K2 : ℝ) = gradConst := by rw [hK2def, gradConst]
    have hroot : ((Real.toNNReal ((2 * R) ^ 3) ^ ((1 : ℝ) / 3) : NNReal) : ℝ) = 2 * R := by
      have h1 : (Real.toNNReal ((2 * R) ^ 3) ^ ((1 : ℝ) / 3) : NNReal)
          = Real.toNNReal (2 * R) := by
        rw [hcube]
        exact NNReal_cube_cbrt _
      rw [h1]
      exact Real.coe_toNNReal (2 * R) h2Rnn
    rw [hC, NNReal.coe_mul, hroot, hK2c]
  rw [hCreal, mul_pow] at hAB
  simpa [mul_assoc] using hAB

/-- **The support cube of the sliding window.**  `χ_{B(u)} = chiB ℓ d u` vanishes outside
`(ℓ·d)•u + acube (ℓ·d)`: its second factor `χ((· − (ℓd)u)/(ℓd))` is supported in the cube of
side `ℓ·d` centred at `(ℓ·d)•u`. -/
lemma support_chiB_subset_cube {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) :
    Function.support (Submission.BoseGases.chiB ℓ d u) ⊆
      {z : ℝ³ |
        z - (ℓ * d) • u ∈ Submission.BoseGases.acube (ℓ * d)} := by
  intro z hz
  have h2 : Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) ≠ 0 := by
    intro h
    exact hz (by simp [Submission.BoseGases.chiB, h])
  exact Submission.BoseGases.chiScale_mem_acube (mul_pos hℓ hd) h2

/-- **`Work.Analysis.HoleVoidCost.chiBGradGe`.**

There is a universal constant `c > 0` such that for all `ℓ, d > 0` and all `u : ℝ³` the squared
`L²`-norm of the sliding window `χ_{B(u)} = chiB ℓ d u` is controlled by its full gradient
energy at the *small-box scale* `ℓ·d`:

    `c · (∫ χ_{B(u)}²) / (ℓ·d)²  ≤  ∫ ∑_{k<3} (∂_k χ_{B(u)})²` .

Equivalently: the localisation function of the small box `B(u)` of side `ℓ·d` has a gradient
energy at least of the order `(ℓ·d)^{-2}` times its mass, uniformly in `ℓ`, `d` and `u` — the
quantitative form of the uncertainty principle for a function whose support has diameter
`≲ ℓ·d`.

The proof is the Poincaré inequality `integral_sq_le_of_support_subset_cube` applied to
`f = chiB ℓ d u` with `R = ℓ·d/2` (so that the support cube is `(ℓ·d)•u + acube (ℓ·d)`),
followed by the identification of the operator norm of `fderiv ℝ f` with the sum of the
squares of its values on the standard basis
(`Work.Analysis.HoleVoidCost.integralFderivNormSqLeSum`) and the elementary arithmetic
`c·c₀·t ≤ t` for `c = 1/(c₀+1)`, `t ≥ 0`. -/
theorem chiBGradGe :
    ∃ c : ℝ, 0 < c ∧ ∀ (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)),
      0 < ℓ → 0 < d →
      c * (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiB ℓ d u z) ^ 2) / (ℓ * d) ^ 2
        ≤ ∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
            ((fderiv ℝ (Submission.BoseGases.chiB ℓ d u) z)
              (EuclideanSpace.single k (1 : ℝ))) ^ 2 := by
  refine ⟨1 / (gradConst ^ 2 + 1), by positivity, ?_⟩
  intro ℓ d u hℓ hd
  set f : ℝ³ → ℝ := Submission.BoseGases.chiB ℓ d u with hfdef
  have hR : 0 < ℓ * d / 2 := by positivity
  have hcd : ContDiff ℝ 1 f :=
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).of_le (by norm_num)
  have hcs : HasCompactSupport f := Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u
  have hsupp : Function.support f ⊆
      {z : ℝ³ | z - (ℓ * d) • u ∈ Submission.BoseGases.acube (ℓ * d)} :=
    support_chiB_subset_cube hℓ hd u
  -- the Poincaré inequality, at `R = ℓd/2` and centre `(ℓd)•u`
  have hp : ∫ z, (f z) ^ 2
      ≤ (2 * (ℓ * d / 2)) ^ 2 * gradConst ^ 2
        * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := by
    refine integral_sq_le_of_support_subset_cube f hcd hcs ((ℓ * d) • u) (ℓ * d / 2) hR ?_
    rwa [show 2 * (ℓ * d / 2) = ℓ * d by ring]
  -- the gradient-norm bridge
  have hD : ∫ z, ‖fderiv ℝ f z‖ ^ 2
      ≤ ∫ z, ∑ k : Fin 3,
          ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2 :=
    integralFderivNormSqLeSum f hcd hcs
  -- assemble
  have hDnn : 0 ≤ ∫ z, ∑ k : Fin 3,
      ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2 :=
    integral_nonneg (fun z => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hA : ∫ z, (f z) ^ 2 ≤ (ℓ * d) ^ 2 * gradConst ^ 2
      * ∫ z, ∑ k : Fin 3,
          ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2 := by
    calc ∫ z, (f z) ^ 2
        ≤ (2 * (ℓ * d / 2)) ^ 2 * gradConst ^ 2 * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := hp
      _ = (ℓ * d) ^ 2 * gradConst ^ 2 * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := by
          rw [show 2 * (ℓ * d / 2) = ℓ * d by ring]
      _ ≤ (ℓ * d) ^ 2 * gradConst ^ 2
            * ∫ z, ∑ k : Fin 3,
                ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left hD (by positivity)
  have hkey : 1 / (gradConst ^ 2 + 1) * (∫ z, (f z) ^ 2)
      ≤ (ℓ * d) ^ 2 * ∫ z, ∑ k : Fin 3,
          ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2 := by
    calc 1 / (gradConst ^ 2 + 1) * (∫ z, (f z) ^ 2)
        ≤ 1 / (gradConst ^ 2 + 1) * ((ℓ * d) ^ 2 * gradConst ^ 2
            * ∫ z, ∑ k : Fin 3,
                ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (1 / (gradConst ^ 2 + 1) * gradConst ^ 2) * ((ℓ * d) ^ 2
            * ∫ z, ∑ k : Fin 3,
                ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2) := by ring
      _ ≤ 1 * ((ℓ * d) ^ 2 * ∫ z, ∑ k : Fin 3,
                ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_mul_eq_mul_div, div_le_one (by positivity)]
          linarith [sq_nonneg gradConst]
      _ = (ℓ * d) ^ 2 * ∫ z, ∑ k : Fin 3,
                ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2 := one_mul _
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (ℓ * d) ^ 2),
    mul_comm (∫ z, ∑ k : Fin 3, ((fderiv ℝ f z) (EuclideanSpace.single k (1 : ℝ))) ^ 2)
      ((ℓ * d) ^ 2)]
  exact hkey

end Work.Analysis.HoleVoidCost
