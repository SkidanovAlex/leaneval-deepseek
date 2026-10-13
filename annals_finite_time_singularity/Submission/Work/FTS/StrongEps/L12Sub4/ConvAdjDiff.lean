import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

open MeasureTheory Set
open scoped Real Topology

/-- The unshifted-weight translation identity on `ℝ × ℝ`: integrating
`x ↦ G x₂ · F (x₁-p₁) (x₂-p₂)` gives the same value as integrating `x ↦ G (x₂+p₂) · F x₁ x₂`.
Immediate from the translation invariance of Lebesgue measure
(`MeasureTheory.integral_add_right_eq_self`), applied in the reverse direction. -/
theorem integral_shift_weight (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ∫ x : ℝ × ℝ, G x.2 * F (x.1 - p.1) (x.2 - p.2)
      = ∫ x : ℝ × ℝ, G (x.2 + p.2) * F x.1 x.2 := by
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun y : ℝ × ℝ => G y.2 * F (y.1 - p.1) (y.2 - p.2)) p
  have h2 : (fun y : ℝ × ℝ => G (y + p).2 * F ((y + p).1 - p.1) ((y + p).2 - p.2))
      = fun y : ℝ × ℝ => G (y.2 + p.2) * F y.1 y.2 := by
    funext y; simp
  rw [← h, h2]

/-- Joint integrability of `(x,p) ↦ k p · G x₂ · F (x₁-p₁) (x₂-p₂)` for the product Lebesgue
measure.  Because `k` is supported in the strip `|p₂| ≤ 1`, the shift bound on `G` and the
translation invariance of Lebesgue measure give a dominating product function, and Tonelli
(`MeasureTheory.integrable_prod_iff'`) turns the two iterated integrals into joint integrability.
The joint measurability of `(x,p) ↦ F (x₁-p₁) (x₂-p₂)` uses that `(x,p) ↦ x - p` is
quasi-measure-preserving (`MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant`). -/
theorem integrable_mollinger_shift (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ 1)
    (hGcont : Continuous G) (hGnn : ∀ ζ, 0 ≤ G ζ)
    (hGshift : ∀ ζ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp (8 * |q|) * G ζ)
    (hFmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F))
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2)))
      (volume.prod volume) := by
  have hF' : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => F x.1 x.2) volume := hFmeas
  have hGle : ∀ ζ : ℝ, ∀ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp 8 * G ζ := by
    intro ζ q hq
    refine le_trans (hGshift ζ q hq) ?_
    apply mul_le_mul_of_nonneg_right _ (hGnn ζ)
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg q, hq]
  have hshift : MeasureTheory.AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => F (z.1.1 - z.2.1) (z.1.2 - z.2.2))
      (volume.prod volume) :=
    hF'.comp_quasiMeasurePreserving
      (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant
        (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure (ℝ × ℝ))))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2)))
      (volume.prod volume) :=
    (hki.aestronglyMeasurable.comp_snd).mul
      (((hGcont.comp (continuous_snd.comp continuous_fst)).aestronglyMeasurable).mul hshift)
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · refine Filter.Eventually.of_forall (fun p => ?_)
    change MeasureTheory.Integrable
      (fun x : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) volume
    by_cases hp : k p = 0
    · rw [show (fun x : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) = fun _ => 0 from by
        funext x; rw [hp]; ring]
      exact integrable_zero _ _ _
    · have hp2 : |p.2| ≤ 1 := hksupp p hp
      have hbase : MeasureTheory.Integrable
          (fun x : ℝ × ℝ => G (x.2 - p.2) * |F (x.1 - p.1) (x.2 - p.2)|) volume :=
        hFint.comp_sub_right p
      refine MeasureTheory.Integrable.mono'
        ((hbase.const_mul (Real.exp 8)).const_mul |k p|) ?_ ?_
      · exact aestronglyMeasurable_const.mul
          (((hGcont.comp continuous_snd).aestronglyMeasurable).mul
            (hF'.comp_quasiMeasurePreserving
              (MeasureTheory.measurePreserving_sub_right (volume : Measure (ℝ × ℝ))
                p).quasiMeasurePreserving))
      · refine Filter.Eventually.of_forall (fun x => ?_)
        have hGx : G x.2 ≤ Real.exp 8 * G (x.2 - p.2) := by
          have h1 := hGle (x.2 - p.2) p.2 hp2
          rwa [show (x.2 - p.2) + p.2 = x.2 from by ring] at h1
        have hFnn : 0 ≤ |F (x.1 - p.1) (x.2 - p.2)| := abs_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p), abs_mul, abs_of_nonneg (hGnn x.2)]
        have h2 : G x.2 * |F (x.1 - p.1) (x.2 - p.2)|
            ≤ Real.exp 8 * (G (x.2 - p.2) * |F (x.1 - p.1) (x.2 - p.2)|) := by
          nlinarith [hGx, hFnn]
        exact mul_le_mul_of_nonneg_left h2 (hknn p)
  · refine MeasureTheory.Integrable.mono'
      ((hki.abs).mul_const (Real.exp 8 * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|)) ?_ ?_
    · exact hmeas.prod_swap.norm.integral_prod_right'
    · refine Filter.Eventually.of_forall (fun p => ?_)
      change ‖∫ x : ℝ × ℝ, ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖‖
        ≤ |k p| * (Real.exp 8 * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|)
      by_cases hp : k p = 0
      · rw [show (fun x : ℝ × ℝ => ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖)
            = fun _ => 0 from by
          funext x; rw [hp]; simp]
        simp [hp]
      · have hp2 : |p.2| ≤ 1 := hksupp p hp
        have hpoint : ∀ x : ℝ × ℝ, ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖
            = |k p| * (G x.2 * |F (x.1 - p.1) (x.2 - p.2)|) := by
          intro x
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p), abs_mul, abs_of_nonneg (hGnn x.2)]
        have hI : ∫ x : ℝ × ℝ, ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖
            = |k p| * ∫ x : ℝ × ℝ, G x.2 * |F (x.1 - p.1) (x.2 - p.2)| := by
          simp only [hpoint]
          rw [MeasureTheory.integral_const_mul]
        have hIpos : 0 ≤ ∫ x : ℝ × ℝ, G x.2 * |F (x.1 - p.1) (x.2 - p.2)| :=
          MeasureTheory.integral_nonneg (fun x => mul_nonneg (hGnn x.2) (abs_nonneg _))
        have hshift2 : ∫ x : ℝ × ℝ, G x.2 * |F (x.1 - p.1) (x.2 - p.2)|
            = ∫ x : ℝ × ℝ, G (x.2 + p.2) * |F x.1 x.2| := by
          have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
            (fun y : ℝ × ℝ => G y.2 * |F (y.1 - p.1) (y.2 - p.2)|) p
          have h2 : (fun y : ℝ × ℝ => G (y + p).2 * |F ((y + p).1 - p.1) ((y + p).2 - p.2)|)
              = fun y : ℝ × ℝ => G (y.2 + p.2) * |F y.1 y.2| := by
            funext y; simp
          rw [← h, h2]
        have hInt : MeasureTheory.Integrable
            (fun x : ℝ × ℝ => G (x.2 + p.2) * |F x.1 x.2|) volume := by
          have hb : MeasureTheory.AEStronglyMeasurable
              (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume :=
            ((hGcont.comp (continuous_snd.add continuous_const)).aestronglyMeasurable).mul hF'
          have hm : MeasureTheory.Integrable
              (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume := by
            refine MeasureTheory.Integrable.mono' (hFint.const_mul (Real.exp 8)) hb ?_
            refine Filter.Eventually.of_forall (fun x => ?_)
            have hGx : G (x.2 + p.2) ≤ Real.exp 8 * G x.2 := hGle x.2 p.2 hp2
            have hFnn : 0 ≤ |F x.1 x.2| := abs_nonneg _
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn (x.2 + p.2))]
            have h2 : G (x.2 + p.2) * |F x.1 x.2| ≤ Real.exp 8 * (G x.2 * |F x.1 x.2|) := by
              nlinarith [hGx, hFnn]
            exact h2
          refine hm.abs.congr ?_
          refine Filter.Eventually.of_forall (fun x => ?_)
          simp only [abs_mul, abs_of_nonneg (hGnn (x.2 + p.2))]
        have hmon : ∫ x : ℝ × ℝ, G (x.2 + p.2) * |F x.1 x.2|
            ≤ Real.exp 8 * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2| := by
          rw [← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_mono hInt (hFint.const_mul (Real.exp 8))
          intro x
          have hGx : G (x.2 + p.2) ≤ Real.exp 8 * G x.2 := hGle x.2 p.2 hp2
          have hFnn : 0 ≤ |F x.1 x.2| := abs_nonneg _
          have h2 : G (x.2 + p.2) * |F x.1 x.2| ≤ Real.exp 8 * (G x.2 * |F x.1 x.2|) := by
            nlinarith [hGx, hFnn]
          exact h2
        rw [hI, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hIpos), hshift2]
        exact mul_le_mul_of_nonneg_left hmon (abs_nonneg _)

/-- Joint integrability of `(x,p) ↦ (k p · (G (x₂+p₂) - G x₂)) · F x₁ x₂`.  This is the
factorised case: the weight difference is bounded by `(e^8+1) G x₂` (thanks to the strip support
of `k` and the shift bound) and the two factors `|k p|` and `(e^8+1) G x₂ |F x₁ x₂|` are both
integrable. -/
theorem integrable_mollinger_weight (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ 1)
    (hGcont : Continuous G) (hGnn : ∀ ζ, 0 ≤ G ζ)
    (hGshift : ∀ ζ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp (8 * |q|) * G ζ)
    (hFmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F))
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (k z.2 * (G (z.1.2 + z.2.2) - G z.1.2)) * F z.1.1 z.1.2)
      (volume.prod volume) := by
  have hF' : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => F x.1 x.2) volume := hFmeas
  have hGle : ∀ ζ : ℝ, ∀ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp 8 * G ζ := by
    intro ζ q hq
    refine le_trans (hGshift ζ q hq) ?_
    apply mul_le_mul_of_nonneg_right _ (hGnn ζ)
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg q, hq]
  have hdom : MeasureTheory.Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      |k z.2| * ((Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|))) (volume.prod volume) :=
    (hki.abs.mul_prod (hFint.const_mul (Real.exp 8 + 1))).swap
  have hc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => G (z.1.2 + z.2.2) - G z.1.2) := by fun_prop
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact ((hki.aestronglyMeasurable.comp_snd).mul hc.aestronglyMeasurable).mul hF'.comp_fst
  · refine Filter.Eventually.of_forall (fun z => ?_)
    change ‖(k z.2 * (G (z.1.2 + z.2.2) - G z.1.2)) * F z.1.1 z.1.2‖
      ≤ |k z.2| * ((Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|))
    by_cases hp : k z.2 = 0
    · rw [hp, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (hGnn _) (abs_nonneg _)))
    · have hz2 : |z.2.2| ≤ 1 := hksupp z.2 hp
      have hd : |G (z.1.2 + z.2.2) - G z.1.2| ≤ (Real.exp 8 + 1) * G z.1.2 := by
        have h1 : G (z.1.2 + z.2.2) ≤ Real.exp 8 * G z.1.2 := hGle z.1.2 z.2.2 hz2
        have h2 : |G (z.1.2 + z.2.2) - G z.1.2| ≤ G (z.1.2 + z.2.2) + G z.1.2 := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hGnn (z.1.2 + z.2.2), hGnn z.1.2],
                 by linarith [hGnn (z.1.2 + z.2.2), hGnn z.1.2]⟩
        nlinarith [h1, h2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hknn z.2)]
      have hFnn : 0 ≤ |F z.1.1 z.1.2| := abs_nonneg _
      have hstep : |G (z.1.2 + z.2.2) - G z.1.2| * |F z.1.1 z.1.2| ≤
          (Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|) := by
        calc |G (z.1.2 + z.2.2) - G z.1.2| * |F z.1.1 z.1.2|
            ≤ ((Real.exp 8 + 1) * G z.1.2) * |F z.1.1 z.1.2| :=
              mul_le_mul_of_nonneg_right hd hFnn
          _ = (Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|) := by ring
      calc (k z.2 * |G (z.1.2 + z.2.2) - G z.1.2|) * |F z.1.1 z.1.2|
          = k z.2 * (|G (z.1.2 + z.2.2) - G z.1.2| * |F z.1.1 z.1.2|) := by ring
        _ ≤ k z.2 * ((Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|)) :=
            mul_le_mul_of_nonneg_left hstep (hknn z.2)

/-- **Adjointness of the mollifier against a `s`-independent weight, difference form** (generic
measure theory, Mathlib only).  For a nonnegative integrable kernel `k` of mass `1` supported in the
strip `|p₂| ≤ 1`, a continuous nonnegative weight `G` with `G (ζ+q) ≤ e^{8|q|} G ζ` for `|q| ≤ 1`,
and an a.e. strongly measurable `F` whose `G`-weighted absolute value is integrable,

  `∫_s ∫_ζ G(ζ) ((∫_p k p · F (s-p₁) (ζ-p₂)) - F(s,ζ))
     = ∫_s ∫_ζ (∫_p k p · (G (ζ+p₂) - G ζ)) F(s,ζ)`.

The subtraction of `F(s,ζ)` is performed *inside* the outer integral, so no measurability of the
weight-convolution `ζ ↦ ∫p, k p G(ζ+p₂)` is ever needed (the `p`-integrals stay at the outermost
level).

Hints: the LHS equals `∫∫ G(ζ)(∫p k p F(s-p₁,ζ-p₂)) - ∫∫ G·F` (`MeasureTheory.integral_sub`; both
terms are integrable — for the first, `(p,x) ↦ k p · G x.2 · |F (x.1-p.1) (x.2-p.2)|` is integrable
by Tonelli, since integrating it over `p` gives
`∫p k p ∫∫ G(ζ)|F(s-p₁,ζ-p₂)| ≤ e^8 ‖k‖₁ ∫∫ G|F| < ∞` by the shift bound).  Then write the first
term as `∫p k p ∫∫G(ζ)F(s-p₁,ζ-p₂)` and the second as `∫p k p ∫∫G(ζ)F(s,ζ)` (using `hk1` and
`MeasureTheory.integral_mul_const`), combine the two `p`-integrals with `MeasureTheory.integral_sub`,
use the translation invariance of Lebesgue measure
(`MeasureTheory.integral_sub_right_eq_self`, twice) on the first term, and finish with Fubini. -/
theorem ConvAdjDiff (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ 1)
    (hGcont : Continuous G) (hGnn : ∀ ζ, 0 ≤ G ζ)
    (hGshift : ∀ ζ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp (8 * |q|) * G ζ)
    (hFmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F))
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    ∫ s, ∫ ζ, G ζ * ((∫ p : ℝ × ℝ, k p * F (s - p.1) (ζ - p.2)) - F s ζ)
      = ∫ s, ∫ ζ, (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) * F s ζ := by
  have hF' : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => F x.1 x.2) volume := hFmeas
  have hGle : ∀ ζ : ℝ, ∀ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp 8 * G ζ := by
    intro ζ q hq
    refine le_trans (hGshift ζ q hq) ?_
    apply mul_le_mul_of_nonneg_right _ (hGnn ζ)
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg q, hq]
  -- integrability of `x ↦ G x₂ F x₁ x₂` (without the absolute value)
  have hGFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * F x.1 x.2) volume := by
    refine MeasureTheory.Integrable.mono' hFint ?_ ?_
    · exact ((hGcont.comp continuous_snd).aestronglyMeasurable).mul hF'
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn x.2)]
  -- the three joint integrability facts
  have hfL := integrable_mollinger_shift k G F hknn hki hksupp hGcont hGnn hGshift hFmeas hFint
  have hfB : MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F z.1.1 z.1.2))
      (volume.prod volume) := (hki.mul_prod hGFint).swap
  have hfC := integrable_mollinger_weight k G F hknn hki hksupp hGcont hGnn hGshift hFmeas hFint
  -- the `p`-slices of the three integrands, integrated in `x`
  have hA : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) volume :=
    MeasureTheory.Integrable.integral_prod_left
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2))) hfL
  have hB : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) volume :=
    MeasureTheory.Integrable.integral_prod_left
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F z.1.1 z.1.2)) hfB
  have hC : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) volume :=
    MeasureTheory.Integrable.integral_prod_left
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        (k z.2 * (G (z.1.2 + z.2.2) - G z.1.2)) * F z.1.1 z.1.2) hfC
  -- pointwise identities for the `p`-slices
  have hpL : ∀ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
      = G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)) := by
    intro x
    rw [show (fun p : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
        = fun p : ℝ × ℝ => G x.2 * (k p * F (x.1 - p.1) (x.2 - p.2)) from by
      funext p; ring,
      MeasureTheory.integral_const_mul]
  have hpB : ∀ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) = G x.2 * F x.1 x.2 := by
    intro x
    rw [MeasureTheory.integral_mul_const, hk1]
    ring
  have hpC : ∀ x : ℝ × ℝ,
      (∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
        = (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
    fun x => MeasureTheory.integral_mul_const _ _
  -- integrability of the `A`, `B`, `C` integrands
  have hA' : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))) volume :=
    hA.congr (Filter.Eventually.of_forall hpL)
  have hC' : MeasureTheory.Integrable
      (fun x : ℝ × ℝ =>
        (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) volume :=
    hC.congr (Filter.Eventually.of_forall hpC)
  -- the two `p`-integrals of the slices
  have hAp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) volume :=
    MeasureTheory.Integrable.integral_prod_right
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2))) hfL
  have hBp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) volume :=
    MeasureTheory.Integrable.integral_prod_right
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F z.1.1 z.1.2)) hfB
  -- the slice identity, for every `p`
  have hpFC : ∀ p : ℝ × ℝ,
      (∫ x : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
        = (∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) := by
    intro p
    by_cases hp : k p = 0
    · rw [show (fun x : ℝ × ℝ => (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) = fun _ => 0 from by
          funext x; rw [hp]; ring,
        show (fun x : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) = fun _ => 0 from by
          funext x; rw [hp]; ring,
        show (fun x : ℝ × ℝ => k p * (G x.2 * F x.1 x.2)) = fun _ => 0 from by
          funext x; rw [hp]; ring]
      simp
    · have hp2 : |p.2| ≤ 1 := hksupp p hp
      -- integrability of the shifted weight
      have hshiftInt : MeasureTheory.Integrable
          (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume := by
        have hb : MeasureTheory.AEStronglyMeasurable
            (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume :=
          ((hGcont.comp (continuous_snd.add continuous_const)).aestronglyMeasurable).mul hF'
        refine MeasureTheory.Integrable.mono' (hFint.const_mul (Real.exp 8)) hb ?_
        refine Filter.Eventually.of_forall (fun x => ?_)
        have hGx : G (x.2 + p.2) ≤ Real.exp 8 * G x.2 := hGle x.2 p.2 hp2
        have hFnn : 0 ≤ |F x.1 x.2| := abs_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn (x.2 + p.2))]
        nlinarith [hGx, hFnn]
      rw [show (fun x : ℝ × ℝ => (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
          = fun x : ℝ × ℝ => k p * ((G (x.2 + p.2) - G x.2) * F x.1 x.2) from by
        funext x; ring,
        MeasureTheory.integral_const_mul,
        show (fun x : ℝ × ℝ => (G (x.2 + p.2) - G x.2) * F x.1 x.2)
          = fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2 - G x.2 * F x.1 x.2 from by
        funext x; ring,
        MeasureTheory.integral_sub hshiftInt hGFint]
      rw [show (∫ x : ℝ × ℝ, G (x.2 + p.2) * F x.1 x.2)
          = ∫ x : ℝ × ℝ, G x.2 * F (x.1 - p.1) (x.2 - p.2) from
        (integral_shift_weight G F p).symm,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      ring
  -- the main chain
  have hmain : (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
        - (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2)
      = ∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 := by
    have hsL : (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
        = ∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)) :=
      MeasureTheory.integral_integral_swap
        (f := fun x p : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) hfL
    have hsB : (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2))
        = ∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2) :=
      MeasureTheory.integral_integral_swap
        (f := fun x p : ℝ × ℝ => k p * (G x.2 * F x.1 x.2)) hfB
    have hsC : (∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
        = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
      (MeasureTheory.integral_integral_swap
        (f := fun x p : ℝ × ℝ => (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) hfC).symm
    calc (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2)
        = (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) := by
          rw [show (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
                = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))
              from integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpL x).symm)),
            show (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2)
                = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)
              from integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpB x).symm))]
      _ = (∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) := by rw [hsL, hsB]
      _ = ∫ p : ℝ × ℝ, ((∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
            - (∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2))) :=
          (MeasureTheory.integral_sub hAp hBp).symm
      _ = ∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
          integral_congr_ae (Filter.Eventually.of_forall (fun p => (hpFC p).symm))
      _ = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 := hsC
      _ = ∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
          integral_congr_ae (Filter.Eventually.of_forall hpC)
  -- Fubini reductions of the two sides of the goal
  have hABint : MeasureTheory.Integrable
      (fun x : ℝ × ℝ =>
        G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)) - F x.1 x.2)) volume := by
    refine (hA'.sub hGFint).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply]
    ring
  have hLHS : (∫ s, ∫ ζ, G ζ * ((∫ p : ℝ × ℝ, k p * F (s - p.1) (ζ - p.2)) - F s ζ))
      = ∫ x : ℝ × ℝ,
          G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)) - F x.1 x.2) :=
    MeasureTheory.integral_integral (μ := volume) (ν := volume)
      (f := fun s ζ => G ζ * ((∫ p : ℝ × ℝ, k p * F (s - p.1) (ζ - p.2)) - F s ζ)) hABint
  have hRHS : (∫ s, ∫ ζ, (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) * F s ζ)
      = ∫ x : ℝ × ℝ,
          (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
    MeasureTheory.integral_integral (μ := volume) (ν := volume)
      (f := fun s ζ => (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) * F s ζ) hC'
  rw [hLHS, hRHS]
  have hsub : (∫ x : ℝ × ℝ, G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))
        - F x.1 x.2))
      = (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
        - (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2) := by
    rw [show (fun x : ℝ × ℝ => G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))
          - F x.1 x.2))
        = fun x : ℝ × ℝ => G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))
          - G x.2 * F x.1 x.2 from by funext x; ring,
      MeasureTheory.integral_sub hA' hGFint]
  rw [hsub, hmain]

end Work.FTS.StrongEps.L12Sub4
