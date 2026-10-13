/-
# The `D_θ`-pairing against the `Φ₁ = w²/(1+z)` weight

`Work.Coercivity.wip ρ (D_θ u) u = ∫∫ (D_θu)·u·ρ` is bounded by the *unsigned* self-pairing
`wip (w²sin(2θ)^{-q}) u u`:

  `wip (w²/(1+z)·sin(2θ)^{-q}) (D_θu) u ≤ wip (w²·sin(2θ)^{-q}) u u`   for `0 ≤ q ≤ 2`.

This is the "transport slot" of the `𝓛̂`-coercivity: the angular integration by parts
`wip_Dth_ibp` turns the left-hand side into `(q-1)·∫_z Φ₁(z)·∫_θ cos(2θ)sin(2θ)^{-q}u²`,
and then `|q-1| ≤ 1` (from `0 ≤ q ≤ 2`), `|cos(2θ)| ≤ 1` and `Φ₁ = w²/(1+z) ≤ w²` on
`z ≥ 0` give the bound.  The proof is carried out on the product measure
`(volume.restrict I_z).prod (volume.restrict I_θ)`, where the comparison of the
`cos`-weighted integrand with the two dominating ones is `integral_mono_of_nonneg`; the
only analytic input is the integration by parts `wip_Dth_ibp` of `DthIbp.lean`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Product-measure bookkeeping (local copies of the private helpers of `WipLSelf`) -/

/-- The restriction of the plane Lebesgue measure to `I_z ×ˢ I_θ` is the product of the two
restricted measures. -/
private theorem volume_restrict_prod_loc :
    volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact (MeasureTheory.Measure.prod_restrict _ _).symm

/-- `IntegrableOn` on the quadrant is `Integrable` against the product of the two restricted
measures. -/
private theorem integrableOn_prod_iff_loc {g : ℝ → ℝ → ℝ} :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ↔ MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [MeasureTheory.IntegrableOn, volume_restrict_prod_loc]
  rfl

theorem dth_Phi1_wip_le {u : ℝ → ℝ → ℝ} {q : ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      ≤ Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q)) u u := by
  set m : MeasureTheory.Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hm
  -- ## 0.  Integrability of the three integrands required by `wip_Dth_ibp`,
  --        with the weight `Φ₁ = w²/(1+z)`.
  have hUtil : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hU1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 / (1 + z))
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hUtil).congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hT1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 / (1 + z)) * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hT).congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hU2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hU.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  -- ## 1.  The same three integrands on the product measure, together with the
  --        `cos`-weighted one (obtained by domination, `|cos| ≤ 1`).
  have hFint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * (Real.sin (2 * p.2)) ^ (-q)) m := by
    rw [hm]
    exact (integrableOn_prod_iff_loc (g := fun z θ => u z θ ^ 2
      * ((Work.Spaces.w z) ^ 2 / (1 + z)) * (Real.sin (2 * θ)) ^ (-q))).mp hU1
  have hGint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q))) m := by
    rw [hm]
    refine ((integrableOn_prod_iff_loc (g := fun z θ => u z θ * u z θ
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))).mp hU2).congr ?_
    filter_upwards with p
    ring
  have hcos : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.cos (2 * p.2)) m :=
    (Real.measurable_cos.comp (measurable_const.mul measurable_snd)).aestronglyMeasurable
  have hEint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)) m := by
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
          * (Real.sin (2 * p.2)) ^ (-q) * Real.cos (2 * p.2)) m :=
      hFint.aestronglyMeasurable.mul hcos
    refine hFint.norm.mono' ?_ ?_
    · refine haesm.congr ?_
      filter_upwards with p
      ring
    · filter_upwards with p
      have hA : |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2)|
          ≤ |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))| := by
        rw [abs_mul]
        calc |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))|
              * |Real.cos (2 * p.2)|
            ≤ |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))| := mul_one _
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc |(u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * Real.cos (2 * p.2)) * (Real.sin (2 * p.2)) ^ (-q)|
          = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * Real.cos (2 * p.2)| * |(Real.sin (2 * p.2)) ^ (-q)| := abs_mul _ _
        _ ≤ |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))|
              * |(Real.sin (2 * p.2)) ^ (-q)| :=
            mul_le_mul_of_nonneg_right hA (abs_nonneg _)
        _ = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * (Real.sin (2 * p.2)) ^ (-q)| := (abs_mul _ _).symm
  have hE1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 / (1 + z))
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    (integrableOn_prod_iff_loc (g := fun z θ => u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 / (1 + z))
      * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))).mpr hEint
  -- ## 2.  The angular integration by parts.
  have hIBP : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      = (q - 1) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
          * ∫ θ in Work.Spaces.Iθ,
              Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) :=
    Work.FTS.StrongPersist.H6Aux.R.wip_Dth_ibp
      (Φ := fun z => (Work.Spaces.w z) ^ 2 / (1 + z)) (q := q) hs hU1 hT1 hE1
  -- ## 3.  The a.e. weight facts on the quadrant.
  have hpos : ∀ᵐ p ∂m, 0 < p.1 := by
    rw [hm]; exact Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos
  have hφnn : ∀ᵐ p ∂m, 0 ≤ (Work.Spaces.w p.1) ^ 2 / (1 + p.1) := by
    filter_upwards [hpos] with p hp
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hφle : ∀ᵐ p ∂m, (Work.Spaces.w p.1) ^ 2 / (1 + p.1)
      ≤ (Work.Spaces.w p.1) ^ 2 := by
    filter_upwards [hpos] with p hp
    have h1 : (0 : ℝ) < 1 + p.1 := by linarith
    rw [div_le_iff₀ h1]
    nlinarith [sq_nonneg (Work.Spaces.w p.1), hp]
  have hσnn : ∀ᵐ p ∂m, 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := by
    have hθ : ∀ᵐ p ∂m, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [hm]; exact Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo
    filter_upwards [hθ] with p hp
    exact Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.1])
      (by linarith [hp.2, Real.pi_pos])).le _
  -- ## 4.  The comparison of the `cos`-weighted integrand with the two dominating ones.
  have hcomp1 : (∫ p, |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)| ∂m)
      ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * (Real.sin (2 * p.2)) ^ (-q) ∂m := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hFint ?_
    filter_upwards [hφnn, hσnn] with p hφ hσ
    have hAnn : 0 ≤ u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)) :=
      mul_nonneg (sq_nonneg _) hφ
    have hA : |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
          * Real.cos (2 * p.2)|
        ≤ u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)) := by
      rw [abs_mul, abs_of_nonneg hAnn]
      calc (u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)))
            * |Real.cos (2 * p.2)|
          ≤ (u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hAnn
        _ = u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)) := mul_one _
    calc |(u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2)) * (Real.sin (2 * p.2)) ^ (-q)|
        = |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2)| * |(Real.sin (2 * p.2)) ^ (-q)| := abs_mul _ _
      _ ≤ (u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1)))
            * |(Real.sin (2 * p.2)) ^ (-q)| :=
          mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ = u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * (Real.sin (2 * p.2)) ^ (-q) := by rw [abs_of_nonneg hσ]
  have hcomp2 : (∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * (Real.sin (2 * p.2)) ^ (-q) ∂m)
      ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q)) ∂m := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hGint ?_
    · filter_upwards [hφnn, hσnn] with p hφ hσ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hφ) hσ
    · filter_upwards [hφle, hσnn] with p hφ hσ
      calc u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * (Real.sin (2 * p.2)) ^ (-q)
          = u p.1 p.2 ^ 2 * (((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
              * (Real.sin (2 * p.2)) ^ (-q)) := by ring
        _ ≤ u p.1 p.2 ^ 2 * (((Work.Spaces.w p.1) ^ 2)
              * (Real.sin (2 * p.2)) ^ (-q)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ hσ) (sq_nonneg _)
        _ = u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-q)) := by ring
  -- ## 5.  The right-hand side of the integration by parts, on the product measure.
  set A : ℝ := ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q) ∂m with hA
  have hTconv : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
        * ∫ θ in Work.Spaces.Iθ,
            Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) = A := by
    have hstep1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
          * ∫ θ in Work.Spaces.Iθ,
              Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2)
        = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
            * (Real.sin (2 * θ)) ^ (-q)) (fun z θ => Real.cos (2 * θ) * u z θ) u := by
      rw [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      dsimp only
      ring
    have hE2 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => (Real.cos (2 * θ) * u z θ) * u z θ
          * ((Work.Spaces.w z) ^ 2 / (1 + z) * (Real.sin (2 * θ)) ^ (-q))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine hE1.congr ?_
      filter_upwards with p
      dsimp only [Function.uncurry]
      ring
    have hstep2 : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
          * (Real.sin (2 * θ)) ^ (-q)) (fun z θ => Real.cos (2 * θ) * u z θ) u
        = ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q) ∂m := by
      rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (fun z θ => Real.cos (2 * θ) * u z θ) u hE2]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      ring
    rw [hstep1, hstep2, hA]
  -- ## 6.  The integral of the absolute value is bounded by the two dominating integrals.
  have hfin : |A| ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-q)) ∂m := by
    rw [hA]
    calc |∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q) ∂m|
        ≤ ∫ p, |u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)| ∂m :=
          abs_integral_le_integral_abs
      _ ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2 / (1 + p.1))
            * (Real.sin (2 * p.2)) ^ (-q) ∂m := hcomp1
      _ ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q)) ∂m := hcomp2
  -- ## 7.  Assembly.
  have habs : |q - 1| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  calc Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 / (1 + z)
        * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      = (q - 1) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 / (1 + z)
          * ∫ θ in Work.Spaces.Iθ,
              Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) := hIBP
    _ = (q - 1) * A := by rw [hTconv]
    _ ≤ |(q - 1) * A| := le_abs_self _
    _ = |q - 1| * |A| := by rw [abs_mul]
    _ ≤ 1 * |A| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    _ = |A| := one_mul _
    _ ≤ ∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-q)) ∂m := hfin
    _ = Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-q)) u u := by
        rw [show (∫ p, u p.1 p.2 ^ 2 * ((Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-q)) ∂m)
            = ∫ p, u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-q)) ∂m from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
        exact (Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-q)) u u hU2).symm

end

end Work.FTS.StrongPersist.H6Aux.R
