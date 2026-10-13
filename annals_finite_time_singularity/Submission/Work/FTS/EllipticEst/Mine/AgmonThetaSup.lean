import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Mine.integrableOn_sin_two_rpow
import Submission.Work.FTS.EllipticEst.Mine.setIntegral_sin_two_rpow_le
import Submission.Work.FTS.EllipticEst.Mine.abs_le_setIntegral_abs_of_hasDerivAt_eq_zero
import Submission.Work.FTS.EllipticEst.Mine.sq_setIntegral_abs_le_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Agmon-style sup-interpolation estimate on the angular slice

For `v : ℝ → ℝ` of class `C²` on the angular interval `[0, π/2]` with `v 0 = v (π/2) = 0`,
weighted interpolation of `(v')²` between the two weighted `L²` quantities
`∫ (v')² sin(2θ)^{2-γ}` and `∫ (v'')² sin(2θ)^{-99/100}` holds with constant
`(π/2)·∫ sin(2θ)^{2-γ}`.

The route is the classical "Agmon" one:

* `v` vanishes at both endpoints, so by Rolle's theorem `v'` has a zero `ξ ∈ (0, π/2)`;
* hence `v'(θ) = ∫_ξ^θ v''` (fundamental theorem of calculus), and therefore, for *every*
  `θ ∈ [0, π/2]`, `(v'(θ))² ≤ (∫_{[0,π/2]} |v''|)²`;
* Cauchy–Schwarz with the reciprocal weights `u = sin(2θ)^{-99/100}` and `v = sin(2θ)^{99/100}`
  bounds the right-hand side by `(∫ (v'')² u)·(∫ v) ≤ (∫ (v'')² u)·(π/2)`;
* integrating the pointwise bound against `sin(2θ)^{2-γ} ≤ 1` (whose integral is `≤ π/2`)
  gives the claim.

The only non-elementary ingredient is that `v''`, namely `deriv (deriv v)`, is a.e. measurable:
this is Mathlib's `measurable_deriv`, and it is used to deduce integrability of `v''` from the
weighted `L²` hypothesis `hint2` by an AM–GM (i.e. `2|g| ≤ g²u + 1/u`) argument.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.FTS.EllipticEst.Mine

/-- `π/2`, the length of the angular interval. -/
private def Lpi : ℝ := Real.pi / 2

/-- The angular weight `θ ↦ sin(2θ)^a`. -/
private def thW (a : ℝ) : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) a

/-- The angular weights are a.e. measurable on the slice: on the open interval the base
`sin (2θ)` is positive, so `θ ↦ sin(2θ)^a` is continuous there, and the open interval is
a.e. equal to the closed one. -/
private theorem aemeasurable_thW (a : ℝ) :
    AEMeasurable (thW a) (volume.restrict (Set.Icc 0 Lpi)) := by
  have hIoo : ContinuousOn (thW a) (Set.Ioo 0 Lpi) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      have h1 : 0 < 2 * θ := by linarith [hθ.1]
      have h2 : 2 * θ < Real.pi := by
        have h3 : θ < Real.pi / 2 := hθ.2
        linarith
      exact Or.inl (Real.sin_pos_of_pos_of_lt_pi h1 h2).ne'
  have hA := hIoo.aemeasurable (μ := volume) measurableSet_Ioo
  rw [show volume.restrict (Set.Icc 0 Lpi) = volume.restrict (Set.Ioo 0 Lpi) from
      (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0)
        (b := Lpi))).symm]
  exact hA

theorem AgmonThetaSup {v : ℝ → ℝ} {γ : ℝ}
    (hcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt v (deriv v θ) θ)
    (hdiff2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (deriv v) (deriv (deriv v) θ) θ)
    (hd1c : ContinuousOn (deriv v) (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (hpi : v (Real.pi / 2) = 0)
    (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 5 / 4)
    (hint1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv v θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (Set.Icc 0 (Real.pi / 2)))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv v) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(99 / 100)))
      (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in Set.Icc 0 (Real.pi / 2),
        (deriv v θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ ((Real.pi / 2) * (∫ θ in Set.Icc 0 (Real.pi / 2),
            Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        * (∫ θ in Set.Icc 0 (Real.pi / 2),
            (deriv (deriv v) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(99 / 100))) := by
  change (∫ θ in Set.Icc 0 Lpi, (deriv v θ) ^ 2 * thW (2 - γ) θ)
      ≤ ((Lpi * (∫ θ in Set.Icc 0 Lpi, thW (2 - γ) θ))
        * (∫ θ in Set.Icc 0 Lpi, (deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ))
  have hLpos : 0 < Lpi := by rw [Lpi]; positivity
  have hLnn : 0 ≤ Lpi := le_of_lt hLpos
  -- elementary facts about `sin (2θ)` on the slice
  have hsin_nn : ∀ θ ∈ Set.Icc 0 Lpi, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
    have h3 : θ ≤ Real.pi / 2 := hθ.2
    linarith
  have hsin_pos : ∀ θ ∈ Set.Ioo 0 Lpi, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    have h3 : θ < Real.pi / 2 := hθ.2
    linarith
  -- measurability of the three weights and of `v'' = deriv (deriv v)`
  have hAM_wt : AEMeasurable (thW (-(99 / 100))) (volume.restrict (Set.Icc 0 Lpi)) :=
    aemeasurable_thW _
  have hAM_wr : AEMeasurable (thW (99 / 100)) (volume.restrict (Set.Icc 0 Lpi)) :=
    aemeasurable_thW _
  have hAM_g : AEMeasurable (deriv (deriv v)) (volume.restrict (Set.Icc 0 Lpi)) :=
    (measurable_deriv _).aemeasurable
  -- integrability of the weights with nonnegative exponent, and the bound on their integrals
  have hW_int : ∀ a : ℝ, 0 ≤ a → IntegrableOn (thW a) (Set.Icc 0 Lpi) := fun a ha => by
    change IntegrableOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) a) (Set.Icc 0 Lpi)
    rw [show Set.Icc (0 : ℝ) Lpi = Set.Icc 0 (Real.pi / 2) from by rw [Lpi]]
    exact integrableOn_sin_two_rpow (a := a) ha
  have hW_int_le : ∀ a : ℝ, 0 ≤ a → (∫ θ in Set.Icc 0 Lpi, thW a θ) ≤ Lpi := fun a ha => by
    simpa [thW, Lpi] using setIntegral_sin_two_rpow_le (a := a) ha
  have hwr_int : IntegrableOn (thW (99 / 100)) (Set.Icc 0 Lpi) := hW_int _ (by norm_num)
  have hw_int : IntegrableOn (thW (2 - γ)) (Set.Icc 0 Lpi) := hW_int _ (by linarith)
  -- pointwise facts on the open interval
  have hwt_nn_pt : ∀ θ ∈ Set.Ioo 0 Lpi, 0 ≤ thW (-(99 / 100)) θ :=
    fun θ hθ => Real.rpow_nonneg (le_of_lt (hsin_pos θ hθ)) _
  have hwr_nn_pt : ∀ θ ∈ Set.Ioo 0 Lpi, 0 ≤ thW (99 / 100) θ :=
    fun θ hθ => Real.rpow_nonneg (le_of_lt (hsin_pos θ hθ)) _
  have hprod_pt : ∀ θ ∈ Set.Ioo 0 Lpi, thW (-(99 / 100)) θ * thW (99 / 100) θ = 1 := by
    intro θ hθ
    have hs := hsin_pos θ hθ
    have h1 : thW (-(99 / 100)) θ * thW (99 / 100) θ = thW (-(99 / 100) + 99 / 100) θ :=
      (Real.rpow_add hs _ _).symm
    rw [h1, show -(99 / 100) + 99 / 100 = (0 : ℝ) by norm_num]
    exact Real.rpow_zero _
  -- the same facts almost everywhere on the closed slice
  have ae_Ioo : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 Lpi)), θ ∈ Set.Ioo 0 Lpi := by
    rw [show volume.restrict (Set.Icc 0 Lpi) = volume.restrict (Set.Ioo 0 Lpi) from
        (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0)
          (b := Lpi))).symm]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun θ hθ => hθ
  have hwt_nn : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 Lpi)), 0 ≤ thW (-(99 / 100)) θ :=
    ae_Ioo.mono fun θ hθ => hwt_nn_pt θ hθ
  have hwr_nn : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 Lpi)), 0 ≤ thW (99 / 100) θ :=
    ae_Ioo.mono fun θ hθ => hwr_nn_pt θ hθ
  have hprod_ae : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 Lpi)),
      thW (-(99 / 100)) θ * thW (99 / 100) θ = 1 :=
    ae_Ioo.mono fun θ hθ => hprod_pt θ hθ
  -- AM-GM: `2|g| ≤ g²u + 1/u`, giving integrability of `v''` from `hint2`
  have hamgm : ∀ θ ∈ Set.Ioo 0 Lpi, |deriv (deriv v) θ|
      ≤ (1 / 2) * ((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ)
        + (1 / 2) * thW (99 / 100) θ := by
    intro θ hθ
    have hs := hsin_pos θ hθ
    have hA : 0 ≤ (deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _)
    have hB : 0 ≤ thW (99 / 100) θ := Real.rpow_nonneg (le_of_lt hs) _
    have hAB : ((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ) * thW (99 / 100) θ
        = (deriv (deriv v) θ) ^ 2 := by
      rw [mul_assoc, hprod_pt θ hθ, mul_one]
    have hsq : |deriv (deriv v) θ|
        = Real.sqrt (((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ) * thW (99 / 100) θ) := by
      rw [hAB, Real.sqrt_sq_eq_abs]
    rw [hsq, Real.sqrt_mul hA]
    have h2 : 2 * (Real.sqrt ((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ)
          * Real.sqrt (thW (99 / 100) θ))
        ≤ ((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ) + thW (99 / 100) θ := by
      have h := sq_nonneg (Real.sqrt ((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ)
        - Real.sqrt (thW (99 / 100) θ))
      rw [sub_sq, Real.sq_sqrt hA, Real.sq_sqrt hB] at h
      nlinarith [h]
    linarith
  have hmvt_int : IntegrableOn (deriv (deriv v)) (Set.Icc 0 Lpi) := by
    have hdom : Integrable (fun θ => (1 / 2) * ((deriv (deriv v) θ) ^ 2 * thW (-(99 / 100)) θ)
        + (1 / 2) * thW (99 / 100) θ) (volume.restrict (Set.Icc 0 Lpi)) :=
      (hint2.const_mul (1 / 2)).add (hwr_int.const_mul (1 / 2))
    refine MeasureTheory.Integrable.mono' hdom hAM_g.aestronglyMeasurable ?_
    filter_upwards [ae_Ioo] with θ hθ
    rw [Real.norm_eq_abs]
    exact hamgm θ hθ
  have hmvt_int_abs : IntegrableOn (fun θ => |deriv (deriv v) θ|) (Set.Icc 0 Lpi) := by
    change Integrable (fun θ => |deriv (deriv v) θ|) (volume.restrict (Set.Icc 0 Lpi))
    simpa [Real.norm_eq_abs] using hmvt_int.norm
  -- Rolle: `v'` has a zero inside the interval
  obtain ⟨ξ, hξmem, hξ0⟩ : ∃ ξ ∈ Set.Ioo 0 Lpi, deriv v ξ = 0 :=
    exists_hasDerivAt_eq_zero hLpos hcont (by rw [h0]; exact hpi.symm) hdiff
  have hInt_g : IntervalIntegrable (deriv (deriv v)) volume 0 Lpi := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hLnn]
    exact hmvt_int.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ θ ∈ Set.Icc 0 Lpi,
      |deriv v θ| ≤ ∫ x in Set.Icc 0 Lpi, |deriv (deriv v) x| := fun θ hθ =>
    abs_le_setIntegral_abs_of_hasDerivAt_eq_zero (f := deriv v) (g := deriv (deriv v))
      hLpos hd1c hdiff2 hξmem hξ0 hθ hInt_g
  -- Cauchy-Schwarz with the reciprocal weights `sin(2θ)^{-99/100}` and `sin(2θ)^{99/100}`
  have hCS : (∫ x in Set.Icc 0 Lpi, |deriv (deriv v) x|) ^ 2
      ≤ (∫ x in Set.Icc 0 Lpi, (deriv (deriv v) x) ^ 2 * thW (-(99 / 100)) x)
        * (∫ x in Set.Icc 0 Lpi, thW (99 / 100) x) :=
    sq_setIntegral_abs_le_mul (g := deriv (deriv v)) (u := thW (-(99 / 100)))
      (v := thW (99 / 100)) (s := Set.Icc 0 Lpi)
      hAM_g hAM_wt hAM_wr hwt_nn hwr_nn hprod_ae hint2 hwr_int hmvt_int_abs
  -- the pointwise bound `(v')² ≤ (∫ (v'')² u) · (π/2)`
  set A : ℝ := ∫ x in Set.Icc 0 Lpi, (deriv (deriv v) x) ^ 2 * thW (-(99 / 100)) x with hAdef
  have hA_nn : 0 ≤ A := by
    rw [hAdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hwt_nn] with θ hθ
    exact mul_nonneg (sq_nonneg _) hθ
  have hpt : ∀ θ ∈ Set.Icc 0 Lpi, (deriv v θ) ^ 2 ≤ A * Lpi := by
    intro θ hθ
    have h1 : (deriv v θ) ^ 2 = |deriv v θ| ^ 2 := by rw [sq_abs]
    have h2 : |deriv v θ| ^ 2 ≤ (∫ x in Set.Icc 0 Lpi, |deriv (deriv v) x|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hpoint θ hθ) 2
    have h3 : (∫ x in Set.Icc 0 Lpi, |deriv (deriv v) x|) ^ 2
        ≤ A * (∫ x in Set.Icc 0 Lpi, thW (99 / 100) x) := by
      rw [hAdef]; exact hCS
    have h4 : (∫ x in Set.Icc 0 Lpi, thW (99 / 100) x) ≤ Lpi := hW_int_le _ (by norm_num)
    have h5 : A * (∫ x in Set.Icc 0 Lpi, thW (99 / 100) x) ≤ A * Lpi :=
      mul_le_mul_of_nonneg_left h4 hA_nn
    linarith
  have hnn_w : ∀ θ ∈ Set.Icc 0 Lpi, 0 ≤ thW (2 - γ) θ :=
    fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _
  have hmono : (∫ θ in Set.Icc 0 Lpi, (deriv v θ) ^ 2 * thW (2 - γ) θ)
      ≤ ∫ θ in Set.Icc 0 Lpi, (A * Lpi) * thW (2 - γ) θ := by
    refine setIntegral_mono_on hint1 (hw_int.const_mul (A * Lpi)) measurableSet_Icc ?_
    intro θ hθ
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) (hnn_w θ hθ)
  calc (∫ θ in Set.Icc 0 Lpi, (deriv v θ) ^ 2 * thW (2 - γ) θ)
      ≤ (A * Lpi) * (∫ θ in Set.Icc 0 Lpi, thW (2 - γ) θ) :=
        hmono.trans_eq (integral_const_mul _ _)
    _ = (Lpi * (∫ θ in Set.Icc 0 Lpi, thW (2 - γ) θ)) * A := by ring

end Work.FTS.EllipticEst.Mine
