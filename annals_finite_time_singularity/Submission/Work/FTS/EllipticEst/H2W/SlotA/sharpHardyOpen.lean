import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.sharpHardyDefs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.crossThetaIbp
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp `cos²`-weighted Hardy inequality on the open interval

This is the *weak-class* version of `Work.FTS.EllipticEst.Honest.SharpHardyCosWeight` and of
`Work.FTS.EllipticEst.H2W.sharpHardy_slice`: the slice `v` is only required to be `C¹` on the
**open** interval `(0,π/2)` (no closed-interval regularity and no endpoint values — this is what
the almost-everywhere class `H2W.Ae.AeData` supplies), and

```
∫_θ v² cos²(2θ) sin(2θ)^{-2-η}  ≤  (1+η)^{-2} · ∫_θ v'(θ)² sin(2θ)^{-η} ,
```

with **no** correction term: the boundary term of the completion of squares vanishes because of
`SlotA.cross_theta_ibp` (`∫ gDeriv η v = 0` on `(0,π/2)`, the derivative of
`gFn η v θ = v θ² cos(2θ) sin(2θ)^{-1-η}`), which is the `θ`-IBP of the cross term of `I₁`.

## Proof

The pointwise completion of squares (`hardy_pointwise`, a copy of the body of
`H2W.sharpHardy_slice.slice_pointwise`) gives, for `θ ∈ (0,π/2)`,

`(1+η)² v² cos²(2θ) sin(2θ)^{-2-η} ≤ v'² sin(2θ)^{-η} - (1+η)·gDeriv η v θ`.

Integrating over `(0,π/2)` and using `∫ gDeriv η v = 0` (from `cross_theta_ibp`, by linearity of
the integral applied to the three summands of `gDeriv`) gives `(1+η)²∫v²cos²2θ sin^{-2-η} ≤
∫v'²sin^{-η}`, i.e. the claim after dividing by `(1+η)² > 0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **The pointwise completion of squares** behind the sharp angular Hardy inequality. -/
private theorem hardy_pointwise (η : ℝ) (hη : 0 < η) (v : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    (1 + η) ^ 2 * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))
      ≤ (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        - (1 + η) * Work.FTS.EllipticEst.H2W.gDeriv η v θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsτ : (Real.sin (2 * θ)) ^ (-η) =
      (Real.sin (2 * θ)) ^ (-η / 2) * (Real.sin (2 * θ)) ^ (-η / 2) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hsυ : (Real.sin (2 * θ)) ^ (-2 - η) =
      (Real.sin (2 * θ)) ^ (-1 - η / 2) * (Real.sin (2 * θ)) ^ (-1 - η / 2) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hsτυ : (Real.sin (2 * θ)) ^ (-(1 + η)) =
      (Real.sin (2 * θ)) ^ (-η / 2) * (Real.sin (2 * θ)) ^ (-1 - η / 2) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hsq : 0 ≤ ((deriv v θ) * (Real.sin (2 * θ)) ^ (-η / 2)
      - (1 + η) * (v θ) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η / 2)) ^ 2 :=
    sq_nonneg _
  have hkey : (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        - (1 + η) * Work.FTS.EllipticEst.H2W.gDeriv η v θ
        - (1 + η) ^ 2 * ((v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-2 - η))
      = ((deriv v θ) * (Real.sin (2 * θ)) ^ (-η / 2)
          - (1 + η) * (v θ) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η / 2)) ^ 2
        + 2 * (1 + η) * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
    rw [Work.FTS.EllipticEst.H2W.gDeriv]
    rw [hsτ, hsυ, hsτυ]
    ring
  have hnn : 0 ≤ 2 * (1 + η) * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _))
  linarith [hsq, hkey, hnn]

/-- **`∫ gDeriv η v = 0` on the open interval**, i.e. the identity `CROSS = ⟨v,v⟩ + (1+η)N` of
`SlotA.cross_theta_ibp` rewritten in terms of the boundary quantity `gFn`. -/
theorem integral_gDeriv_eq_zero (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (v : ℝ → ℝ)
    (hv : ∀ θ ∈ Iθo, HasDerivAt v (deriv v θ) θ)
    (hintA : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Iθo)
    (hintC : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) Iθo)
    (hintN : MeasureTheory.IntegrableOn
      (fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)) Iθo) :
    (∫ θ in Iθo, Work.FTS.EllipticEst.H2W.gDeriv η v θ) = 0 := by
  have hmain := cross_theta_ibp η hη hη1 v hv hintA hintC hintN
  set F : ℝ → ℝ := fun θ =>
    2 * (v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) with hF
  set G : ℝ → ℝ := fun θ => 2 * (v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) with hG
  set H : ℝ → ℝ := fun θ => 2 * (1 + η) * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-2 - η)) with hH
  have hFi : MeasureTheory.IntegrableOn F Iθo := by rw [hF]; exact hintC.const_mul 2
  have hGi : MeasureTheory.IntegrableOn G Iθo := by rw [hG]; exact hintA.const_mul 2
  have hHi : MeasureTheory.IntegrableOn H Iθo := by rw [hH]; exact hintN.const_mul (2 * (1 + η))
  have heq : (∫ θ in Iθo, Work.FTS.EllipticEst.H2W.gDeriv η v θ) = ∫ θ in Iθo, F θ - G θ - H θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    simp only [Work.FTS.EllipticEst.H2W.gDeriv, hF, hG, hH]
    ring_nf
  have hFG : (∫ θ in Iθo, F θ - G θ) = (∫ θ in Iθo, F θ) - (∫ θ in Iθo, G θ) :=
    MeasureTheory.integral_sub hFi hGi
  have hFGH : (∫ θ in Iθo, F θ - G θ - H θ)
      = (∫ θ in Iθo, F θ - G θ) - (∫ θ in Iθo, H θ) :=
    MeasureTheory.integral_sub (hFi.sub hGi) hHi
  have hF' : (∫ θ in Iθo, F θ)
      = 2 * (∫ θ in Iθo,
          v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) := by
    rw [hF]
    exact MeasureTheory.integral_const_mul 2 _
  have hG' : (∫ θ in Iθo, G θ)
      = 2 * (∫ θ in Iθo, v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
    rw [hG]
    exact MeasureTheory.integral_const_mul 2 _
  have hH' : (∫ θ in Iθo, H θ)
      = 2 * (1 + η) * (∫ θ in Iθo, v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - η)) := by
    rw [hH]
    exact MeasureTheory.integral_const_mul (2 * (1 + η)) _
  rw [heq, hFGH, hFG, hF', hG', hH']
  linarith [hmain]

/-- **The sharp `cos²`-weighted Hardy inequality on the open interval.** -/
theorem sharpHardyCosWeight_open (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (v : ℝ → ℝ)
    (hv : ∀ θ ∈ Iθo, HasDerivAt v (deriv v θ) θ)
    (hintA : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Iθo)
    (hintC : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) Iθo)
    (hintN : MeasureTheory.IntegrableOn
      (fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)) Iθo)
    (hintD : MeasureTheory.IntegrableOn
      (fun θ => (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Iθo) :
    (∫ θ in Iθo, v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))
      ≤ (1 / (1 + η) ^ 2) * (∫ θ in Iθo, (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  have hgz := integral_gDeriv_eq_zero η hη hη1 v hv hintA hintC hintN
  -- integrability of the two sides
  have hL : MeasureTheory.IntegrableOn
      (fun θ => (1 + η) ^ 2 * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-2 - η))) Iθo :=
    hintN.const_mul ((1 + η) ^ 2)
  have hZ : MeasureTheory.IntegrableOn
      (fun θ => (1 + η) * Work.FTS.EllipticEst.H2W.gDeriv η v θ) Iθo := by
    have hbase : MeasureTheory.IntegrableOn (fun θ =>
        2 * (v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η)))
          - 2 * (v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          - 2 * (1 + η) * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-2 - η))) Iθo := by
      refine (((hintC.const_mul 2).sub (hintA.const_mul 2)).sub
        (hintN.const_mul (2 * (1 + η)))).congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Pi.sub_apply]
      rw [show (-1 - η) = -(1 + η) by ring]
    have h : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.H2W.gDeriv η v) Iθo := hbase
    exact h.const_mul (1 + η)
  have hR : MeasureTheory.IntegrableOn
      (fun θ => (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        - (1 + η) * Work.FTS.EllipticEst.H2W.gDeriv η v θ) Iθo :=
    hintD.sub hZ
  -- the pointwise bound holds on all of `Iθo`
  have hmono : (∫ θ in Iθo, (1 + η) ^ 2 * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-2 - η)))
      ≤ ∫ θ in Iθo, ((deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        - (1 + η) * Work.FTS.EllipticEst.H2W.gDeriv η v θ) :=
    MeasureTheory.integral_mono_ae hL hR
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall (fun θ hθ => hardy_pointwise η hη v hθ)))
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub hintD hZ, MeasureTheory.integral_const_mul, hgz, mul_zero,
    sub_zero] at hmono
  have hpos : (0 : ℝ) < (1 + η) ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos]
  linarith [hmono]

end Work.FTS.EllipticEst.H2W.SlotA
