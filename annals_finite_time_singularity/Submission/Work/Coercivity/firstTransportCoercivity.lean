/-
# The coercivity of `𝓛_Γ^T` in the three weighted `L²` norms (`FirstTransportCoercivity`)

This file proves the estimate that the paper uses as the base case of the `ℋ¹`
coercivity of `𝓛_Γ^T`: the three energies `EfEta f`, `EDth α f` and `Ef f` are
bounded by the three `𝓛_Γ^T`-pairings with the weights `w²/sin^η`, `w²` and
`w²/sin^γ`.

The mathematics is a bookkeeping exercise on top of the three propositions of the
chapter:

* `L2CoercivityTransportEta` (the `sin^{-η}`-weighted `L²` coercivity of `𝓛_Γ^T`):
  `(1/5)·EfEta f - 10⁵(EL12z f + EDthW f + Ef f) ≤ wip w²/sin^η (𝓛_Γ^T f) f`;
* `L2CoercivityTransport` (the unweighted one):
  `(1/5)·Ef f - 10⁴·EDthW f ≤ wip w² (𝓛_Γ^T f) f`;
* `thetaDerivative` (the `D_θ` coercivity):
  `(1/4 - α)·EDth α f - 10⁷α·Ef f ≤ wip w²/sin^γ (D_θ𝓛_Γ^T f) (D_θ f)`,

together with the finite-dimensional inputs

* `EL12z_le`: `EL12z f ≤ 16·Ef f`,
* `EDthW_le_EDth` (below): `|D_θ f w|² ≤ |D_θ f w/√sin^γ|²`, because the extra
  angular factor `sin(2θ)^{-γ}` is `≥ 1` a.e. on the quadrant (`γ = 1 + α/10 > 0`).

Multiplying the three propositions by `10`, `10⁸` and `10¹³` and rearranging gives
the multipliers of the target statement; the numerical inequalities that have to be
satisfied are

* `10¹³(1/4 - α) ≥ 10¹² + 10⁶` (needed to absorb the `EDthW`-errors of the first
  two propositions by the `EDth`-gain of the third, once `EDthW ≤ EDth` is used) —
  here `α ≤ 10^{-14}` is used only through `10¹³α ≤ 1/10`;
* `10⁶ ≥ 10²⁰α` (to absorb the `10⁷α·Ef`-error of `thetaDerivative`, using the
  `Ef`-gain of `L2CoercivityTransport`), i.e. `α ≤ 10^{-14}`;
* `2·10⁷ ≥ 10⁶ + 10⁶ + 16·10⁶` (the `Ef`-bookkeeping with `EL12z ≤ 16 Ef`).

The constant `10¹³` on the third term is a deviation from the paper's `10¹²` (see
`NOTES.md`); with it all the bookkeeping closes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.thetaDerivative
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.f_sq_w_sq_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The unweighted angular energy is dominated by the `sin(2θ)^{-γ}`-weighted one:
`|D_θ f·w|²_{L²} ≤ |D_θ f·w/√(sin(2θ)^γ)|²_{L²}`.

The two energies only differ by the angular factor `sin(2θ)^{-γ}`, which is `≥ 1`
almost everywhere on the quadrant: `γ = Spaces.gam α = 1 + α/10 > 0` for `α > 0`
and `0 < sin(2θ) ≤ 1` for `θ ∈ (0, π/2)`.  The hypothesis `CoerciveData` supplies
the joint integrability of both integrands (`intDth` and `intDthGam`), so that both
sides are honest finite integrals.  (This is the `D_θ`-analogue of `Ef_le_EfEta`.) -/
theorem EDthW_le_EDth (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    EDthW f ≤ EDth α f := by
  set P : Measure (ℝ × ℝ) :=
    (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  -- ## Joint integrability against the product measure
  have hIntW : Integrable (fun p : ℝ × ℝ =>
      Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
    integrableOn_prod hi.intDth
  have hIntG : Integrable (fun p : ℝ × ℝ =>
      Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
        * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)))) P := by
    refine (integrableOn_prod (g := fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
      * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) hi.intDthGam).congr
      (Eventually.of_forall fun p => ?_)
    ring
  -- ## The two energies as integrals against the product measure
  have hW : (∫ p, Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
      = EDthW f := by
    rw [hP, EDthW]
    exact (wip_eq_integral_prod (fun z _ => Spaces.w z ^ 2) (Spaces.Dth f) (Spaces.Dth f)
      (by simpa using hi.intDth)).symm
  have hG : (∫ p, Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
        * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) ∂P) = EDth α f := by
    rw [hP, EDth_eq_wip]
    refine (wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth f) (Spaces.Dth f) ?_).symm
    refine IntegrableOn.congr_fun hi.intDthGam (fun p hp => ?_)
      (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  -- ## The a.e. pointwise inequality
  have hle : ∀ᵐ p ∂P, Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2
      ≤ Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
        * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
    have hne : ∀ᵐ p ∂P, Real.sin (2 * p.2) ≠ 0 := by
      rw [hP, ← volume_restrict_prod]
      exact ae_restrict_of_ae ae_sin_two_ne_zero
    filter_upwards [ae_prod_quadrant, hne] with p hp hsin
    have h0 : 0 ≤ Real.sin (2 * p.2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
    have hpos : 0 < Real.sin (2 * p.2) := lt_of_le_of_ne h0 (Ne.symm hsin)
    have hgam : 0 ≤ Spaces.gam α := by rw [gam_eq]; linarith
    have hle1 : (Real.sin (2 * p.2)) ^ (Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one h0 (Real.sin_le_one _) hgam
    have hge1 : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := by
      rw [Real.rpow_neg (le_of_lt hpos)]
      exact (one_le_inv₀ (Real.rpow_pos_of_pos hpos _)).mpr hle1
    have hgnn : 0 ≤ Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2 :=
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
    calc Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2
        = (Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2) * 1 :=
          (mul_one _).symm
      _ ≤ (Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2)
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := mul_le_mul_of_nonneg_left hge1 hgnn
      _ = Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
            * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by ring
  -- ## Monotonicity of the integral
  calc EDthW f = ∫ p, Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P :=
        hW.symm
    _ ≤ ∫ p, Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
          * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) ∂P :=
        integral_mono_ae hIntW hIntG hle
    _ = EDth α f := hG

theorem firstTransportCoercivity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hΓ2 : GammaPointwiseBnd α)
    (hi : CoerciveData α f) :
    EfEta f + EDth α f + Ef f
      ≤ 10 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
            (LGammaT α f) f
        + 10 ^ 8 * wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f
        + 10 ^ 13 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
            (Spaces.Dth (LGammaT α f)) (Spaces.Dth f) := by
  -- `α ≤ 1/10¹⁴ ≤ 1`, so that the three coercivity propositions apply
  have hα1' : α ≤ 1 := le_trans hα1 (by norm_num)
  -- The three `𝓛_Γ^T`-pairings of the right-hand side
  set X : ℝ := wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
    (LGammaT α f) f with hX
  set Y : ℝ := wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f with hY
  set Z : ℝ := wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
    (Spaces.Dth (LGammaT α f)) (Spaces.Dth f) with hZ
  -- ## Nonnegativity of the energies
  have hEf_nn : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEfEta_nn : 0 ≤ EfEta f := by
    rw [EfEta, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEDth_nn : 0 ≤ EDth α f := by
    rw [EDth, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  -- ## The three propositions of the chapter
  have hA := L2CoercivityTransportEta α hα hα1' f hf hfH hΓ hi
  rw [← hX] at hA
  have hB := L2CoercivityTransport α hα hα1' f hf hfH hΓ hi
  rw [← hY] at hB
  have hC := thetaDerivative α hα hα1' f hf hfH hΓ hΓ2 hi
  rw [← hZ] at hC
  -- ## The finite-dimensional inputs `EL12z f ≤ 16 Ef f` and `EDthW f ≤ EDth α f`
  have hfw : IntegrableOn (Function.uncurry fun z θ => (f z θ * Spaces.w z) ^ 2)
      (Spaces.Iz ×ˢ Spaces.Iθ) volume := by
    refine IntegrableOn.congr_fun (f_sq_w_sq_integrable α f hi) (fun p hp => ?_)
      (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have hEL := EL12z_le f hfH hfw
  have hED := EDthW_le_EDth α hα f hi
  -- ## The three propositions, scaled to the multipliers of the statement
  have hstep1 : 2 * EfEta f - 10 ^ 6 * (EL12z f + EDthW f + Ef f) ≤ 10 * X := by
    have h := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 10)
    linarith [h]
  have hstep2 : 2 * 10 ^ 7 * Ef f - 10 ^ 12 * EDthW f ≤ 10 ^ 8 * Y := by
    have h := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 8)
    linarith [h]
  have hstep3 : 2 * 10 ^ 12 * EDth α f - 10 ^ 6 * Ef f ≤ 10 ^ 13 * Z := by
    have hC13 := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 13)
    have h1 : (10 : ℝ) ^ 13 * ((1 / 4 - α) * EDth α f) - (10 : ℝ) ^ 20 * (α * Ef f)
        ≤ (10 : ℝ) ^ 13 * Z := by
      have heq : (10 : ℝ) ^ 13 * ((1 / 4 - α) * EDth α f - 10 ^ 7 * α * Ef f)
          = (10 : ℝ) ^ 13 * ((1 / 4 - α) * EDth α f) - (10 : ℝ) ^ 20 * (α * Ef f) := by
        ring
      linarith [hC13, heq]
    have hαp : (10 : ℝ) ^ 20 * α ≤ 10 ^ 6 := by
      have h := mul_le_mul_of_nonneg_left hα1 (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 20)
      have h2 : (10 : ℝ) ^ 20 * (1 / 10 ^ 14) = 10 ^ 6 := by norm_num
      linarith [h, h2]
    have h2 : (10 : ℝ) ^ 20 * (α * Ef f) ≤ 10 ^ 6 * Ef f := by
      have h := mul_le_mul_of_nonneg_right hαp hEf_nn
      simpa [mul_assoc] using h
    have hc : (2 : ℝ) * 10 ^ 12 ≤ (10 : ℝ) ^ 13 * (1 / 4 - α) := by
      have h := mul_le_mul_of_nonneg_left hα1 (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 13)
      have h2 : (10 : ℝ) ^ 13 * (1 / 10 ^ 14) = 1 / 10 := by norm_num
      have h3 : (10 : ℝ) ^ 13 * α ≤ 1 / 10 := by linarith [h, h2]
      calc (2 : ℝ) * 10 ^ 12 ≤ (10 : ℝ) ^ 13 * (1 / 4) - 1 / 10 := by norm_num
        _ ≤ (10 : ℝ) ^ 13 * (1 / 4) - (10 : ℝ) ^ 13 * α := by linarith
        _ = (10 : ℝ) ^ 13 * (1 / 4 - α) := by ring
    have h3 : (2 : ℝ) * 10 ^ 12 * EDth α f ≤ (10 : ℝ) ^ 13 * ((1 / 4 - α) * EDth α f) := by
      have h := mul_le_mul_of_nonneg_right hc hEDth_nn
      have heq : ((10 : ℝ) ^ 13 * (1 / 4 - α)) * EDth α f
          = (10 : ℝ) ^ 13 * ((1 / 4 - α) * EDth α f) := by ring
      linarith [h, heq]
    linarith [h1, h2, h3]
  have hstep4 : 10 ^ 12 * EDthW f ≤ 10 ^ 12 * EDth α f :=
    mul_le_mul_of_nonneg_left hED (by norm_num)
  have hstep5 : 10 ^ 6 * EDthW f ≤ 10 ^ 6 * EDth α f :=
    mul_le_mul_of_nonneg_left hED (by norm_num)
  have hstep6 : 10 ^ 6 * EL12z f ≤ 10 ^ 6 * 16 * Ef f := by
    have h := mul_le_mul_of_nonneg_left hEL (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6)
    linarith [h]
  -- ## The bookkeeping
  linarith [hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, hEfEta_nn, hEDth_nn, hEf_nn]

end Work.Coercivity
