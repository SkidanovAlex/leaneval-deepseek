import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux7
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux8` — the weighted box integral of a pair kernel

For a weight `G` on configurations and a pair kernel `e`, the box integral
`∫_{abox n ℓ} G x * e (x p.1) (x p.2)` (the right-hand side of `dict13_L1` at
`G = P_{p.1}Q_{p.2}·P_{p.2}Q_{p.1}`) is shown to be a.e.-invariant in `e`, and bounded by
`B · (ℓ³)^{n-2} · ∫∫_{Λ×Λ}‖e‖` when `|G| ≤ B` on the box.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- The box integral of a weight times the `(p.1, p.2)`-pullback of a pair kernel depends only on
the a.e. class of the kernel. -/
theorem rhsGen_congr_ae {n : ℕ} {ℓ : ℝ} {G : Xn n → ℝ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {e₁ e₂ : E3 → E3 → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      Function.uncurry e₂) :
    (∫ x in abx n ℓ, G x * e₁ (x p.1) (x p.2))
      = ∫ x in abx n ℓ, G x * e₂ (x p.1) (x p.2) := by
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Xn n => (x p.1, x p.2))
      ((volume : Measure (Xn n)).restrict (abx n ℓ))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    haveI : SigmaFinite ((volume : Measure E3).restrict (acb ℓ)) := inferInstance
    have h1 := Work.BoseFixB2.Pot.quasiMeasurePreserving_pair_eval_aux
      ((volume : Measure E3).restrict (acb ℓ)) hp
    rw [show (volume : Measure (Xn n)).restrict (abx n ℓ)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (acb ℓ)) from
        Submission.BoseGases.restrict_abox_eq_pi n ℓ]
    refine h1.mono_right ?_
    exact Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le (restrict_acube_le ℓ))
      (Measure.absolutelyContinuous_of_le (restrict_acube_le ℓ))
  have hae : (fun x : Xn n => Function.uncurry e₁ (x p.1, x p.2))
      =ᵐ[(volume : Measure (Xn n)).restrict (abx n ℓ)]
      (fun x : Xn n => Function.uncurry e₂ (x p.1, x p.2)) := hqmp.ae_eq h
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp only [Function.uncurry] at hx ⊢
  rw [hx]

/-- **The `L¹` bound of the weighted box integral.** -/
theorem rhsGen_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {G : Xn n → ℝ} {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hGb : ∀ x ∈ abx n ℓ, ‖G x‖ ≤ Bc) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {e : E3 → E3 → ℝ}
    (he : AEStronglyMeasurable (Function.uncurry e)
      ((volume : Measure E3).prod (volume : Measure E3)))
    (hfin : boxL1 ℓ e < ⊤) :
    |∫ x in abx n ℓ, G x * e (x p.1) (x p.2)|
      ≤ Bc * (ℓ ^ 3) ^ (n - 2) * (boxL1 ℓ e).toReal := by
  have h := rhs_enorm_le hℓ hBc hGb hp he
  have hvol : (volume : Measure E3) (acb ℓ) = ENNReal.ofReal (ℓ ^ 3) :=
    Submission.BoseGases.acube_volume ℓ hℓ.le
  have hpow : (ENNReal.ofReal (ℓ ^ 3) : ENNReal) ^ (n - 2)
      = ENNReal.ofReal ((ℓ ^ 3) ^ (n - 2)) :=
    (ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ ^ 3) (n - 2)).symm
  rw [hvol, hpow] at h
  have hfin' : ENNReal.ofReal Bc * ENNReal.ofReal ((ℓ ^ 3) ^ (n - 2)) * boxL1 ℓ e ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ne_of_lt hfin)
  calc |∫ x in abx n ℓ, G x * e (x p.1) (x p.2)|
      = (‖∫ x in abx n ℓ, G x * e (x p.1) (x p.2)‖ₑ).toReal := by
          rw [toReal_enorm, Real.norm_eq_abs]
    _ ≤ (ENNReal.ofReal Bc * ENNReal.ofReal ((ℓ ^ 3) ^ (n - 2)) * boxL1 ℓ e).toReal :=
        ENNReal.toReal_mono hfin' h
    _ = Bc * (ℓ ^ 3) ^ (n - 2) * (boxL1 ℓ e).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hBc,
          ENNReal.toReal_ofReal (by positivity)]

/-- Linearity of the weighted box integral in the pair kernel. -/
theorem rhsGen_linear {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {G : Xn n → ℝ} (hG : Continuous G)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) {e₁ e₂ : E3 → E3 → ℝ}
    (hm₁ : AEStronglyMeasurable (Function.uncurry e₁)
      ((volume : Measure E3).prod (volume : Measure E3)))
    (hm₂ : AEStronglyMeasurable (Function.uncurry e₂)
      ((volume : Measure E3).prod (volume : Measure E3)))
    (hi₁ : boxL1 ℓ e₁ < ⊤) (hi₂ : boxL1 ℓ e₂ < ⊤) :
    (∫ x in abx n ℓ, G x * e₁ (x p.1) (x p.2))
        - (∫ x in abx n ℓ, G x * e₂ (x p.1) (x p.2))
      = ∫ x in abx n ℓ, G x * (e₁ (x p.1) (x p.2) - e₂ (x p.1) (x p.2)) := by
  rw [← MeasureTheory.integral_sub (rhs_integrableOn hℓ hG hp hm₁ hi₁)
    (rhs_integrableOn hℓ hG hp hm₂ hi₂)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

end Work.BoseBoxFock
