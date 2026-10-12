import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.W1_mass_bounds` — the mass of `W₁`, two-sided

`W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g₀)` is the χ-renormalised one-body
kernel `g₀/(χ⋆χ)(·/ℓ)` of Fournais--Solovej.  This lemma bounds its total mass
`∫W₁` from both sides by the scattering-length mass `8π·a v`:

    8π·a v ≤ ∫W₁ ≤ 8π·a v·(1 + 2C(R/ℓ)²)

under the pointwise second-order condition `|(χ⋆χ)(x) − 1| ≤ C‖x‖²` for
`‖x‖ ≤ r₁` and the regime `R/ℓ ≤ r₁`, `C(R/ℓ)² ≤ 1/2` (`eq:W1-g` of
Fournais--Solovej), where `supp g₀ ⊆ ball 0 R`.

The substance is a.e.-pointwise: `Submission.BoseGases.wScaled_g0_ae_bounds`
gives `0 ≤ W₁ − g₀ ≤ 2C(R/ℓ)²·g₀` a.e.; integrability of `W₁` (which is *not*
`wScaled_g0_integrable`, that one needs the disjoint regime `R ≤ ℓ·chiR0`, not
implied here) follows from `W₁ = g₀·((χ⋆χ)(·/ℓ))⁻¹` being the product of the
integrable `g₀` with a measurable factor, dominated a.e. by
`(1 + 2C(R/ℓ)²)‖g₀‖` thanks to the *lower* half of the sandwich, and
`∫g₀ = 8π·a v` is `Submission.BoseGases.g0_integral`.  Both integral
comparisons are then `MeasureTheory.integral_mono_ae`.

Note (the `π`-trap of this workspace): the statement mentions `π`, so the
`Real` notation scope must be open for it to elaborate at all — `open scoped
Real` below makes `π` the constant `Real.pi`.
-/

open scoped Real

namespace Work.BoseBogFS

theorem W1_mass_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ r₁ C : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁) (hℓ : 0 < ℓ)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    8 * π * _root_.BoseGases.a v ≤ ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y
      ∧ ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y
        ≤ 8 * π * _root_.BoseGases.a v * (1 + 2 * C * (R / ℓ) ^ 2) := by
  -- the a.e. sandwich `g₀ ≤ W₁ ≤ (1 + 2C(R/ℓ)²)·g₀` (FS `eq:W1-g`)
  have hb : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x ∧
        Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x
          ≤ 2 * C * (R / ℓ) ^ 2 * Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R) (ℓ := ℓ)
      (r₁ := r₁) (C := C) hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hg_int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable (v := v) (R := R) hR hv_supp h
  have hg_nn : ∀ᵐ z : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  -- `W₁ = g₀·(χ⋆χ)(·/ℓ)⁻¹` is the product of the integrable `g₀` with a
  -- measurable factor
  have hWmeas : MeasureTheory.AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := by
    have hEq : Work.BoseFixR.W1fun v h ℓ
        = fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.g0 v h z * (Submission.BoseGases.convScale ℓ z)⁻¹ := by
      funext z
      simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, div_eq_mul_inv]
    rw [hEq]
    exact hg_int.aestronglyMeasurable.mul
      ((measurable_inv.comp
        (Submission.BoseGases.convScale_continuous ℓ).measurable).aestronglyMeasurable)
  -- domination: `‖W₁‖ ≤ (1 + 2C(R/ℓ)²)·‖g₀‖` a.e. (both halves of the sandwich)
  have hdom : ∀ᵐ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseFixR.W1fun v h ℓ z‖
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * ‖Submission.BoseGases.g0 v h z‖ := by
    filter_upwards [hb, hg_nn] with z hz hz0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [hz.1]),
      abs_of_nonneg hz0]
    nlinarith [hz.2]
  have hW_int : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    MeasureTheory.Integrable.mono' (hg_int.norm.const_mul _) hWmeas hdom
  -- the two integral comparisons
  have hlow : (∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z)
      ≤ ∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ z :=
    MeasureTheory.integral_mono_ae hg_int hW_int (by
      filter_upwards [hb] with z hz
      linarith [hz.1])
  have hup : (∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ z)
      ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
          (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h z :=
    MeasureTheory.integral_mono_ae hW_int (hg_int.const_mul _) (by
      filter_upwards [hb] with z hz
      nlinarith [hz.2])
  constructor
  · rw [← Submission.BoseGases.g0_integral (v := v) (R := R) hR hv_supp h]
    exact hlow
  · calc ∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ z
        ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
            (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h z := hup
      _ = (1 + 2 * C * (R / ℓ) ^ 2) * ∫ z : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.g0 v h z := MeasureTheory.integral_const_mul _ _
      _ = (1 + 2 * C * (R / ℓ) ^ 2) * (8 * π * _root_.BoseGases.a v) := by
            rw [Submission.BoseGases.g0_integral (v := v) (R := R) hR hv_supp h]
      _ = 8 * π * _root_.BoseGases.a v * (1 + 2 * C * (R / ℓ) ^ 2) := by ring

end Work.BoseBogFS
