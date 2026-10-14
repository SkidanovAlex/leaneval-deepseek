import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Vocab
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.FaCoefSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `rl¹`-engine with an energetic coefficient.**

Let `N` obey `|K θ · N r θ| ≤ |A r θ| · |B r θ|` on the open quadrant, let `A` be bounded in
`L²(θ)` by `√(C Ψ r)` at every radius and let `B` have angular energy at most `Φ r`
(`∫⁻_θ ofReal (B r θ²) ≤ ofReal (Φ r)`).  Then

  `Fa N ≤ ofReal (√C · √(π/2) · √(∫Ψ) · √(∫ r⁻²Φ))`.

The two square roots of the right-hand side are the `θ`- and `r`-Cauchy–Schwarz losses. -/
theorem Fa_le_coef_slot {N A B : Fn} {C Ys Zs : ℝ} {Ψ Φ : ℝ → ℝ}
    (hC : 0 ≤ C) (hYs : 0 ≤ Ys) (hZs : 0 ≤ Zs)
    (hΨnn : ∀ r, 0 ≤ Ψ r)
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)))
    (hΨle : (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Ys)
    (hΦnn : ∀ r, 0 ≤ Φ r)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦint : MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)))
    (hΦle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r) ≤ Zs)
    (hAmeas : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => A r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBmeas : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => B r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBsq : ∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2)
      Work.Spaces.Iθ)
    (hAb : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (A r θ) ^ 2 ≤ C * Ψ r)
    (hB : ∀ r, 0 < r → (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      ≤ ENNReal.ofReal (Φ r))
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ |A r θ| * |B r θ|) :
    Fa N ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys
      * Real.sqrt Zs) := by
  -- ## Step 1: the `θ`-bound at a fixed radius `r > 0`
  have hinner : ∀ r, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2) * Real.sqrt (Φ r)) := by
    intro r hr
    have hCΨ : 0 ≤ C * Ψ r := mul_nonneg hC (hΨnn r)
    have hsCΨ : 0 ≤ Real.sqrt (C * Ψ r) := Real.sqrt_nonneg _
    -- the pointwise a.e. domination by `√(CΨ r)·|B|`
    have hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|
          ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r)) * ENNReal.ofReal |B r θ| := by
      filter_upwards [hAb r hr,
        Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
          (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun θ hθ => hθ)] with θ hAθ hθ
      have hAabs : |A r θ| ≤ Real.sqrt (C * Ψ r) := Real.abs_le_sqrt hAθ
      have h1 : |Work.Spaces.K θ * N r θ| ≤ Real.sqrt (C * Ψ r) * |B r θ| :=
        (hpt r hr θ hθ).trans (mul_le_mul_of_nonneg_right hAabs (abs_nonneg _))
      rw [← ENNReal.ofReal_mul hsCΨ]
      exact ENNReal.ofReal_le_ofReal h1
    have hstep1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r))
          * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ| :=
      (MeasureTheory.lintegral_mono_ae hdom).trans_eq
        (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    -- the `B`-slot bound
    have hsqrtB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * ENNReal.ofReal (Real.sqrt (Φ r)) := by
      have h1 := lintegral_abs_le_sqrt (B := B) (r := r) (hBmeas r hr) (hBsq r hr)
      have h2 : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
          = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2) :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hBsq r hr)
          (Eventually.of_forall fun θ => sq_nonneg (B r θ))
      have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) ≤ Real.sqrt (Φ r) :=
        Real.sqrt_le_sqrt
          ((ENNReal.ofReal_le_ofReal_iff (hΦnn r)).mp (h2 ▸ hB r hr))
      calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)
          ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) ^ (1 / 2 : ℝ) := h1
        _ = ENNReal.ofReal (Real.sqrt (Real.pi / 2))
              * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)) := by
            rw [ofReal_rpow_half (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
        _ ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * ENNReal.ofReal (Real.sqrt (Φ r)) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal h4) _
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r))
            * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ| := hstep1
      _ ≤ ENNReal.ofReal (Real.sqrt (C * Ψ r))
            * (ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * ENNReal.ofReal (Real.sqrt (Φ r))) :=
          mul_le_mul_right hsqrtB _
      _ = ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2)
            * Real.sqrt (Φ r)) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (Real.pi / 2)),
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg (C * Ψ r))]
          ring_nf
  -- ## Step 2: the radial Cauchy–Schwarz
  set θw : ℝ → ℝ := fun r => |r⁻¹| * Real.sqrt (Φ r) with hθwdef
  set M : ℝ → ℝ := fun r => Real.sqrt (C * Ψ r) with hMdef
  have hθwnn : ∀ r, 0 ≤ θw r :=
    fun r => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hMnn : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  have hθwmeas : AEMeasurable θw (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun r : ℝ => |r⁻¹|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_inv.abs).aemeasurable
    have h2 : AEMeasurable (fun r : ℝ => Real.sqrt (Φ r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hΦmeas
    exact h1.mul h2
  have hθwint : MeasureTheory.IntegrableOn (fun r => (θw r) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hΦint
      (fun r _ => by
        rw [hθwdef, mul_pow, sq_abs, Real.sq_sqrt (hΦnn r)]) measurableSet_Ioi
  have hMle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), (M r) ^ 2 ≤ C * Ψ r :=
    Eventually.of_forall fun r => le_of_eq (Real.sq_sqrt (mul_nonneg hC (hΨnn r)))
  have houter := outer_gen (C := C) hC hθwnn hMnn hΨnn hθwmeas hΨmeas hθwint hΨint hMle
  have hθwval : ∀ r, 0 < r → θw r = r⁻¹ * Real.sqrt (Φ r) := by
    intro r hr
    show |r⁻¹| * Real.sqrt (Φ r) = r⁻¹ * Real.sqrt (Φ r)
    rw [abs_of_pos (inv_pos.mpr hr)]
  have hθw2le : (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2) ≤ Zs := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
        rw [hθwval r hr, mul_pow, Real.sq_sqrt (hΦnn r)])
    rw [h1]
    exact hΦle
  have hΨY : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Real.sqrt Ys :=
    Real.sqrt_le_sqrt hΨle
  rw [Fa]
  have hBigA : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (θw r) * ENNReal.ofReal (M r)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    have hkey : ENNReal.ofReal r⁻¹
        * ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2) * Real.sqrt (Φ r))
        = ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (θw r) * ENNReal.ofReal (M r)) := by
      have hA : 0 ≤ Real.sqrt (C * Ψ r) := Real.sqrt_nonneg _
      have hB0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
      have hC0 : 0 ≤ Real.sqrt (Φ r) := Real.sqrt_nonneg _
      rw [hθwval r hr0, hMdef]
      rw [show ENNReal.ofReal (Real.sqrt (C * Ψ r) * Real.sqrt (Real.pi / 2)
              * Real.sqrt (Φ r))
            = ENNReal.ofReal (Real.sqrt (C * Ψ r)) * ENNReal.ofReal (Real.sqrt (Real.pi / 2))
              * ENNReal.ofReal (Real.sqrt (Φ r)) from by
          rw [ENNReal.ofReal_mul (mul_nonneg hA hB0), ENNReal.ofReal_mul hA],
        show ENNReal.ofReal (r⁻¹ * Real.sqrt (Φ r))
            = ENNReal.ofReal r⁻¹ * ENNReal.ofReal (Real.sqrt (Φ r)) from
          ENNReal.ofReal_mul hinv]
      ring
    exact (mul_le_mul_right (hinner r hr0) _).trans_eq hkey
  have hBigB : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt (Real.pi / 2))
        * (ENNReal.ofReal (θw r) * ENNReal.ofReal (M r)))
      ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys
          * Real.sqrt Zs) := by
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [show ENNReal.ofReal (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys
          * Real.sqrt Zs)
        = ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * ENNReal.ofReal (Real.sqrt C * Real.sqrt Ys * Real.sqrt Zs) from by
      rw [show (Real.sqrt C * Real.sqrt (Real.pi / 2) * Real.sqrt Ys * Real.sqrt Zs : ℝ)
            = Real.sqrt (Real.pi / 2) * (Real.sqrt C * Real.sqrt Ys * Real.sqrt Zs) from by
          ring,
        ENNReal.ofReal_mul (Real.sqrt_nonneg (Real.pi / 2))]]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine houter.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hΨY (Real.sqrt_nonneg C))
      (Real.sqrt_le_sqrt hθw2le) (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg _))
  exact hBigA.trans hBigB

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- Change of variables `t = z u` for the interval integral over `(0,1)`. -/
lemma integral_comp_mul_left_zero_one (f : ℝ → ℝ) {z : ℝ} (hz : z ≠ 0) :
    ∫ u in (0 : ℝ)..1, f (z * u) = z⁻¹ * ∫ t in (0 : ℝ)..z, f t := by
  have h := intervalIntegral.integral_comp_mul_left (f := f) (a := (0 : ℝ)) (b := (1 : ℝ))
    (c := z) hz
  simpa using h

/-- Change of variables `t = z u` for the set integral over `Ioi 1`. -/
lemma integral_comp_mul_left_Ioi_one (f : ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ u in Set.Ioi (1 : ℝ), f (z * u) = z⁻¹ * ∫ t in Set.Ioi z, f t := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi f (1 : ℝ) hz
  simpa using h

/-- The rescaled form of `∫₀^z c t t^s dt`:
`∫ u in (0)..1, c (z*u) * u^s = z^{-(s+1)} · ∫ t in (0)..z, c t * t^s` for `z > 0`. -/
lemma integral_zero_one_rpow (c : ℝ → ℝ) (s : ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ u in (0 : ℝ)..1, c (z * u) * u ^ s
      = z ^ (-(s + 1)) * ∫ t in (0 : ℝ)..z, c t * t ^ s := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hsub := integral_comp_mul_left_zero_one (fun t => c t * t ^ s) hz0
  have hcongr : ∫ u in (0 : ℝ)..1, c (z * u) * (z * u) ^ s
      = ∫ u in (0 : ℝ)..1, z ^ s * (c (z * u) * u ^ s) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := by
      have h1 : u ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
      exact h1.1
    show c (z * u) * (z * u) ^ s = z ^ s * (c (z * u) * u ^ s)
    rw [Real.mul_rpow (le_of_lt hz) hu0]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul] at hsub
  have h1 : z ^ (-s) * z ^ s = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have h2 : z ^ (-s) * z⁻¹ = z ^ (-(s + 1)) := by
    rw [← Real.rpow_neg_one z, ← Real.rpow_add hz]
    congr 1
    ring
  calc ∫ u in (0 : ℝ)..1, c (z * u) * u ^ s
      = z ^ (-s) * (z ^ s * ∫ u in (0 : ℝ)..1, c (z * u) * u ^ s) := by
        rw [← mul_assoc, h1, one_mul]
    _ = z ^ (-s) * (z⁻¹ * ∫ t in (0 : ℝ)..z, c t * t ^ s) := by rw [hsub]
    _ = z ^ (-(s + 1)) * ∫ t in (0 : ℝ)..z, c t * t ^ s := by
        rw [← mul_assoc, h2]

/-- The rescaled form of `∫_{Ioi z} c t t^s dt`:
`∫ u in Ioi 1, c (z*u) * u^s = z^{-(s+1)} · ∫ t in Ioi z, c t * t^s` for `z > 0`. -/
lemma integral_Ioi_one_rpow (c : ℝ → ℝ) (s : ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ s
      = z ^ (-(s + 1)) * ∫ t in Set.Ioi z, c t * t ^ s := by
  have hsub := integral_comp_mul_left_Ioi_one (fun t => c t * t ^ s) hz
  have hcongr : ∫ u in Set.Ioi (1 : ℝ), c (z * u) * (z * u) ^ s
      = ∫ u in Set.Ioi (1 : ℝ), z ^ s * (c (z * u) * u ^ s) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : 0 ≤ u := le_of_lt (lt_trans zero_lt_one hu1)
    show c (z * u) * (z * u) ^ s = z ^ s * (c (z * u) * u ^ s)
    rw [Real.mul_rpow (le_of_lt hz) hu0]
    ring
  rw [hcongr, MeasureTheory.integral_const_mul] at hsub
  have h1 : z ^ (-s) * z ^ s = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have h2 : z ^ (-s) * z⁻¹ = z ^ (-(s + 1)) := by
    rw [← Real.rpow_neg_one z, ← Real.rpow_add hz]
    congr 1
    ring
  calc ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ s
      = z ^ (-s) * (z ^ s * ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ s) := by
        rw [← mul_assoc, h1, one_mul]
    _ = z ^ (-s) * (z⁻¹ * ∫ t in Set.Ioi z, c t * t ^ s) := by rw [hsub]
    _ = z ^ (-(s + 1)) * ∫ t in Set.Ioi z, c t * t ^ s := by
        rw [← mul_assoc, h2]

theorem radGreen_eq_rescaled {α : ℝ} (hα : 0 < α) (m : ℕ) (c : ℝ → ℝ) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.PhiStar.Radial.radGreen α m c z
        = Work.FTS.PhiStar.RadialWAux.radK α m
            * (Work.FTS.PhiStar.RadialWAux.radPhi α m c z
              + Work.FTS.PhiStar.RadialWAux.radPsi α m c z) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  intro z hz
  have hq := integral_zero_one_rpow c (radQ α m - 1) hz
  have hp := integral_Ioi_one_rpow c (-(radP α m) - 1) hz
  simp only [Work.FTS.PhiStar.Radial.radGreen, radK, radPhi, radPsi] at *
  dsimp only [radQ, radP] at *
  have hexp1 : -(((2 * (m : ℝ) + 5) / α - 1) + 1) = -(2 * (m : ℝ) + 5) / α := by
    rw [sub_add_cancel, neg_div]
  have hexp2 : -(-(2 * (m : ℝ) / α) - 1 + 1) = 2 * (m : ℝ) / α := by
    rw [sub_add_cancel, neg_neg]
  rw [hq, hp, hexp1, hexp2]

end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- The `k`-th differentiated kernel of `radPhi`, i.e. the parametric integral
`z ↦ ∫ u in (0)..1, c^{(k)}(z * u) * u^{k + q - 1}`.  `radPhi_iteratedDeriv` says that this is
`iteratedDeriv k (radPhi α m c)`; the differentiation is differentiated under the integral sign
over the *fixed* interval `(0,1)`. -/
private def radPhiKernel (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1)

/-- On `Ioi 0`, where `c` is `C^22`, the `k`-th iterated derivative of `c` is differentiable
as soon as `k < 22`. -/
private lemma differentiableAt_iteratedDeriv {c : ℝ → ℝ} (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    {k : ℕ} (hk : k < 22) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (iteratedDeriv k c) y := by
  have hEq : Set.EqOn (iteratedDeriv k c) (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) := by
    intro t ht
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_of_lt hk))
      ht).symm
  have hd : DifferentiableOn ℝ (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)

/-- The kernel integrand `u ↦ c^{(k)}(x u) u^{k + q - 1}` is a.e. strongly measurable on `(0,1]`
for `x > 0`, `k ≤ 22`.  (Measurability only fails at the single point `u = 0`, where `c` is only
known to be `C^22` on `(0,∞)` and where `u^{k+q-1}` may blow up.) -/
private lemma aestronglyMeasurable_kernel {c : ℝ → ℝ} (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    {q : ℝ} {k : ℕ} (hk : k ≤ 22) {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
  have hw : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_Ioi 0)
  have hmaps : Set.MapsTo (fun u : ℝ => x * u) (Set.Ioo 0 1) (Set.Ioi 0) :=
    fun u hu => mul_pos hx hu.1
  have h1 : ContinuousOn (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u))
      (Set.Ioo 0 1) :=
    hw.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have h2 : Set.EqOn (fun u : ℝ => iteratedDeriv k c (x * u))
      (fun u : ℝ => iteratedDerivWithin k c (Set.Ioi 0) (x * u)) (Set.Ioo 0 1) := by
    intro u hu
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
      ((hc.contDiffAt (isOpen_Ioi.mem_nhds (hmaps hu))).of_le (by exact_mod_cast hk))
      (hmaps hu)).symm
  have h3 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioo 0 1) := h1.congr h2
  have h4 : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) + q - 1)) (Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (ne_of_gt hu.1))
  have h5 : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (h3.mul h4).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [show (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
        = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
    (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc).symm]

/-- The kernel integrand is integrable on `(0,1]`, dominated by `K u^{k+q-1}`. -/
private lemma integrableOn_kernel {c : ℝ → ℝ} {K q : ℝ} (hK : 0 ≤ K) (hq : 0 < q)
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) {k : ℕ} (hk : k ≤ 22) {x : ℝ} (hx : 0 < x)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1))) :
    IntegrableOn (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + q - 1))
      (Set.Ioc 0 1) volume := by
  have hr : (-1 : ℝ) < (k : ℝ) + q - 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
    linarith
  have hg : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) + q - 1))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h1 : IntervalIntegrable (fun u : ℝ => u ^ ((k : ℝ) + q - 1)) volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' hr
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at h1
    exact h1.const_mul K
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
  exact mul_le_mul_of_nonneg_right (hb k hk (x * u) (mul_pos hx hu0))
    (Real.rpow_nonneg (le_of_lt hu0) _)

/-- Differentiation under the integral sign for the kernel of `radPhi`: passing from the `k`-th to
the `(k+1)`-st kernel multiplies the `u`-weight by `u`. -/
private lemma hasDerivAt_radPhiKernel {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) {k : ℕ} (hk : k + 1 ≤ 22) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (radPhiKernel α m c k) (radPhiKernel α m c (k + 1) z) z := by
  have hq : 0 < radQ α m := radQ_pos hα m
  have hkle : k ≤ 22 := by omega
  have hklt : k < 22 := by omega
  have hr : (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) + radQ α m - 1 := by
    have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aestronglyMeasurable_kernel hc hkle hx
  have hF_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact integrableOn_kernel hK hq hb hkle hz (aestronglyMeasurable_kernel hc hkle hz)
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (k + 1) c (z * u)
        * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact aestronglyMeasurable_kernel hc hk hz
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)‖
        ≤ K * t ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1) := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) hk (x * t) (mul_pos hx ht0))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t) * t ^ ((k : ℝ) + radQ α m - 1))
        (iteratedDeriv (k + 1) c (x * t) * t ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1)) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have hxt : 0 < x * t := mul_pos hx ht0
    have hgd : HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c (x * t)) (x * t) := by
      simpa only [iteratedDeriv_succ] using
        (differentiableAt_iteratedDeriv hc hklt hxt).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv k c (y * t))
        (iteratedDeriv (k + 1) c (x * t) * t) x := by
      simpa only [Function.comp_def] using hgd.comp x hlin
    have hmul := hcomp.mul_const (t ^ ((k : ℝ) + radQ α m - 1))
    have hexp : (((k + 1 : ℕ) : ℝ) + radQ α m - 1) = ((k : ℝ) + radQ α m - 1) + 1 := by
      push_cast; ring
    rw [hexp]
    refine hmul.congr_deriv ?_
    rw [Real.rpow_add ht0, Real.rpow_one]
    ring
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) + radQ α m - 1))
    (F' := fun x u => iteratedDeriv (k + 1) c (x * u)
      * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
    (x₀ := z) (s := Set.Ioi 0) (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (bound := fun u : ℝ => K * u ^ (((k + 1 : ℕ) : ℝ) + radQ α m - 1))
    hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2
  exact hmain

theorem radPhi_iteratedDeriv {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 22 → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z
        = ∫ u in (0 : ℝ)..1,
            iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
  have key : ∀ k : ℕ, 0 ≤ k → k ≤ 22 → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (radPhi α m c) z = radPhiKernel α m c k z :=
    Nat.le_induction (m := 0)
      (P := fun n _ => n ≤ 22 → ∀ z : ℝ, 0 < z →
        iteratedDeriv n (radPhi α m c) z = radPhiKernel α m c n z)
      (by
        intro _ z _
        simp only [radPhiKernel, radPhi, iteratedDeriv_zero, Nat.cast_zero, zero_add])
      (by
        intro n _ ih hn22 z hz
        have hnle : n ≤ 22 := by omega
        have h1 : deriv (iteratedDeriv n (radPhi α m c)) z
            = deriv (radPhiKernel α m c n) z := by
          refine Filter.EventuallyEq.deriv_eq ?_
          filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
          exact ih hnle y hy
        have h2 : deriv (radPhiKernel α m c n) z = radPhiKernel α m c (n + 1) z :=
          (hasDerivAt_radPhiKernel hα m hK hc hb hn22 hz).deriv
        rw [iteratedDeriv_succ, h1, h2])
  intro k hk z hz
  exact key k (Nat.zero_le k) hk z hz

/-- The crude bound that accompanies `radPhi_iteratedDeriv`: the `k`-th `z`-derivative of the
inner rescaled Green piece `radPhi α m c` is dominated by `K/(k + q)`, where `q = radQ α m ≥ 7`.
(It is the `∫ u in (0)..1, u^{k+q-1} = 1/(k+q)` moment of the differentiated kernel.) -/
theorem radPhi_iteratedDeriv_bound {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 22 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z|
        ≤ K / ((k : ℝ) + Work.FTS.PhiStar.RadialWAux.radQ α m) := by
  intro k hk z hz
  have hq : 0 < radQ α m := radQ_pos hα m
  have hkq : 0 < (k : ℝ) + radQ α m := by
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg k
    linarith
  have hr : (-1 : ℝ) < (k : ℝ) + radQ α m - 1 := by linarith
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have hg_int : IntervalIntegrable
      (fun u : ℝ => iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1))
      volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact integrableOn_kernel hK hq hb hk hz (aestronglyMeasurable_kernel hc hk hz)
  have hK_int : IntervalIntegrable
      (fun u : ℝ => K * u ^ ((k : ℝ) + radQ α m - 1)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have hae : ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      |iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1)|
        ≤ K * u ^ ((k : ℝ) + radQ α m - 1) := by
    rw [show (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
        = (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) from
      (Measure.restrict_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Icc).symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu0 : 0 < u := hu.1
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    exact mul_le_mul_of_nonneg_right (hb k hk (z * u) (mul_pos hz hu0))
      (Real.rpow_nonneg hu0.le _)
  have h1 : |iteratedDeriv k (radPhi α m c) z|
      ≤ ∫ u in (0 : ℝ)..1,
          |iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1)| := by
    rw [radPhi_iteratedDeriv hα m hK hc hb k hk z hz]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have h2 : (∫ u in (0 : ℝ)..1,
        |iteratedDeriv k c (z * u) * u ^ ((k : ℝ) + radQ α m - 1)|)
      ≤ ∫ u in (0 : ℝ)..1, K * u ^ ((k : ℝ) + radQ α m - 1) :=
    intervalIntegral.integral_mono_ae_restrict hab hg_int.abs hK_int hae
  have h3 : (∫ u in (0 : ℝ)..1, K * u ^ ((k : ℝ) + radQ α m - 1))
      = K / ((k : ℝ) + radQ α m) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr), Real.one_rpow,
      Real.zero_rpow (by linarith : (k : ℝ) + radQ α m - 1 + 1 ≠ 0), sub_zero,
      show (k : ℝ) + radQ α m - 1 + 1 = (k : ℝ) + radQ α m from by ring]
    ring
  linarith

end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.radPsi_integral_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

theorem radPsi_integral_bound {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 22 → (k : ℝ) < Work.FTS.PhiStar.RadialWAux.radP α m →
      ∀ z : ℝ, 0 < z →
        |∫ u in Set.Ioi 1,
            iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) - Work.FTS.PhiStar.RadialWAux.radP α m - 1)|
          ≤ K / (Work.FTS.PhiStar.RadialWAux.radP α m - (k : ℝ)) := by
  intro k hk hkp z hz
  have hlt : (k : ℝ) - radP α m - 1 < -1 := by linarith
  -- the dominating function is integrable on `(Ioi 1)`
  have hKint : Integrable (fun u : ℝ => K * u ^ ((k : ℝ) - radP α m - 1))
      (volume.restrict (Set.Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K
  -- the pointwise bound, a.e. on `(Ioi 1)`
  have hbnd : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ‖iteratedDeriv k c (z * u) * u ^ ((k : ℝ) - radP α m - 1)‖
        ≤ K * u ^ ((k : ℝ) - radP α m - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hrpow : 0 ≤ u ^ ((k : ℝ) - radP α m - 1) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow]
    exact mul_le_mul_of_nonneg_right (hb k hk (z * u) (mul_pos hz hu0)) hrpow
  -- the value of the model integral `∫_{u>1} u^{k-p-1} du = 1/(p-k)`
  have hInt : ∫ u in Set.Ioi 1, u ^ ((k : ℝ) - radP α m - 1)
      = 1 / (radP α m - (k : ℝ)) := by
    rw [integral_Ioi_rpow_of_lt (a := (k : ℝ) - radP α m - 1) hlt (c := 1) zero_lt_one,
      Real.one_rpow]
    have hden : ((k : ℝ) - radP α m - 1) + 1 = (k : ℝ) - radP α m := by ring
    rw [hden, div_eq_div_iff (by linarith : (k : ℝ) - radP α m ≠ 0)
      (by linarith : radP α m - (k : ℝ) ≠ 0)]
    ring
  have hmain : ‖∫ u in Set.Ioi 1,
        iteratedDeriv k c (z * u) * u ^ ((k : ℝ) - radP α m - 1)‖
      ≤ K / (radP α m - (k : ℝ)) := by
    calc ‖∫ u in Set.Ioi 1, iteratedDeriv k c (z * u) * u ^ ((k : ℝ) - radP α m - 1)‖
        ≤ ∫ u in Set.Ioi 1, K * u ^ ((k : ℝ) - radP α m - 1) :=
          norm_integral_le_of_norm_le hKint hbnd
      _ = K * (∫ u in Set.Ioi 1, u ^ ((k : ℝ) - radP α m - 1)) := by
          rw [integral_const_mul]
      _ = K / (radP α m - (k : ℝ)) := by rw [hInt]; ring
  simpa [Real.norm_eq_abs] using hmain

end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- On `(0,∞)` a `C^22` function has continuous `k`-th iterated derivative, `k ≤ 22`. -/
lemma radPsiAux_continuousOn_iteratedDeriv {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) {k : ℕ} (hk : k ≤ 22) :
    ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- The `(k+1)`-st iterated derivative is the derivative of the `k`-th one. -/
lemma radPsiAux_hasDerivAt_iteratedDeriv {c : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hc : ContDiffAt ℝ 22 c x) (hk : k < 22) :
    HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k c) x := by
    have h' := hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := k)
      (show ((k : ℕ) : WithTop ℕ∞) < ((22 : ℕ) : WithTop ℕ∞) by exact_mod_cast hk)
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv k c) (deriv (iteratedDeriv k c) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

/-- **Differentiation under the integral sign for the `Ψ`-kernel.**  If `c` is `C^22` on
`(0,∞)` with `|c^{(j)}| ≤ K` there, `k + 1 ≤ 22` and `k + 1 < p`, then at every `z > 0`

  `z ↦ ∫_{u > 1} c^{(k)}(z u) u^{k-p-1} du` has derivative `∫_{u>1} c^{(k+1)}(z u) u^{k-p} du`.

(The dominating function at this step is `K u^{k-p}`, integrable on `(Ioi 1)` because
`k - p < -1`.) -/
theorem radPsiAux_kernel_hasDerivAt {c : ℝ → ℝ} {K p : ℝ}
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv 22 c K)
    {k : ℕ} (hk22 : k + 1 ≤ 22) (hkp : (k : ℝ) + 1 < p) {z : ℝ} (hz : 0 < z) :
    HasDerivAt
      (fun x : ℝ => ∫ u in Set.Ioi 1, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
      (∫ u in Set.Ioi 1,
        iteratedDeriv (k + 1) c (z * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) z := by
  have hk22' : k ≤ 22 := by omega
  have hlt : (k : ℝ) - p < -1 := by linarith
  have hlt' : (k : ℝ) - p - 1 < -1 := by linarith
  have hcont_k : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) :=
    radPsiAux_continuousOn_iteratedDeriv hc hk22'
  have hcont_k1 : ContinuousOn (iteratedDeriv (k + 1) c) (Set.Ioi 0) :=
    radPsiAux_continuousOn_iteratedDeriv hc hk22
  have hne : ∀ u ∈ Set.Ioi (1 : ℝ), u ≠ 0 := fun u hu => ne_of_gt (lt_trans zero_lt_one hu)
  have hrpow : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) - p - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hrpow1 : ContinuousOn (fun u : ℝ => u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hcomp : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_k.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hcomp1 : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv (k + 1) c (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_k1.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 1)) (s := Set.Ioi (0 : ℝ)) (x₀ := z)
    (F := fun x u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
    (F' := fun x u : ℝ => iteratedDeriv (k + 1) c (x * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1))
    (bound := fun u : ℝ => K * u ^ ((k : ℝ) - p))
    (isOpen_Ioi.mem_nhds hz)
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ((hcomp x hx).mul hrpow).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine MeasureTheory.Integrable.mono'
        ((integrableOn_Ioi_rpow_of_lt hlt' zero_lt_one).const_mul K)
        (((hcomp z hz).mul hrpow).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu' _)]
      exact mul_le_mul_of_nonneg_right (hb k hk22' (z * u) (mul_pos hz hu'))
        (le_of_lt (Real.rpow_pos_of_pos hu' _)))
    (by exact ((hcomp1 z hz).mul hrpow1).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha' _),
        show (((k + 1 : ℕ) : ℝ) - p - 1) = (k : ℝ) - p from by push_cast; ring]
      exact mul_le_mul_of_nonneg_right (hb (k + 1) hk22 (x * a) (mul_pos hx ha'))
        (le_of_lt (Real.rpow_pos_of_pos ha' _)))
    (by exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      have hid : HasDerivAt (fun y : ℝ => y * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have hca : ContDiffAt ℝ 22 c (x * a) :=
        hc.contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hx ha'))
      have hd := radPsiAux_hasDerivAt_iteratedDeriv hca (by omega : k < 22)
      have hc' := hd.comp x hid
      have hfun : (iteratedDeriv k c ∘ fun y : ℝ => y * a) =
          fun y : ℝ => iteratedDeriv k c (y * a) := rfl
      rw [hfun] at hc'
      have hres := hc'.mul_const (a ^ ((k : ℝ) - p - 1))
      have hval : ((iteratedDeriv (k + 1) c (x * a) * a) * a ^ ((k : ℝ) - p - 1))
          = iteratedDeriv (k + 1) c (x * a) * a ^ (((k + 1 : ℕ) : ℝ) - p - 1) := by
        rw [show (((k + 1 : ℕ) : ℝ) - p - 1) = 1 + ((k : ℝ) - p - 1) from by push_cast; ring,
          Real.rpow_add ha', Real.rpow_one]
        ring
      rw [hval] at hres
      exact hres)
  exact hmain.2

theorem radPsi_iteratedDeriv {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ k : ℕ, k ≤ 22 → (k : ℝ) < Work.FTS.PhiStar.RadialWAux.radP α m → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z
        = ∫ u in Set.Ioi 1,
            iteratedDeriv k c (z * u)
              * u ^ ((k : ℝ) - Work.FTS.PhiStar.RadialWAux.radP α m - 1) := by
  intro k
  induction k with
  | zero =>
    intro _ _ z _
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_sub]
    rfl
  | succ k ih =>
    intro h22 hp z hz
    have hk22 : k ≤ 22 := by omega
    have hkp : (k : ℝ) + 1 < radP α m := by
      push_cast at hp ⊢
      exact hp
    have hkp' : (k : ℝ) < radP α m := by linarith
    have hstep := radPsiAux_kernel_hasDerivAt (p := radP α m) (K := K) hc hb h22 hkp hz
    have hev : iteratedDeriv k (radPsi α m c) =ᶠ[𝓝 z]
        (fun x : ℝ => ∫ u in Set.Ioi 1,
          iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - radP α m - 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ih hk22 hkp' x hx
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact hstep.deriv

end Work.FTS.PhiStar.RadialWAux
end
end
