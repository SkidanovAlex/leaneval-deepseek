import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter

/-- The restricted measure on `Iθ = [0,π/2]` is the restriction to the open interval, since the
two endpoints form a null set. -/
private theorem restrict_Iθ_eq_restrict_Ioo_local :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-- The integral of the constant `1` over `Iθ` is `π/2`. -/
private theorem integral_one_Iθ : (∫ _s in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- The pointwise Cauchy–Schwarz/AM–GM step: on the open angular interval the weight `σθ` is at
least `1`, so `|h| ≤ (h²·σθ + 1)/2` there. -/
private theorem abs_le_half_sq_mul_add {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |h s| ≤ (h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2 := by
  have hσ : 1 ≤ Work.FTS.EllipticEst.thEta s := one_le_thEta_of_mem_Ioo hs
  have hX2 : 0 ≤ h s ^ 2 := sq_nonneg _
  have h2 : 2 * |h s| ≤ h s ^ 2 + 1 := by
    nlinarith [sq_nonneg (|h s| - 1), sq_abs (h s)]
  nlinarith [h2, hX2, mul_le_mul_of_nonneg_left hσ hX2]

/-- The `L¹`–`L²` bound for an angular slice: `∫_{Iθ}|h| ≤ ½(∫_{Iθ}h²σθ + π/2)`. -/
private theorem integral_abs_le {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => h s ^ 2 * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ) :
    (∫ s in Work.Spaces.Iθ, |h s|)
      ≤ (1 / 2) * ((∫ s in Work.Spaces.Iθ, h s ^ 2 * Work.FTS.EllipticEst.thEta s)
          + Real.pi / 2) := by
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hInt1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const hIθ_ne_top (by simp)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun s : ℝ => h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) Work.Spaces.Iθ :=
    hint.add hInt1
  have hIntG : MeasureTheory.IntegrableOn
      (fun s : ℝ => ((h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.div_const hInt2 2
  have hpoint : (fun s : ℝ => |h s|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => (h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2) := by
    rw [restrict_Iθ_eq_restrict_Ioo_local]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun s hs => abs_le_half_sq_mul_add hs)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s => abs_nonneg (h s))) hIntG hpoint
  have hcalc : (∫ s in Work.Spaces.Iθ,
        (h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2)
      = (1 / 2) * ((∫ s in Work.Spaces.Iθ, h s ^ 2 * Work.FTS.EllipticEst.thEta s)
          + Real.pi / 2) := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hint hInt1, integral_one_Iθ]
    ring
  exact hmono.trans (le_of_eq hcalc)

theorem slice_abs_le {X : ℝ → ℝ → ℝ} {u ε θ : ℝ} (hu : 0 < u) (hε : 0 < ε)
    (hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => X u s ^ 2 * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => X u s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|)
      ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ / 2)
        * ((∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s) + Real.pi / 2) := by
  -- Write `c := 3 (ε · sMass)⁻¹`, the uniform bound on the kernel.
  set c : ℝ := 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact mul_pos (by norm_num) (inv_pos.mpr (mul_pos hε Work.FTS.EllSol.PkgK5.K5c.sMass_pos))
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hInt1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const hIθ_ne_top (by simp)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun s : ℝ => X u s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) Work.Spaces.Iθ :=
    hint.add hInt1
  have hIntDom : MeasureTheory.IntegrableOn
      (fun s : ℝ => (X u s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2)
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.div_const hInt2 2
  -- The dominating function: `|X u| ≤ (X u ² σθ + 1)/2` a.e. on `Iθ`.
  have hle : (fun s : ℝ => |X u s|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => (X u s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2) := by
    rw [restrict_Iθ_eq_restrict_Ioo_local]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun s hs => abs_le_half_sq_mul_add hs)
  -- Integrability of the slice of `X u`, from the hypothesis `hint` and the a.e.-strong
  -- measurability `haesm`.
  have hIntAbs : MeasureTheory.IntegrableOn (fun s : ℝ => |X u s|) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hIntDom haesm.norm (by
      filter_upwards [hle] with s hs
      simpa only [Real.norm_eq_abs, abs_abs] using hs)
  have hIntcAbs : MeasureTheory.IntegrableOn (fun s : ℝ => c * |X u s|) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.const_mul hIntAbs c
  have hpointKJ : (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => c * |X u s|) :=
    Filter.Eventually.of_forall (fun s =>
      mul_le_mul_of_nonneg_right (by
        rw [hcdef]; exact Work.FTS.EllSol.EllPkgAux.KJ_le hε θ s) (abs_nonneg _))
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|) :=
    Filter.Eventually.of_forall (fun s =>
      mul_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε θ s) (abs_nonneg _))
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn hIntcAbs hpointKJ
  calc (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|)
      ≤ ∫ s in Work.Spaces.Iθ, c * |X u s| := hmono
    _ = c * ∫ s in Work.Spaces.Iθ, |X u s| := MeasureTheory.integral_const_mul c _
    _ ≤ c * ((1 / 2) * ((∫ s in Work.Spaces.Iθ,
          X u s ^ 2 * Work.FTS.EllipticEst.thEta s) + Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left (integral_abs_le hint) hcpos.le
    _ = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ / 2)
        * ((∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s) + Real.pi / 2) := by
        rw [hcdef]; ring

end Work.FTS.EllSol.EllPkgAux.MollDom
