import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Fourier.continuous_integral_rawSlotAmp_sq
import Submission.Work.SmallBoxBridge.Fourier.exists_rawSlotAmp_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the `p`-space raw slot amplitude form

The kinetic bridge writes `𝒯₀` as `(2π)⁻³∫_p ‖p‖²·(s³)⁻¹∫_{abox}‖rawSlotAmp s p (Q_iΨ) i x‖²`
(`T0Form`); for the Bochner integral to be non-junk the `p`-integrand must be `Integrable`.

`rawSlotAmp s p Φ i x` is the Fourier transform (in `p`) of the compactly supported smooth
fibre `z ↦ χ_s(z)·Φ(x_{i↦z})`, so (by `exists_rawSlotAmp_decay`) it decays like
`(1+‖p‖)^{-3}` uniformly in `x ∈ abox` and in `i`.  Squaring and using the bounded volume of
`abox (n+1) s`, the whole `p`-integrand is dominated (for `x`-a.e. and, indeed, for all `x ∈
abox`) by `C²·(s³)^n·‖p‖²/(1+‖p‖)^6`, which is integrable in dimension `3` (the exponent `6`
exceeds the critical `4 = 3 + 1`).  The `p`-integrand is continuous
(`continuous_integral_rawSlotAmp_sq`), hence a.e. strongly measurable, so `Integrable.mono'`
closes the proof.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real ENNReal BigOperators

namespace Work.SmallBoxBridge.Fourier

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem integrable_rSlotAmp {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
      ((s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.rawSlotAmp s p (Submission.BoseGases.aQ s i Ψ) i x‖ ^ 2)) := by
  let Φ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ := Submission.BoseGases.aQ s i Ψ
  have hΦcd : ContDiff ℝ ∞ Φ := Submission.BoseGases.contDiff_aQ hs i hΨ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦcd.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC0, hC⟩ := exists_rawSlotAmp_decay (n := n) (s := s) hs (Ψ := Φ) hΦ3
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2) :=
    continuous_integral_rawSlotAmp_sq hs hΦcd.continuous i
  have hreal : ((volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.abox (n + 1) s)).real Set.univ = (s ^ 3) ^ (n + 1) := by
    rw [Measure.real_def, Measure.restrict_apply_univ,
      Submission.BoseGases.abox_volume (n + 1) s hs.le, ENNReal.toReal_ofReal (by positivity)]
  -- Pointwise bound on the `x`-integral, uniformly in `p`.
  have hIntBound : ∀ p : EuclideanSpace ℝ (Fin 3),
      ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2
      ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * (s ^ 3) ^ (n + 1) := by
    intro p
    set D : ℝ := (C / (1 + ‖p‖) ^ 3) ^ 2 with hDdef
    have hg : Integrable (fun _ : Fin (n + 1) → EuclideanSpace ℝ (Fin 3) => D)
        ((volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.abox (n + 1) s)) := by
      exact integrableOn_const ((Submission.BoseGases.abox_lt_top (n + 1) s hs.le).ne)
        (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
    have hle : ∀ᵐ x ∂((volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox (n + 1) s)),
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2 ≤ D := by
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) s)]
      filter_upwards with x hx
      rw [hDdef]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x hx i p) 2
    have hmono := integral_mono_of_nonneg
      (μ := (volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox (n + 1) s))
      (f := fun x : Fin (n + 1) → EuclideanSpace ℝ (Fin 3) =>
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2)
      (g := fun _ : Fin (n + 1) → EuclideanSpace ℝ (Fin 3) => D)
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hg hle
    calc ∫ x in Submission.BoseGases.abox (n + 1) s,
          ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2
        = ∫ x, ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2
            ∂((volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.abox (n + 1) s)) := rfl
      _ ≤ ∫ x, D ∂((volume : Measure (Fin (n + 1) → EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.abox (n + 1) s)) := hmono
      _ = D * (s ^ 3) ^ (n + 1) := by
          rw [integral_const, smul_eq_mul, hreal, mul_comm]
      _ = (C / (1 + ‖p‖) ^ 3) ^ 2 * (s ^ 3) ^ (n + 1) := by rw [hDdef]
  -- The `p`-integrand is dominated by `C²(s³)^n·‖p‖²/(1+‖p‖)^6`.
  have hkey : ∀ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
      ((s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2)
      ≤ (C ^ 2 * (s ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by
    intro p
    have hs3 : s ^ 3 ≠ 0 := ne_of_gt (pow_pos hs 3)
    have hpd : (1 + ‖p‖) ≠ 0 := by positivity
    calc ‖p‖ ^ 2 * ((s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
          ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2)
        ≤ ‖p‖ ^ 2 * ((s ^ 3)⁻¹ *
            ((C / (1 + ‖p‖) ^ 3) ^ 2 * (s ^ 3) ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hIntBound p) (by positivity)) (sq_nonneg _)
      _ = (C ^ 2 * (s ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by
          rw [div_pow, ← pow_mul, pow_succ]
          norm_num
          field_simp
          ring
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (C ^ 2 * (s ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6)) :=
    (Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow 6 le_rfl).const_mul _
  have hf_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
      ((s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2)) :=
    (continuous_norm.pow 2).mul (continuous_const.mul hcont)
  have hgoal : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
      ((s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.rawSlotAmp s p Φ i x‖ ^ 2)) := by
    refine hdom.mono' hf_cont.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))))]
    exact hkey p
  exact hgoal

end Work.SmallBoxBridge.Fourier
