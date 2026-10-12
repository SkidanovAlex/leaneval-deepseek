import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.continuous_integral_tBamp_sq
import Submission.Work.SmallBoxTBWord.fderiv_boxQ_kcDir
import Submission.Work.SmallBoxTBWord.tBamp_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the `𝒯_B`-amplitude `p`-integrand

`tBdiagForm` (and hence `tBwordKin`) is a sum of Bochner integrals
`(2π)⁻³∫_p F(‖p‖)·(a³)⁻¹∫_{abox}‖tBamp χ p (Q_{B,i}Ψ) i x‖²`, and any comparison argument
between two symbols (`Basic.tBdiagForm_mono`) needs the `p`-integrand to be `Integrable` for
the *larger* symbol, so that `integral_mono_of_nonneg` applies.  This module supplies that
integrability for the symbol `F = ‖·‖²`, i.e. the weight actually used in
`tBwordKin_le_kinWord`.

## The argument

* `tBamp χ p Φ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Φ(x_{i←z})dz` (with `Φ = Q_{B,i}Ψ`) is, for fixed
  `x ∈ abox (n+1) a`, the Fourier transform of the compactly supported smooth fibre
  `z ↦ χ(z)Φ(x_{i←z})`; the decay `tBamp_decay` gives `‖tBamp χ p Φ i x‖ ≤ C(1+‖p‖)^{-3}`
  uniformly in `x ∈ abox` and in the slot.
* Squaring and integrating over `abox (n+1) a` (of volume `(a³)^{n+1}`, `abox_volume`) bounds the
  `x`-integral by `(C(1+‖p‖)^{-3})²(a³)^{n+1}`, so the `p`-integrand is dominated by
  `C²(a³)^n·‖p‖²(1+‖p‖)^{-6}`, which is integrable in dimension `3` because `6 > 4 = 3+1`
  (`Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow`).
* The `p`-integrand is continuous (`continuous_integral_tBamp_sq`), hence a.e. strongly
  measurable, so `Integrable.mono'` applies.
* For `a ≤ 0` the box `abox (n+1) a` is contained in the single point `abox (n+1) 0`, a null
  set, so the inner integral vanishes identically and the statement is trivial.  (The statement
  is unconditional in `a`, so this case must be handled.)

## The one-body box projection

`Q_{B,i}Ψ = Ψ − P_{B,i}Ψ` is `C^∞` because the box `A` is compact
(`boxQ_contDiff_of_compact`), which is what allows `tBamp_decay` to be applied to `Φ = Q_{B,i}Ψ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **Smoothness of the box mean-free projection.**  For a compact box `A`, the mean
`P_{B,i}Φ = (1/volA)∫_{z∈A}Φ(x_{i←z})dz` is smooth (differentiation under the integral sign over a
compact set), hence so is `Q_{B,i}Φ = Φ − P_{B,i}Φ`. -/
theorem boxQ_contDiff_of_compact {N : ℕ} {A : Set ℝ³} (hA : IsCompact A) (volA : ℝ)
    (i : Fin N) {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ContDiff ℝ (⊤ : ENat) (boxQ volA A i Φ) := by
  have hU : ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => Function.update q.1 i q.2) :=
    contDiff_update_pair i
  have hF : ContDiff ℝ (⊤ : ENat)
      (Function.uncurry (fun (p : X N) (z : ℝ³) => Φ (Function.update p i z))) :=
    hΦ.comp hU
  have hmain : ContDiff ℝ (⊤ : ENat)
      (fun p : X N => ∫ z in A, Φ (Function.update p i z)) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (F := fun (p : X N) (z : ℝ³) =>
      Φ (Function.update p i z)) hA hF
  have hboxP : ContDiff ℝ (⊤ : ENat) (boxP volA A i Φ) := by
    rw [show boxP volA A i Φ =
      fun y : X N => (1 / volA) * ∫ z in A, Φ (Function.update y i z) from rfl]
    exact contDiff_const.mul hmain
  rw [show boxQ volA A i Φ = Φ - boxP volA A i Φ from rfl]
  exact hΦ.sub hboxP


theorem tBampForm_integrable {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ} (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ) (hA : IsCompact A) {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) a, ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2)) := by
  classical
  set Φ : X (n + 1) → ℝ := boxQ volA A i Ψ with hΦdef
  have hΦ : ContDiff ℝ (⊤ : ENat) Φ := boxQ_contDiff_of_compact hA volA i hΨ
  by_cases ha : a ≤ 0
  · -- the box is null: the inner integral vanishes identically
    have hsub : abox (n + 1) a ⊆ abox (n + 1) 0 := by
      intro x hx
      rw [mem_abox_iff] at hx ⊢
      intro j
      have hj : x j ∈ acube a := hx j
      rw [mem_acube_iff] at hj ⊢
      intro m
      have hb := hj m
      rw [Set.mem_Icc] at hb ⊢
      exact ⟨by linarith [hb.1, hb.2, ha], by linarith [hb.1, hb.2, ha]⟩
    have h0 : (volume : Measure (X (n + 1))) (abox (n + 1) 0) = 0 := by
      rw [abox_volume (n + 1) 0 le_rfl]
      norm_num
    have habox : (volume : Measure (X (n + 1))) (abox (n + 1) a) = 0 :=
      le_antisymm (le_trans (measure_mono hsub) (le_of_eq h0)) zero_le
    have hres : (volume : Measure (X (n + 1))).restrict (abox (n + 1) a) = 0 :=
      Measure.restrict_eq_zero.mpr habox
    have hzero : ∀ p : ℝ³, ‖p‖ ^ 2 * ((a ^ 3)⁻¹ *
        ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2) = 0 := by
      intro p
      have hz : (∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2) = 0 := by
        rw [show (∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
            = ∫ x, ‖tBamp χ p Φ i x‖ ^ 2
                ∂((volume : Measure (X (n + 1))).restrict (abox (n + 1) a)) from rfl, hres]
        exact MeasureTheory.integral_zero_measure _
      rw [hz, mul_zero, mul_zero]
    exact (MeasureTheory.integrable_zero ℝ³ ℝ volume).congr
      (Filter.Eventually.of_forall (fun p => (hzero p).symm))
  · push_neg at ha
    -- the fibre amplitude decays like `(1+‖p‖)^{-3}` uniformly on the box
    have hcont : Continuous (fun p : ℝ³ =>
        ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2) :=
      continuous_integral_tBamp_sq (N := n + 1) ha hχ.continuous hcs hΦ.continuous i
    obtain ⟨C, hC0, hC⟩ := tBamp_decay (N := n + 1) ha hχ hcs hΦ
    have hreal : ((volume : Measure (X (n + 1))).restrict (abox (n + 1) a)).real Set.univ
        = (a ^ 3) ^ (n + 1) := by
      rw [Measure.real_def, Measure.restrict_apply_univ, abox_volume (n + 1) a ha.le,
        ENNReal.toReal_ofReal (by positivity)]
    -- the `x`-integral is bounded by the decay constant squared times the volume of the box
    have hIntBound : ∀ p : ℝ³, (∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
        ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 * (a ^ 3) ^ (n + 1) := by
      intro p
      set D : ℝ := (C / (1 + ‖p‖) ^ 3) ^ 2 with hDdef
      have hg : Integrable (fun _ : X (n + 1) => D)
          ((volume : Measure (X (n + 1))).restrict (abox (n + 1) a)) :=
        integrableOn_const (abox_lt_top (n + 1) a ha.le).ne
          (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
      have hle : ∀ᵐ x ∂((volume : Measure (X (n + 1))).restrict (abox (n + 1) a)),
          ‖tBamp χ p Φ i x‖ ^ 2 ≤ D := by
        rw [ae_restrict_iff' (abox_measurable (n + 1) a)]
        filter_upwards with x hx
        rw [hDdef]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC x hx i p) 2
      have hmono := integral_mono_of_nonneg
        (μ := (volume : Measure (X (n + 1))).restrict (abox (n + 1) a))
        (f := fun x : X (n + 1) => ‖tBamp χ p Φ i x‖ ^ 2)
        (g := fun _ : X (n + 1) => D)
        (Eventually.of_forall (fun x => sq_nonneg _)) hg hle
      calc (∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
          = ∫ x, ‖tBamp χ p Φ i x‖ ^ 2
              ∂((volume : Measure (X (n + 1))).restrict (abox (n + 1) a)) := rfl
        _ ≤ ∫ x, D ∂((volume : Measure (X (n + 1))).restrict (abox (n + 1) a)) := hmono
        _ = D * (a ^ 3) ^ (n + 1) := by rw [integral_const, smul_eq_mul, hreal, mul_comm]
        _ = (C / (1 + ‖p‖) ^ 3) ^ 2 * (a ^ 3) ^ (n + 1) := by rw [hDdef]
    -- the `p`-integrand is dominated by `C²(a³)^n·‖p‖²(1+‖p‖)^{-6}`
    have hkey : ∀ p : ℝ³, ‖p‖ ^ 2 * ((a ^ 3)⁻¹ *
        ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
        ≤ (C ^ 2 * (a ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by
      intro p
      have ha3 : a ^ 3 ≠ 0 := ne_of_gt (pow_pos ha 3)
      have hpd : (1 + ‖p‖) ≠ 0 := by positivity
      calc ‖p‖ ^ 2 * ((a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
          ≤ ‖p‖ ^ 2 * ((a ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 * (a ^ 3) ^ (n + 1))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hIntBound p) (by positivity)) (sq_nonneg _)
        _ = (C ^ 2 * (a ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by
            rw [div_pow, ← pow_mul, pow_succ]
            norm_num
            field_simp
            ring
    have hdom : Integrable (fun p : ℝ³ =>
        (C ^ 2 * (a ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6)) :=
      (Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow 6 le_rfl).const_mul _
    refine hdom.mono' ?_ ?_
    · exact ((continuous_norm.pow 2).mul (continuous_const.mul hcont)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))))]
      exact hkey p

end Work.SmallBoxTBWord
