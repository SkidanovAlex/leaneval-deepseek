import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_bsFamUnprojJoint
import Submission.Work.BSKinetic.integrable_bsFamUnprojSlice
import Submission.Work.BSKinetic.unproj_familyForm_eq
import Submission.Work.SmallBoxBridge.winModeForm_eq_kernelForm_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.familyFormUnproj_eq_kernelForm`

The **unprojected** one-body moving-box family form of FS's `lem:LocKinEn` is a *convolution
kernel form*:

    `∫_u (2π)⁻³∫_p F‖p‖·‖kinFT(χ_u·ψ) p‖²`
      `= ∫_x ∫_y (χ⋆χ)((x−y)/ℓ)/ℓ³ · K_F(x−y) · ψ x · ψ y`,

with `χ_u(x) = bsWin ℓ u x = χ(x/ℓ − u)` the big-box window family, `K_F = 𝓕⁻¹F` the kernel of
the radial symbol `F(‖·‖)` and `convScale ℓ` the scaled autocorrelation `(χ⋆χ)(·/ℓ)` of the bump.

This is the *kernel-form* counterpart of `Work.BSKinetic.unproj_familyForm_eq` (which computes
the `F = (·)²` case as the full-space Dirichlet word plus the window excess).

## Proof

1. **per-`u` kernel identity**: the unprojected form at fixed `u` is the quadratic form of the
   convolution operator with kernel `K_F` applied to the windowed state `χ_u ψ` — this is the
   `p`-convention Plancherel/Fubini computation of
   `Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm`, specialised to `χ_u`
   (`bsOneBodyUnproj_eq_iterKernel`);
2. **Fubini in `u`**: the joint integrand `(u,x,y) ↦ χ_u(x)ψ(x)K_F(x−y)χ_u(y)ψ(y)` is
   integrable (`integrable_bsFamUnprojJoint`), its `u`-slices too
   (`integrable_bsFamUnprojSlice`), so the `u`-integral can be moved inside the double integral;
3. **the `u`-integral of the window product**: for fixed `x,y`,
   `∫_u χ_u(x)χ_u(y) du = (χ⋆χ)((x−y)/ℓ) = convScale ℓ (x−y)` (the off-diagonal companion of
   the `L²`-partition `∫_u χ_u(x)² = 1`; this is `chiU_chiU_integral`);
4. pull the constant `K_F(x−y)ψ(x)ψ(y)` out of the `u`-integral.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- The family/kernel integrand at a triple `(u,x,y)`. -/
private noncomputable def bkiFam (ℓ : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) (u x y : ℝ³) : ℝ :=
  bsWin ℓ u x * ψ x * (kinKernel F (x - y) * (bsWin ℓ u y * ψ y))

/-- The `(x,y)`-integrand of the right hand side. -/
private noncomputable def bkiFinal (ℓ : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) (z : ℝ³ × ℝ³) : ℝ :=
  kinKernel F (z.1 - z.2) * (ψ z.1 * (ψ z.2 * convScale ℓ (z.1 - z.2)))

/-- The right-hand-side double integrand is integrable: it is a.e. strongly measurable (the
kernel through `kinKernel_stronglyMeasurable`), bounded (`kinKernel_bdd`, `abs_bsWin_le`,
`abs_convScale_le_one`) and supported in the compact square determined by `tsupport ψ`. -/
private lemma integrable_bkiFinal {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (bkiFinal ℓ F ψ) ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  obtain ⟨R, hR⟩ := (hcs.isCompact.isBounded).exists_norm_le
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hψ.continuous
  set B : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖ with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (ψ 0)) (hM 0)
  have hkey : ∀ z : ℝ³ × ℝ³, ‖bkiFinal ℓ F ψ z‖ ≤ B * M * (M * 1) := by
    intro z
    have h1 : ‖kinKernel F (z.1 - z.2)‖ ≤ B := by
      rw [hB]; exact Work.SmallBoxBridge.Resolve.kinKernel_bdd F hFi _
    have h2 : ‖ψ z.1‖ ≤ M := hM z.1
    have h3 : ‖ψ z.2‖ ≤ M := hM z.2
    have h4 : ‖convScale ℓ (z.1 - z.2)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact abs_convScale_le_one ℓ _
    calc ‖bkiFinal ℓ F ψ z‖
        = ‖kinKernel F (z.1 - z.2)‖ *
            (‖ψ z.1‖ * (‖ψ z.2‖ * ‖convScale ℓ (z.1 - z.2)‖)) := by
          simp only [bkiFinal, norm_mul]
      _ ≤ B * (M * (M * 1)) := by
          refine mul_le_mul h1 (mul_le_mul h2 (mul_le_mul h3 h4 (norm_nonneg _) hM0)
            (by positivity) hM0) (by positivity) hB0
      _ = B * M * (M * 1) := by ring
  have hmeas : AEStronglyMeasurable (bkiFinal ℓ F ψ)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => kinKernel F (z.1 - z.2))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      aestronglyMeasurable_kinKernel_sub hFi
    have h2 : AEStronglyMeasurable
        (fun z : ℝ³ × ℝ³ => ψ z.1 * (ψ z.2 * convScale ℓ (z.1 - z.2)))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      ((hψ.continuous.comp continuous_fst).mul
        ((hψ.continuous.comp continuous_snd).mul
          ((continuous_convScale ℓ).comp (continuous_fst.sub continuous_snd)))).aestronglyMeasurable
    have hmul : AEStronglyMeasurable ((fun z : ℝ³ × ℝ³ => kinKernel F (z.1 - z.2)) *
          fun z : ℝ³ × ℝ³ => ψ z.1 * (ψ z.2 * convScale ℓ (z.1 - z.2)))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := h1.mul h2
    unfold bkiFinal
    exact hmul
  refine integrable_of_compact_support ⟨Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R,
      (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R), ?_⟩ hmeas
    ⟨B * M * (M * 1), hkey⟩
  intro z hz
  have hz1 : ψ z.1 ≠ 0 := by
    intro h0; refine hz ?_
    simp only [bkiFinal, h0, mul_zero, zero_mul]
  have hz2 : ψ z.2 ≠ 0 := by
    intro h0; refine hz ?_
    simp only [bkiFinal, h0, zero_mul, mul_zero]
  simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
  exact ⟨hR z.1 (subset_tsupport ψ (Function.mem_support.mpr hz1)),
    hR z.2 (subset_tsupport ψ (Function.mem_support.mpr hz2))⟩

private lemma continuous_bsWin' {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) : Continuous (bsWin ℓ u) :=
  (chiScale_contDiff hℓ).continuous.comp (continuous_id.sub continuous_const)

private lemma hasCompactSupport_bsWin' {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (bsWin ℓ u) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (ℓ • u) (ℓ / 2)) ?_
  rw [Function.support_subset_iff]
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact bsWin_ne_zero_le_norm hℓ hx

/-- The unprojected family form at fixed `u` *is* the windowed mode form of the window
`bsWin ℓ u` (both are `(2π)⁻³∫_p F‖p‖·‖kinFT(χ_u·ψ) p‖²`, definitionally). -/
private lemma bsOneBodyUnproj_eq_winModeForm (ℓ : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    bsOneBodyUnproj ℓ F u ψ = winModeForm (bsWin ℓ u) F ψ := rfl

theorem familyFormUnproj_eq_kernelForm {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ)
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFm : ∀ r : ℝ, 0 ≤ F r) :
    Work.BSKinetic.bsFamilyFormUnproj ℓ F ψ
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.convScale ℓ (x - y) * Submission.BoseGases.kinKernel F (x - y) *
            ψ x * ψ y := by
  have hJoint : Integrable (fun w : ℝ³ × (ℝ³ × ℝ³) => bkiFam ℓ F ψ w.1 w.2.1 w.2.2)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
    integrable_bsFamUnprojJoint hℓ hFi ψ hψ hcs
  have hSlice : ∀ u : ℝ³, Integrable (fun z : ℝ³ × ℝ³ => bkiFam ℓ F ψ u z.1 z.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    fun u => by simpa only [bkiFam] using integrable_bsFamUnprojSlice hℓ hFi ψ hψ hcs u
  have hfin : Integrable (bkiFinal ℓ F ψ)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := integrable_bkiFinal hℓ hFi hψ hcs
  calc bsFamilyFormUnproj ℓ F ψ
      = ∫ u : ℝ³, ∫ x : ℝ³, (bsWin ℓ u x * ψ x) *
          (∫ y : ℝ³, kinKernel F (x - y) * (bsWin ℓ u y * ψ y)) := by
        rw [bsFamilyFormUnproj]
        apply integral_congr_ae
        filter_upwards with u
        rw [bsOneBodyUnproj_eq_winModeForm]
        exact Work.SmallBoxBridge.winModeForm_eq_kernelForm_general (bsWin ℓ u) ψ F hFi
          ((continuous_bsWin' (ne_of_gt hℓ) u).mul hψ.continuous |>.integrable_of_hasCompactSupport
            ((hasCompactSupport_bsWin' hℓ u).mul_right))
    _ = ∫ u : ℝ³, ∫ z : ℝ³ × ℝ³, bkiFam ℓ F ψ u z.1 z.2 := by
        apply integral_congr_ae
        filter_upwards with u
        have h1 : (∫ x : ℝ³, (bsWin ℓ u x * ψ x) *
              (∫ y : ℝ³, kinKernel F (x - y) * (bsWin ℓ u y * ψ y)))
            = ∫ x : ℝ³, ∫ y : ℝ³, bkiFam ℓ F ψ u x y := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [bkiFam]
          rw [MeasureTheory.integral_const_mul]
        have h2 : (∫ x : ℝ³, ∫ y : ℝ³, bkiFam ℓ F ψ u x y)
            = ∫ z : ℝ³ × ℝ³, bkiFam ℓ F ψ u z.1 z.2 :=
          (MeasureTheory.integral_prod (fun z : ℝ³ × ℝ³ => bkiFam ℓ F ψ u z.1 z.2)
            (hSlice u)).symm
        exact h1.trans h2
    _ = ∫ z : ℝ³ × ℝ³, ∫ u : ℝ³, bkiFam ℓ F ψ u z.1 z.2 :=
        MeasureTheory.integral_integral_swap (f := fun (u : ℝ³) (z : ℝ³ × ℝ³) =>
          bkiFam ℓ F ψ u z.1 z.2) hJoint
    _ = ∫ z : ℝ³ × ℝ³, bkiFinal ℓ F ψ z := by
        apply integral_congr_ae
        filter_upwards with z
        have hfun : (fun u : ℝ³ => bkiFam ℓ F ψ u z.1 z.2)
            = fun u : ℝ³ => (kinKernel F (z.1 - z.2) * ψ z.1 * ψ z.2) *
                (bsWin ℓ u z.1 * bsWin ℓ u z.2) := by
          funext u; simp only [bkiFam]; ring
        rw [hfun, MeasureTheory.integral_const_mul, integral_bsWin_mul_bsWin hℓ z.1 z.2]
        simp only [bkiFinal]
        ring
    _ = ∫ x : ℝ³, ∫ y : ℝ³, bkiFinal ℓ F ψ (x, y) :=
        MeasureTheory.integral_prod (fun z : ℝ³ × ℝ³ => bkiFinal ℓ F ψ z) hfin
    _ = ∫ x : ℝ³, ∫ y : ℝ³,
          kinKernel F (x - y) * (ψ x * (ψ y * convScale ℓ (x - y))) := by
        apply integral_congr_ae
        filter_upwards with x
        apply integral_congr_ae
        filter_upwards with y
        simp only [bkiFinal]
    _ = ∫ x : ℝ³, ∫ y : ℝ³,
          convScale ℓ (x - y) * kinKernel F (x - y) * ψ x * ψ y := by
        apply integral_congr_ae
        filter_upwards with x
        apply integral_congr_ae
        filter_upwards with y
        ring

end Work.BSKinetic
