import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.ae_mem_abox_prod
import Submission.Work.UBBInputs9.B.exists_bound_fderiv_windowed_state
import Submission.Work.UBBInputs9.B.fderiv_chiScale_eq_zero_of_norm_gt
import Submission.Work.UBBInputs9.B.kinWordW_le_sup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.integrable_fderiv_chiBPhi_sq`

**The sliding-window Dirichlet integrand is `L¹`.**  For `ℓ, d > 0` and a smooth state `Φ` of
compact support on `X 1`, the squared directional derivative of the sliding product
`y ↦ χ_{B(u)}(y 0)·Φ y` in the kinetic direction `kcDir 1 0 k`,

    `p = (x, u) ↦ (∂_k (χ_{B(u)}·Φ)(x))²`,

is `Integrable` for the product of `volume ↾ abox 1 ℓ` with the Lebesgue measure on `ℝ³`.
This is the a.e.-integrability input which turns the outer `∫_u` of the sliding Dirichlet word
(`B/integral_dirichlet_chiB_eq`, `B/unproj_defect`) into a genuine Bochner integral.

## Proof

The Leibniz formula `fderiv_chiBPhi_eq` (Basic) splits the derivative into

    `∂_k(χ_{B(u)}·Φ)(x) = A(x)·χ_{B(u)}(x) + χ_ℓ(x)·Φ(x)·∂_kχ_{ℓd}(x 0 − (ℓd)u)`,

with `A(x) = ∂_k(χ_ℓ·Φ)(x)`.  Each factor is bounded **uniformly**:

* `|A(x)| ≤ MA` — the derivative of the windowed smooth compactly supported state is bounded
  (`exists_bound_fderiv_windowed_state`);
* `|χ_ℓ(x)| ≤ chiSup` (`abs_chiScale_le_chiSup`) and `|Φ(x)| ≤ MΦ` (`HasCompactSupport.exists_bound_of_continuous`);
* `|∂_kχ_{ℓd}(z)| ≤ MD` — the derivative of the bump is bounded.

Both `u`-dependent factors vanish when `z = x 0 − (ℓd)u` lies outside `ball 0 (ℓd/2)`
(`chiScale_eq_zero_of_norm_gt` here, `fderiv_chiScale_eq_zero_of_norm_gt` from the sibling
module).  Since `‖x 0‖ ≤ C` on `abox 1 ℓ` (compactness of `acube ℓ`), this forces
`u ∈ closedBall 0 R` for `R = (C + ℓd/2)/(ℓd)` (`s‖u‖ ≤ ‖x 0‖ + ‖z‖` by the triangle
inequality).  Hence the integrand is dominated a.e. — the `a.e.` being supplied by
`ae_mem_abox_prod` — by the `u`-only function `g(x,u) = MH·1_{closedBall 0 R}(u)` with
`MH = (MA·chiSup + chiSup·MΦ·MD)²`, which is `Integrable` by `Integrable.mul_prod` (the
constant in `x` is integrable because `abox 1 ℓ` has finite measure).  `Integrable.mono'`
concludes, and `Integrable.congr` transfers the statement back to the original integrand.

## Contents

* `chiScale_eq_zero_of_norm_gt` — the bump vanishes strictly outside its ball;
* `integrable_fderiv_chiBPhi_sq` — the target.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The vanishing of `chiScale` outside its ball -/

lemma chiScale_eq_zero_of_norm_gt {s : ℝ} (hs : 0 < s) {y : ℝ³} (h : s / 2 < ‖y‖) :
    chiScale s y = 0 := by
  rw [chiScale]
  apply chi_eq_zero_of_norm_gt
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hs))]
  rw [show (1 : ℝ) / 2 = s⁻¹ * (s / 2) by field_simp]
  exact mul_lt_mul_of_pos_left h (inv_pos.mpr hs)

/-! ## The main theorem -/

theorem integrable_fderiv_chiBPhi_sq (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ) (k : Fin 3) :
    MeasureTheory.Integrable (fun p : Submission.BoseGases.X 1 × EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
          Submission.BoseGases.chiB ℓ d p.2 (y 0) * Φ y) p.1
            (Submission.BoseGases.kcDir 1 0 k)) ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X 1)).restrict
          (Submission.BoseGases.abox 1 ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  classical
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hldne : ℓ * d ≠ 0 := ne_of_gt hld
  -- ### bounds
  obtain ⟨MA, hMA0, hMA⟩ := exists_bound_fderiv_windowed_state ℓ hℓ hΦ hcs k
  obtain ⟨MΦ, hMΦ⟩ := hcs.exists_bound_of_continuous hΦ.continuous
  have hΦb : ∀ x : X1, |Φ x| ≤ MΦ := fun x => by
    rw [← Real.norm_eq_abs]; exact hMΦ x
  have hDcont : Continuous (fun z : ℝ³ => fderiv ℝ (chiScale (ℓ * d)) z (kcStdBasis k)) :=
    (chiScale_contDiff hldne).continuous_fderiv (by simp) |>.clm_apply continuous_const
  obtain ⟨MD, hMD⟩ :=
    (chiScale_hasCompactSupport hldne).fderiv_apply ℝ (kcStdBasis k) |>.exists_bound_of_continuous hDcont
  have hMDb : ∀ z : ℝ³, |fderiv ℝ (chiScale (ℓ * d)) z (kcStdBasis k)| ≤ MD := fun z => by
    rw [← Real.norm_eq_abs]; exact hMD z
  obtain ⟨C₀, hC₀⟩ := (acube_isCompact ℓ).exists_bound_of_continuousOn continuous_norm.continuousOn
  have hC : ∀ y : ℝ³, y ∈ acube ℓ → ‖y‖ ≤ C₀ := fun y hy => by
    have h := hC₀ y hy
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] at h
  set R : ℝ := (C₀ + ℓ * d / 2) / (ℓ * d) with hRdef
  set MH : ℝ := (MA * chiSup + (chiSup * MΦ) * MD) ^ 2 with hMHdef
  -- ### the pointwise bound
  have hpoint : ∀ x : X1, x ∈ abox 1 ℓ → ∀ u : ℝ³,
      ‖((fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
          * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
        + (chiScale ℓ (x 0) * Φ x)
          * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))) ^ 2‖
      ≤ MH * (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) u := by
    intro x hx u
    have hx0 : x 0 ∈ acube ℓ := (mem_abox_iff 1 ℓ x).mp hx 0
    have hx0n : ‖x 0‖ ≤ C₀ := hC (x 0) hx0
    by_cases hu : u ∈ closedBall (0 : ℝ³) R
    · rw [Set.indicator_of_mem hu, mul_one]
      have h1 : |fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k)| ≤ MA := hMA x
      have h2 : |chiScale (ℓ * d) (x 0 - (ℓ * d) • u)| ≤ chiSup := abs_chiScale_le_chiSup _ _
      have h3 : |chiScale ℓ (x 0) * Φ x| ≤ chiSup * MΦ := by
        rw [abs_mul]
        exact mul_le_mul (abs_chiScale_le_chiSup _ _) (hΦb x) (abs_nonneg _) chiSup_pos.le
      have h4 : |fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)| ≤ MD := hMDb _
      have h5 : |(fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
            * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
          + (chiScale ℓ (x 0) * Φ x)
            * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))|
          ≤ MA * chiSup + (chiSup * MΦ) * MD := by
        have hAB : |(fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
            * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)| ≤ MA * chiSup := by
          rw [abs_mul]
          exact mul_le_mul h1 h2 (abs_nonneg _) hMA0
        have hMΦ0 : 0 ≤ MΦ := le_trans (norm_nonneg (Φ x)) (hMΦ x)
        have hCD : |(chiScale ℓ (x 0) * Φ x)
            * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))|
            ≤ (chiSup * MΦ) * MD := by
          rw [abs_mul]
          exact mul_le_mul h3 h4 (abs_nonneg _) (mul_nonneg chiSup_pos.le hMΦ0)
        calc |(fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
              * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
            + (chiScale ℓ (x 0) * Φ x)
              * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))|
            ≤ |(fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
                * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)|
              + |(chiScale ℓ (x 0) * Φ x)
                * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))| := by
              simpa only [Real.norm_eq_abs] using
                norm_add_le ((fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
                  * chiScale (ℓ * d) (x 0 - (ℓ * d) • u))
                  ((chiScale ℓ (x 0) * Φ x)
                  * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k)))
          _ ≤ MA * chiSup + (chiSup * MΦ) * MD := add_le_add hAB hCD
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hMHdef, sq_le_sq]
      exact le_trans h5 (le_abs_self _)
    · have huR : R < ‖u‖ := by
        have h1 : ¬ (‖u‖ ≤ R) := by
          have h2 := hu
          rw [mem_closedBall, dist_eq_norm, sub_zero] at h2
          exact h2
        exact lt_of_not_ge h1
      have hzu : (ℓ * d) / 2 < ‖x 0 - (ℓ * d) • u‖ := by
        have hnorm : ‖(ℓ * d) • u‖ = (ℓ * d) * ‖u‖ := by
          rw [norm_smul, Real.norm_of_nonneg hld.le]
        have hkey : (ℓ * d) * R = C₀ + (ℓ * d) / 2 := by
          rw [hRdef]; field_simp
        have hlt : C₀ + (ℓ * d) / 2 < (ℓ * d) * ‖u‖ := by
          rw [← hkey]; exact mul_lt_mul_of_pos_left huR hld
        have hle : ‖(ℓ * d) • u‖ - ‖x 0‖ ≤ ‖x 0 - (ℓ * d) • u‖ := by
          have h := norm_sub_norm_le ((ℓ * d) • u) (x 0)
          rwa [norm_sub_rev] at h
        rw [hnorm] at hle
        linarith
      have hB0 : chiScale (ℓ * d) (x 0 - (ℓ * d) • u) = 0 :=
        chiScale_eq_zero_of_norm_gt hld hzu
      have hD0 : fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k) = 0 :=
        fderiv_chiScale_eq_zero_of_norm_gt hld hzu
      have hzero : ((fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k))
            * chiScale (ℓ * d) (x 0 - (ℓ * d) • u)
          + (chiScale ℓ (x 0) * Φ x)
            * (fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))) ^ 2 = 0 := by
        rw [hB0, hD0]; ring
      rw [hzero, norm_zero, Set.indicator_of_notMem hu, mul_zero]
  -- ### the dominating function is integrable
  set g : X1 × ℝ³ → ℝ :=
    fun p => MH * (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.2 with hg
  have hfin : IsFiniteMeasure ((volume : Measure X1).restrict (abox 1 ℓ)) := ⟨by
    rw [Measure.restrict_apply_univ, abox_volume 1 ℓ hℓ.le]
    exact ENNReal.ofReal_lt_top⟩
  have hgint : Integrable g (((volume : Measure X1).restrict (abox 1 ℓ)).prod
      (volume : Measure ℝ³)) := by
    rw [hg]
    have hf : Integrable (fun _ : X1 => MH) ((volume : Measure X1).restrict (abox 1 ℓ)) :=
      (integrable_const_iff (μ := (volume : Measure X1).restrict (abox 1 ℓ))
        (c := MH)).mpr (Or.inr inferInstance)
    have h1 : Integrable
        (fun u : ℝ³ => (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) u)
        (volume : Measure ℝ³) := by
      rw [integrable_indicator_iff (isClosed_closedBall.measurableSet)]
      exact integrableOn_const
        (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R)).ne
    exact hf.mul_prod h1
  -- ### `H`, the rewritten integrand, is continuous
  have hAcont : Continuous (fun x : X1 =>
      fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k)) := by
    have hcd : ContDiff ℝ (⊤ : ENat) (fun y : X1 => chiScale ℓ (y 0) * Φ y) :=
      ((chiScale_contDiff (ne_of_gt hℓ)).comp
        (ContinuousLinearMap.contDiff projX1)).mul hΦ
    exact (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
  set H : X1 × ℝ³ → ℝ := fun p =>
    ((fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) p.1 (kcDir 1 0 k))
        * chiScale (ℓ * d) (p.1 0 - (ℓ * d) • p.2)
      + (chiScale ℓ (p.1 0) * Φ p.1)
        * (fderiv ℝ (chiScale (ℓ * d)) (p.1 0 - (ℓ * d) • p.2) (kcStdBasis k))) ^ 2 with hH
  have hHcont : Continuous H := by
    rw [hH]
    have hBc : Continuous
        (fun p : X1 × ℝ³ => chiScale (ℓ * d) (p.1 0 - (ℓ * d) • p.2)) :=
      (chiScale_contDiff hldne).continuous.comp
        (((continuous_apply 0).comp continuous_fst).sub (continuous_snd.const_smul (ℓ * d)))
    have hCc : Continuous (fun p : X1 × ℝ³ => chiScale ℓ (p.1 0) * Φ p.1) :=
      ((chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
        ((continuous_apply 0).comp continuous_fst)).mul (hΦ.continuous.comp continuous_fst)
    have hDc : Continuous
        (fun p : X1 × ℝ³ => fderiv ℝ (chiScale (ℓ * d)) (p.1 0 - (ℓ * d) • p.2) (kcStdBasis k)) :=
      hDcont.comp
        (((continuous_apply 0).comp continuous_fst).sub (continuous_snd.const_smul (ℓ * d)))
    have hAc : Continuous
        (fun p : X1 × ℝ³ => fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) p.1
          (kcDir 1 0 k)) :=
      hAcont.comp continuous_fst
    exact ((hAc.mul hBc).add (hCc.mul hDc)).pow 2
  -- ### assemble
  have hae : ∀ᵐ p ∂(((volume : Measure X1).restrict (abox 1 ℓ)).prod (volume : Measure ℝ³)),
      ‖H p‖ ≤ g p := by
    rw [hg, hH]
    filter_upwards [ae_mem_abox_prod ℓ] with p hp
    exact hpoint p.1 hp p.2
  have hIntH : Integrable H (((volume : Measure X1).restrict (abox 1 ℓ)).prod
      (volume : Measure ℝ³)) :=
    hgint.mono' hHcont.aestronglyMeasurable hae
  refine hIntH.congr ?_
  rw [hH]
  filter_upwards with p
  rw [fderiv_chiBPhi_eq ℓ d hΦ p.2 p.1 k]

end Work.UBBInputs9.B
