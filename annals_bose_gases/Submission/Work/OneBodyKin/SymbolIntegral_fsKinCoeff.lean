import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.OneBodyKin.MeasurableBSOneBody
import Submission.Work.OneBodyKin.SymbolIntegralRhsTendsto
import Submission.Work.OneBodyKin.bsFamilyForm_eq_symbolIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SymbolIntegral_fsKinCoeff` — the symbol identity at the FS cut-off

The projected half of Bratteli--Solovej Lemma 3.3, `Work.OneBodyKin.SymbolIntegral ℓ F`, is an
identity of two explicit integrals:

    `bsFamilyForm ℓ F ψ = (2π)⁻³ ∫_q famSym ℓ F q · ‖kinFT ψ q‖² dq`.

It is proved for symbols `F` that are `L¹` in the radial variable
(`Work.OneBodyKin.bsFamilyForm_eq_symbolIntegral`), but the FS cut-off symbol
`fsKinCoeff c = [· − c]₊²` grows quadratically and is *not* `L¹`, so the identity at `F =
fsKinCoeff c` is not an instance of that theorem.

## The argument (monotone convergence on both sides)

The cut-off symbol is the increasing pointwise limit of the truncated symbols
`Ftrunc c n` (`TruncDefs.lean`), each of which *is* `L¹` in the radial variable, nonnegative and
bounded.  Hence, for every smooth compactly supported `ψ`,

    `bsFamilyForm ℓ (Ftrunc c n) ψ = (2π)⁻³ ∫_q famSym ℓ (Ftrunc c n) q ‖kinFT ψ q‖² dq`

by the `L¹` theorem (`hbase`), and it remains to let `n → ∞` on both sides:

* **the left side** (`bsFamilyForm_Ftrunc_tendsto`): for each box shift `u` the inner
  `p`-integral converges by monotone convergence (`Ftrunc c n ↑ fsKinCoeff c` pointwise), and the
  `u`-integral converges by monotone convergence as well — the limiting `u`-integrand is
  integrable because it is *continuous* `(continuous_bsOneBody)` with *compact support*
  `(bsOneBody_eq_zero_of_far)`, and each approximant is dominated by it;
* **the right side** (`SymbolIntegralRhsTendsto`): pointwise convergence of `famSym ℓ (Ftrunc c n) q`
  combined with dominated convergence in `q` against the Schwartz decay of `kinFT ψ`.

The two limits are equal because `ℝ` is Hausdorff (`tendsto_nhds_unique`).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

private lemma sic_contDiff_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsWin ℓ u) := by
  change ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => chiScale ℓ (z - ℓ • u))
  exact (chiScale_contDiff (ne_of_gt hℓ)).comp (contDiff_id.sub contDiff_const)

private lemma sic_contDiff_bsQ {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsQ ℓ u ψ) := by
  change ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => ψ z - Work.BSKinetic.bsMean ℓ u ψ)
  exact hψ.sub contDiff_const

private lemma sic_hasCompactSupport_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (Work.BSKinetic.bsWin ℓ u) := by
  have h : HasCompactSupport (fun z : ℝ³ => chiScale ℓ (z - ℓ • u)) :=
    (chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph (Homeomorph.subRight (ℓ • u))
  exact h

/-- The complexified windowed mean-free state. -/
private noncomputable def sic_winQc (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℂ :=
  fun z => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)

private lemma sic_continuous_winQc {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) : Continuous (sic_winQc ℓ u ψ) :=
  (Complex.continuous_ofReal.comp (sic_contDiff_bsWin hℓ u).continuous).mul
    (Complex.continuous_ofReal.comp (sic_contDiff_bsQ u hψ).continuous)

private lemma sic_hasCompactSupport_winQc {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    HasCompactSupport (sic_winQc ℓ u ψ) := by
  have h1 : HasCompactSupport (fun z : ℝ³ => (chiScale ℓ : ℝ³ → ℝ) (z - ℓ • u)) :=
    (chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph (Homeomorph.subRight (ℓ • u))
  have h2 : HasCompactSupport (fun z : ℝ³ => ((chiScale ℓ (z - ℓ • u) : ℝ) : ℂ)) :=
    h1.comp_left (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)
  have h3 : sic_winQc ℓ u ψ = fun z : ℝ³ =>
      ((chiScale ℓ (z - ℓ • u) : ℝ) : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ) := rfl
  rw [h3]
  exact h2.mul_right

/-- The `p`-integrand of `bsOneBody` at the full cut-off is integrable. -/
private lemma sic_integrable_winQc_fsKinCoeff {ℓ c : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) :
    MeasureTheory.Integrable (fun p : ℝ³ =>
      fsKinCoeff c ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2) := by
  have hcd : ContDiff ℝ (⊤ : ENat)
      (fun z : ℝ³ => Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) :=
    (sic_contDiff_bsWin hℓ u).mul (sic_contDiff_bsQ u hψ)
  have hcc : HasCompactSupport
      (fun z : ℝ³ => Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) :=
    (sic_hasCompactSupport_bsWin hℓ u).mul_right
  have h := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) hcd hcc
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  have hfun : (fun z : ℝ³ =>
        (((fun z : ℝ³ => Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) z : ℝ) : ℂ))
      = sic_winQc ℓ u ψ := by
    funext z
    simp only [sic_winQc]
    push_cast
    ring
  simp only [Work.BSKinetic.Decomp.bsPsi]
  rw [hfun]

/-- The `p`-integrand at the truncated symbol (dominated by the untruncated one). -/
private lemma sic_integrable_winQc_Ftrunc {ℓ c : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) (n : ℕ) :
    MeasureTheory.Integrable (fun p : ℝ³ =>
      Ftrunc c n ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2) := by
  have hF := sic_integrable_winQc_fsKinCoeff (ℓ := ℓ) (c := c) hℓ hψ u
  have hcont : Continuous (fun p : ℝ³ => ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2) :=
    ((Work.OneBodyKin.continuous_kinFT
      ((sic_continuous_winQc hℓ hψ u).integrable_of_hasCompactSupport
        (sic_hasCompactSupport_winQc hℓ u ψ))).norm).pow 2
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ =>
      Ftrunc c n ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2) :=
    (((measurable_Ftrunc c n).comp continuous_norm.measurable).mul
      hcont.measurable).aestronglyMeasurable
  refine hF.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
  have hle := Ftrunc_le_fsKinCoeff c n ‖p‖
  have hnn : (0:ℝ) ≤ ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2 := sq_nonneg _
  have hf0 : 0 ≤ Ftrunc c n ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2 :=
    mul_nonneg (Ftrunc_nonneg c n ‖p‖) hnn
  rw [Real.norm_of_nonneg hf0]
  exact mul_le_mul_of_nonneg_right hle hnn

/-- **Pointwise (in `u`) monotone convergence of the inner `p`-integral.** -/
private lemma sic_bsOneBody_Ftrunc_tendsto {ℓ c : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : ℝ³) :
    Filter.Tendsto (fun n : ℕ => Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ)
      Filter.atTop (nhds (Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u ψ)) := by
  have hFint := sic_integrable_winQc_fsKinCoeff (ℓ := ℓ) (c := c) hℓ hψ u
  have hmain : Filter.Tendsto
      (fun n : ℕ => ∫ p : ℝ³, Ftrunc c n ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2)
      Filter.atTop
      (nhds (∫ p : ℝ³, fsKinCoeff c ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2)) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (f := fun n p => Ftrunc c n ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2)
      (F := fun p => fsKinCoeff c ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2)
      (fun n => sic_integrable_winQc_Ftrunc hℓ hψ u n) hFint ?_ ?_
    · filter_upwards with p
      intro n m hnm
      exact mul_le_mul_of_nonneg_right (Ftrunc_mono_le c hnm ‖p‖) (sq_nonneg _)
    · filter_upwards with p
      exact (Ftrunc_tendsto c ‖p‖).mul_const (‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2)
  have hthis := hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  unfold Work.BSKinetic.bsOneBody
  exact hthis

/-- The `u`-integrand at the full cut-off is integrable. -/
private lemma sic_integrable_bsOneBody_fsKinCoeff {ℓ c : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable
      (fun u : ℝ³ => Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u ψ) := by
  have hcont : Continuous (fun u : ℝ³ => Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u ψ) :=
    Work.BSKinetic.Decomp.continuous_bsOneBody hℓ c ψ hψ hcs
  obtain ⟨R, hR0, hR⟩ := Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far hℓ c ψ hψ hcs
  refine hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro' (K := closedBall (0 : ℝ³) R)
      (isCompact_closedBall (0 : ℝ³) R) isClosed_closedBall ?_)
  intro u hu
  rw [mem_closedBall, dist_zero_right, not_le] at hu
  exact hR u hu.le

/-- The `u`-integrand at a truncated symbol is integrable. -/
private lemma sic_integrable_bsOneBody_Ftrunc {ℓ c : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (n : ℕ) :
    MeasureTheory.Integrable
      (fun u : ℝ³ => Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ) := by
  have hFint := sic_integrable_bsOneBody_fsKinCoeff (ℓ := ℓ) (c := c) hℓ hψ hcs
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ³ => Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ) :=
    Work.OneBodyKin.MeasurableBSOneBody hℓ (measurable_Ftrunc c n) hψ.continuous hcs
  refine hFint.mono' hmeas (Filter.Eventually.of_forall fun u => ?_)
  have hFn : MeasureTheory.Integrable (fun p : ℝ³ =>
      Ftrunc c n ‖p‖ * ‖kinFT (sic_winQc ℓ u ψ) p‖ ^ 2) :=
    sic_integrable_winQc_Ftrunc hℓ hψ u n
  have hle : Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ
      ≤ Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u ψ := by
    rw [Work.BSKinetic.bsOneBody]
    refine mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono hFn
      (sic_integrable_winQc_fsKinCoeff hℓ hψ u) (fun p =>
        mul_le_mul_of_nonneg_right (Ftrunc_le_fsKinCoeff c n ‖p‖) (sq_nonneg _))) ?_
    positivity
  have hnn : 0 ≤ Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ := by
    rw [Work.BSKinetic.bsOneBody]
    exact mul_nonneg (by positivity) (integral_nonneg fun p =>
      mul_nonneg (Ftrunc_nonneg c n ‖p‖) (sq_nonneg _))
  rw [Real.norm_of_nonneg hnn]
  exact hle

/-- **The left-hand side converges along the truncations.** -/
theorem bsFamilyForm_Ftrunc_tendsto {ℓ c : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => Work.BSKinetic.bsFamilyForm ℓ (Ftrunc c n) ψ)
      Filter.atTop (nhds (Work.BSKinetic.bsFamilyForm ℓ (fsKinCoeff c) ψ)) := by
  have hFint := sic_integrable_bsOneBody_fsKinCoeff (ℓ := ℓ) (c := c) hℓ hψ hcs
  have hmain : Filter.Tendsto
      (fun n : ℕ => ∫ u : ℝ³, Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ)
      Filter.atTop (nhds (∫ u : ℝ³, Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u ψ)) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (f := fun n u => Work.BSKinetic.bsOneBody ℓ (Ftrunc c n) u ψ)
      (F := fun u => Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u ψ)
      (fun n => sic_integrable_bsOneBody_Ftrunc hℓ hψ hcs n) hFint ?_ ?_
    · filter_upwards with u
      intro n m hnm
      unfold Work.BSKinetic.bsOneBody
      refine mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono
        (sic_integrable_winQc_Ftrunc hℓ hψ u n) (sic_integrable_winQc_Ftrunc hℓ hψ u m)
        (fun p => mul_le_mul_of_nonneg_right (Ftrunc_mono_le c hnm ‖p‖) (sq_nonneg _))) ?_
      positivity
    · filter_upwards with u
      exact sic_bsOneBody_Ftrunc_tendsto hℓ hψ u
  have hthis := hmain
  unfold Work.BSKinetic.bsFamilyForm
  exact hthis


/-- **The symbol-integral identity at the FS cut-off** (the projected half of BS Lemma 3.3 for
`F = [· − c]₊²`): the projected moving-box family form is the Fourier integral of its symbol
`famSym ℓ (fsKinCoeff c)`. -/
theorem SymbolIntegral_fsKinCoeff {ℓ c : ℝ} (hℓ : 0 < ℓ) :
    Work.OneBodyKin.SymbolIntegral ℓ (Submission.BoseGases.fsKinCoeff c) := by
  intro ψ hψ hcs
  have hL' : Filter.Tendsto
      (fun n : ℕ => ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        famSym ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop (nhds (Work.BSKinetic.bsFamilyForm ℓ (fsKinCoeff c) ψ)) := by
    refine Filter.Tendsto.congr' ?_ (bsFamilyForm_Ftrunc_tendsto hℓ hψ hcs)
    filter_upwards with n
    exact bsFamilyForm_eq_symbolIntegral hℓ (integrable_Ftrunc c n)
      (fun r => Ftrunc_nonneg c n r) ψ hψ hcs
  exact tendsto_nhds_unique hL' (SymbolIntegralRhsTendsto hℓ ψ hψ hcs)

end Work.OneBodyKin
