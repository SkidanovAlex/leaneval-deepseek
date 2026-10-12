import ChallengeDeps
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFix.Defs
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable
import Submission.Work.BoseKinLoc.Word.kinFormB_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.isLowB_chemBoundAlt`

The lemma `isLowB_chemBoundAlt` is the `IsLowB` (FS `eq:aprioriPsi`) consequence needed by the
`perBoxIntegratedPos` route: a low box state's **one-body (flat) mass**

`M := ∫_{abox n ℓ} Φ²·(Σᵢ ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y)`

is bounded from below by the FS threshold value:

`4πμ²(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖² ≤ μ·M`,   `ℓ = sideAt μ (a v)`.

In the corpus vocabulary `IsLowB` is `wordB ≤ ℓ³·Theta (a v) J μ·normB`, where
`Theta A J ρ = −4πρ²A(1 − J√(ρA³))`, and `wordB = boxFormB = kinFormB + chemPartB + pairPartB`
(`Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable`, whose hypotheses are exactly the two
integrability requirements `hA`, `hB` of the statement), while `chemPartB = −μ·M`.  Hence

`chemPartB ≤ wordB ≤ ℓ³·Theta (a v) J μ·normB`

as soon as `0 ≤ kinFormB` and `0 ≤ pairPartB`; multiplying by `−1` gives the displayed
inequality.  No sign hypothesis on `μ`, on `a v`, or on `1 − J√(μ(a v)³)` is used: the inequality
direction is automatic.

## The two nonnegativity inputs

* `pairPartB_nonneg`: the integrand is pointwise nonnegative, because
  `wLoc ℓ v 0 x y = χ_0(x)·wScaled ℓ v (x−y)·χ_0(y)` (`Submission/LocPotential.lean`) with `χ ≥ 0`
  (`chi_nonneg`) and `wScaled ℓ v z = v z / convScale ℓ z ≥ 0` for `0 ≤ v` (`div_nonneg` against
  `convScale_nonneg`).  No positivity of `ℓ` is needed: `integral_nonneg` asks only for pointwise
  nonnegativity.
* `0 ≤ kinFormB n ℓ d s εT b Φ`: this is `Work.BoseKinLoc.Word.kinFormB_nonneg` when the
  parameters satisfy `0 ≤ εT ≤ 1`, and `kinFormB_nonneg_of_one_le` (below) when `1 ≤ d`.

The second case is needed because the parameter block `paramsAt μ (a v) = fsParams (μ(a v)³)` of
`Work.BoseBox.Word` has `d = (μa³)^{6/323}`, `s = (μa³)^{1/323}`, `εT = (μa³)^{23/1292}`, `b = 1/16`
and `ℓ = (μa³)^{-3/2}(μa)^{-1/2}`.  Writing `t := μ·(a v)³`:

* `t ≤ 0` forces `ℓ = 0`, hence `kinFormB = ℓ^{-3}·(…) = 0` (`sideAt_eq_zero_of_nonpos`);
* `0 < t ≤ 1` gives `0 < d, s` and `0 ≤ εT ≤ 1` — the standard lemma applies;
* `1 ≤ t` gives `0 < d, s`, `0 ≤ εT` and `1 ≤ d` — the variant below applies.

(`t ≤ 0` and `t > 0` are the only cases: `t = 0` is the degenerate box side `ℓ = 0`.)

## Why `kinFormB_nonneg_of_one_le` is true — and why the standard lemma does not suffice

`fsT = neuWord + gapWord + momWord + mainWord`; the first three words are nonnegative as soon as
`0 ≤ εT`, `0 ≤ b`, `d ℓ ≥ 0` (the factor `εT` appears only *multiplicatively*), so `εT ≤ 1` enters
only through `mainWord = (1 − εT)A₁ + εT A₂`, with `A_j` the two `bsOneBody`s at the cutoffs
`(2sℓ)⁻¹` and `(2dsℓ)⁻¹`.  Since `fsKinCoeff c r = [r − c]₊²` is *antitone* in `c`, the hypothesis
`1 ≤ d` (together with `s ℓ > 0`) gives `A₁ ≤ A₂`, and then
`mainWord = A₁ + εT(A₂ − A₁) ≥ A₁ ≥ 0` for every `εT ≥ 0`.  This is exactly the regime met above:
`d ≥ 1` holds precisely when `t ≥ 1`, while `εT ≤ 1` holds precisely when `t ≤ 1`.

## Organization

Everything is proved in this single file so that the submission depends only on the corpus:
`pairPartB_nonneg`, `sideAt_eq_zero_of_nonpos`, `continuous_kinFT_cspt`, `fsKinCoeff_anti`,
`integrable_bsKinFTWeight`, `bsOneBody_mono_of_coeff_le`, `mainWord_nonneg_of_one_le`,
`fsT_nonneg_of_one_le`, `kinFormB_nonneg_of_one_le`, and finally `isLowB_chemBoundAlt`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff FourierTransform

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. `pairPartB ≥ 0` for a nonnegative potential -/

/-- **The box-restricted pair-interaction part is nonnegative for `0 ≤ v`.**  The integrand
`Φ x ^ 2 * Σ_{i<j} wLoc ℓ v 0 (xᵢ) (xⱼ)` is pointwise nonnegative: `Φ x ^ 2 ≥ 0`, and each
`wLoc ℓ v 0 x y = χ₀(x)·wScaled ℓ v (x−y)·χ₀(y)` with `χ ≥ 0` and
`wScaled ℓ v z = v z / convScale ℓ z ≥ 0`. -/
theorem pairPartB_nonneg {n : ℕ} {v : E3 → ℝ} (hv : 0 ≤ v) (ℓ : ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseKinLoc.pairPartB n v ℓ Φ := by
  unfold Work.BoseKinLoc.pairPartB
  refine MeasureTheory.integral_nonneg fun x => ?_
  refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun ij _ => ?_)
  unfold Submission.BoseGases.wLoc
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · rw [Submission.BoseGases.chiU]
    exact Submission.BoseGases.chi_nonneg _
  · unfold Submission.BoseGases.wScaled
    exact div_nonneg (hv _) (Submission.BoseGases.convScale_nonneg ℓ _)
  · rw [Submission.BoseGases.chiU]
    exact Submission.BoseGases.chi_nonneg _

/-! ## 2. The box side vanishes at nonpositive diluteness -/

/-- `sideAt μ a = (μa³)^{-3/646}·(μa)^{-1/2}`.  If `μa³ ≤ 0` then either `μa³ = 0`, where the
first factor is `0`, or `μa < 0`, where `(μa)^{-1/2} = exp(log(μa)·(-1/2))·cos(-π/2) = 0`
(`Real.rpow_def_of_neg`). -/
theorem sideAt_eq_zero_of_nonpos {μ a : ℝ} (h : μ * a ^ 3 ≤ 0) :
    Work.BoseBox.sideAt μ a = 0 := by
  have h3 : μ * a ^ 3 = (μ * a) * a ^ 2 := by ring
  have hma : μ * a ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have ha0 : a ≠ 0 := by rintro rfl; simp at hcon
    have hpos : 0 < μ * a ^ 3 := by
      rw [h3]; exact mul_pos hcon (by simpa [sq_abs] using pow_pos (abs_pos.mpr ha0) 2)
    linarith
  rcases lt_or_eq_of_le hma with hlt | heq
  · have hr : (μ * a) ^ (-(1 / 2 : ℝ)) = 0 := by
      rw [Real.rpow_def_of_neg hlt]
      rw [show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
        Real.cos_pi_div_two, mul_zero]
    rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide, hr, mul_zero]
  · have ht : μ * a ^ 3 = 0 := by rw [h3, heq, zero_mul]
    have hKl : (Work.BoseBox.paramsAt μ a).Kl = 0 := by
      show Work.BoseBox.fsXp (μ * a ^ 3) (-(3 / 2)) = 0
      rw [ht, Work.BoseBox.fsXp]
      exact Real.zero_rpow (by norm_num)
    rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide, hKl, zero_mul]

/-! ## 3. `kinFT` of a compactly supported smooth function is continuous -/

theorem continuous_kinFT_cspt {G : E3 → ℝ} (hGd : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) :
    Continuous (fun p : E3 => Submission.BoseGases.kinFT (fun z : E3 => (G z : ℂ)) p) := by
  have hGcC : HasCompactSupport (fun z : E3 => (G z : ℂ)) :=
    hGc.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hGdC : ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => (G z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hGd
  let F : SchwartzMap E3 ℂ := hGcC.toSchwartzMap hGdC
  have hcoe : (F : E3 → ℂ) = fun z => (G z : ℂ) := rfl
  have hfun : (fun p : E3 => Submission.BoseGases.kinFT (fun z : E3 => (G z : ℂ)) p)
      = fun p : E3 => (𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p) := by
    funext p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hcoe, ← SchwartzMap.fourier_coe F]
  rw [hfun]
  exact (SchwartzMap.continuous (𝓕 F)).comp (continuous_const_smul _)

/-! ## 4. `fsKinCoeff` is antitone in the cutoff -/

theorem fsKinCoeff_anti {c₁ c₂ r : ℝ} (h : c₁ ≤ c₂) :
    Submission.BoseGases.fsKinCoeff c₂ r ≤ Submission.BoseGases.fsKinCoeff c₁ r := by
  unfold Submission.BoseGases.fsKinCoeff
  refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ (le_max_right _ _)) 2
  exact le_trans (sub_le_sub_left h r) (le_max_left _ _)

/-! ## 5. Integrability of the weighted `p`-integrand -/

theorem integrable_bsKinFTWeight {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3) {ψ : E3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Submission.BoseGases.kinFT
        (fun z : E3 => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) p‖ ^ 2) := by
  have hGd : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : E3 => Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) :=
    Work.BSKinetic.contDiff_bsWin_mul_bsQ u hψ
  have hGc : HasCompactSupport
      (fun z : E3 => Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) :=
    (Work.BSKinetic.hasCompactSupport_bsWin hℓ.ne' u).mul_right
  have hfuneq : (fun z : E3 => ((Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z : ℝ) : ℂ))
      = fun z : E3 => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ) := by
    funext z; push_cast; ring
  have hint : Integrable (fun p : E3 => ‖p‖ ^ 2 *
      ‖Submission.BoseGases.kinFT
        (fun z : E3 => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) p‖ ^ 2) := by
    have h := Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
      (fun z : E3 => Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z) hGd hGc
    rwa [hfuneq] at h
  have hmeas : AEStronglyMeasurable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Submission.BoseGases.kinFT
        (fun z : E3 => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (Work.BSKinetic.bsQ ℓ u ψ z : ℂ)) p‖ ^ 2)
      volume := by
    have hcont : Continuous (fun p : E3 => Submission.BoseGases.kinFT
        (fun z : E3 => ((Work.BSKinetic.bsWin ℓ u z * Work.BSKinetic.bsQ ℓ u ψ z : ℝ) : ℂ)) p) :=
      continuous_kinFT_cspt hGd hGc
    rw [hfuneq] at hcont
    have hf : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact ((continuous_norm.sub continuous_const).max continuous_const).pow 2
    exact (hf.mul (hcont.norm.pow 2)).aestronglyMeasurable
  refine hint.mono' hmeas ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _))]
  have h2 : Submission.BoseGases.fsKinCoeff c ‖p‖ ≤ ‖p‖ ^ 2 := by
    have h3 := Work.BSKinetic.fsKinCoeff_zero_le hc ‖p‖
    rwa [Work.BSKinetic.fsKinCoeff_zero_of_nonneg (norm_nonneg p)] at h3
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-! ## 6. Monotonicity of `bsOneBody` in the cutoff -/

theorem bsOneBody_mono_of_coeff_le {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3) {ψ : E3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h12 : c₁ ≤ c₂) :
    Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c₂) u ψ
      ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c₁) u ψ :=
  Work.BSKinetic.bsOneBody_mono_coeff (F := Submission.BoseGases.fsKinCoeff c₂)
    (G := Submission.BoseGases.fsKinCoeff c₁) (Submission.BoseGases.fsKinCoeff_nonneg c₂)
    (fun r => fsKinCoeff_anti h12) (integrable_bsKinFTWeight hℓ u hψ hc₁)

/-! ## 7. `mainWord ≥ 0` when `1 ≤ d` -/

theorem mainWord_nonneg_of_one_le {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) (hd : 1 ≤ d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (u : E3) {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    0 ≤ Work.BoseKinLoc.mainWord ℓ d s εT u ψ := by
  have hsℓ : 0 < s * ℓ := mul_pos hs hℓ
  have hcoef : (2 * (d * s * ℓ))⁻¹ ≤ (2 * (s * ℓ))⁻¹ := by
    rw [show (2 * (d * s * ℓ))⁻¹ = 1 / (2 * (d * s * ℓ)) by rw [one_div]]
    rw [show (2 * (s * ℓ))⁻¹ = 1 / (2 * (s * ℓ)) by rw [one_div]]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hsℓ.le]
  have hA : Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
      ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ :=
    bsOneBody_mono_of_coeff_le hℓ u hψ (by positivity) (by positivity) hcoef
  have hA1 : 0 ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ :=
    Work.BSKinetic.bsOneBody_nonneg (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r) u ψ
  have hA2 : 0 ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ :=
    le_trans hA1 hA
  unfold Work.BoseKinLoc.mainWord
  rcases le_total εT 1 with h1 | h1
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) hA1, mul_nonneg hεT hA2]
  · nlinarith [hA1, hA, hεT, mul_nonneg hεT (sub_nonneg.mpr hA)]

/-! ## 8. `fsT ≥ 0` when `1 ≤ d` -/

theorem fsT_nonneg_of_one_le {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 1 ≤ d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hb : 0 ≤ b) (u : E3) {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    0 ≤ Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have hds : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hdℓ : 0 < d * ℓ := mul_pos hds hℓ
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := hψ.continuous.sub continuous_const
  have hI : Integrable (fun z : E3 => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
      (hcont.pow 2).continuousOn).mono_set
        (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ u)
  have hneu : 0 ≤ Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
    have hn := Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 u hI
    unfold Work.BoseKinLoc.neuWord
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεT) ha2) hn
  have hgap : 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ := Work.BoseKinLoc.gapWord_nonneg hb hℓ.le u ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b u ψ :=
    Work.BoseKinLoc.momWord_nonneg hb hεT hdℓ.le u ψ
  have hmain : 0 ≤ Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    mainWord_nonneg_of_one_le hℓ hd hs hεT u hψ
  rw [Work.BoseKinLoc.fsT_eq_sum]
  linarith

/-! ## 9. `kinFormB ≥ 0` when `1 ≤ d` -/

theorem kinFormB_nonneg_of_one_le {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 1 ≤ d)
    (hs : 0 < s) (hεT : 0 ≤ εT) (hb : 0 ≤ b) (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    0 ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ) := by
  unfold Work.BoseKinLoc.kinFormB
  refine mul_nonneg (zpow_nonneg hℓ.le _) (Finset.sum_nonneg fun i _ => ?_)
  refine integral_nonneg fun x => ?_
  refine mul_nonneg (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x i)) ?_
  have hfib : ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x) :=
    Φ.contDiff.comp (by
      rw [contDiff_pi]
      intro j
      simp only [Function.update_apply]
      split_ifs with hji
      · exact contDiff_id
      · exact contDiff_const)
  exact fsT_nonneg_of_one_le hℓ hd hs hεT hb 0 hfib

/-! ## 10. The target -/

theorem isLowB_chemBoundAlt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) {J μ : ℝ}
    (hJ : 0 ≤ J) {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hL : Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ))
    (hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    (hB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :
    4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let P : Work.BoseBox.FSParams := Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)
  -- the splitting of the box word
  have hsplit : Work.BoseKinLoc.boxFormB n v (Submission.BoseGases.g0 v h) ℓ μ P.d P.s P.eT P.b
        (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.pairPartB n v ℓ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable (Φ : Submission.BoseGases.X n → ℝ) hA hB
  have hL' : Work.BoseKinLoc.boxFormB n v (Submission.BoseGases.g0 v h) ℓ μ P.d P.s P.eT P.b
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ℓ ^ 3 * Work.UBB.Theta (_root_.BoseGases.a v) J μ * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    simp only [Work.BoseBoxFix.IsLowB, Work.BoseBoxFix.wordB, Work.BoseBoxFix.normB] at hL
    exact hL
  -- kinetic nonnegativity
  have hkin : 0 ≤ Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b (Φ : Submission.BoseGases.X n → ℝ) := by
    by_cases ht : 0 < μ * (_root_.BoseGases.a v) ^ 3
    · have hμne : μ ≠ 0 := by rintro rfl; simp at ht
      have hμ2 : 0 < μ ^ 2 := by simpa [pow_two] using mul_self_pos.mpr hμne
      have hma : 0 < μ * (_root_.BoseGases.a v) := by
        have hcub : 0 < (μ * (_root_.BoseGases.a v)) ^ 3 := by
          have hid : (μ * (_root_.BoseGases.a v)) ^ 3
              = μ ^ 2 * (μ * (_root_.BoseGases.a v) ^ 3) := by ring
          rw [hid]; exact mul_pos hμ2 ht
        nlinarith [sq_nonneg (μ * (_root_.BoseGases.a v))]
      have hKl : 0 < P.Kl := by
        show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2))
        exact Work.BoseBox.fsXp_pos ht
      have hℓpos : 0 < ℓ := by
        show 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide]
        exact mul_pos hKl (Real.rpow_pos_of_pos hma _)
      have hdpos : 0 < P.d := by
        show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
        exact Work.BoseBox.fsXp_pos ht
      have hspos : 0 < P.s := by
        show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1
        exact Work.BoseBox.fsXp_pos ht
      have heT0 : 0 ≤ P.eT := (Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3)
        (c := 23 / 4) ht).le
      have hb : 0 ≤ P.b := by
        show (0 : ℝ) ≤ Work.BoseBox.bValue
        norm_num [Work.BoseBox.bValue]
      by_cases ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1
      · have heT1 : P.eT ≤ 1 := by
          show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (23 / 4) ≤ 1
          rw [Work.BoseBox.fsXp]
          exact Real.rpow_le_one ht.le ht1 (by norm_num)
        exact Work.BoseKinLoc.Word.kinFormB_nonneg hℓpos hdpos hspos heT0 heT1 hb Φ
      · have ht1' : 1 ≤ μ * (_root_.BoseGases.a v) ^ 3 := le_of_lt (not_le.mp ht1)
        have hd1 : 1 ≤ P.d := by
          show 1 ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
          rw [Work.BoseBox.fsXp]
          exact Real.one_le_rpow ht1' (by norm_num)
        exact kinFormB_nonneg_of_one_le hℓpos hd1 hspos heT0 hb Φ
    · have ht0 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 0 := not_lt.mp ht
      have hℓz : ℓ = 0 := sideAt_eq_zero_of_nonpos ht0
      rw [hℓz]
      simp [Work.BoseKinLoc.kinFormB]
  have hpair : 0 ≤ Work.BoseKinLoc.pairPartB n v ℓ (Φ : Submission.BoseGases.X n → ℝ) :=
    pairPartB_nonneg hv ℓ (Φ : Submission.BoseGases.X n → ℝ)
  have hchem : Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ℓ ^ 3 * Work.UBB.Theta (_root_.BoseGases.a v) J μ * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have hw := hL'
    rw [hsplit] at hw
    linarith
  -- `chemPartB = -μ·M`
  have hchem_eq : Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ
        (Φ : Submission.BoseGases.X n → ℝ)
      = -μ * (∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
    have hfun : (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (-μ * (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
        = fun x : Submission.BoseGases.X n => -μ * (((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
      funext x; ring
    unfold Work.BoseKinLoc.chemPartB
    rw [hfun, MeasureTheory.integral_const_mul]
  -- `-(ℓ³·Theta·‖Φ‖²) = LHS`
  have hTheta : -(ℓ ^ 3 * Work.UBB.Theta (_root_.BoseGases.a v) J μ *
        Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      = 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
    unfold Work.UBB.Theta
    ring
  have hgoal : 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ μ * (∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
    linarith [hchem, hchem_eq, hTheta]
  exact hgoal

end Work.BoseFixB1B
