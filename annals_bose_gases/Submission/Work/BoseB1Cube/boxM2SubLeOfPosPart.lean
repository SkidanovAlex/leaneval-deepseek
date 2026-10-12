import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.smallWinNodes
import Submission.Work.BoseB1Cube.swhTruncAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.boxM2SubLeOfPosPart`

The truncation comparison for the localised two-body mass: replacing the numerator `g₀ = v(1−ω₀)`
of the sliding pair kernel by the truncated potential `min v K` costs at most the positive part
`(g₀ − K)₊`, weighted by the `χ ⊗ χ` pairing mass:

    boxM2 (wSmallPair g₀) − boxM2 (wSmallPair (min v K))
      ≤ 2·(smallConvLower M)⁻¹ · chiMass · ∫ (g₀ − K)₊ .

## Structure of the proof

Everything is pointwise plus three integral facts:

* the numerator is *linear*: `wSmallPair f₁ − wSmallPair f₂ = wSmallPair (f₁ − f₂)`;
* the difference of numerators `f = g₀ − min(v·)K` satisfies `f ≤ (g₀ − K)₊` (`0 ≤ v`, `g₀ ≤ v`
  a.e., `min v K ≥ 0`) and is supported in `ball 0 R`, so the sharp pointwise kernel bound
  `wSmallPair f x y ≤ 2/smallConvLower M · χ(x)·(g₀ − K)₊(x−y)·χ(y)` holds;
* the `χ ⊗ χ` pairing (`pairing_le_chiSq_mul_abs_integral`, AM–GM + Tonelli) turns the latter into
  `chiMass · ∫ (g₀ − K)₊`.

Integrability of all three kernels on `B(u) × B(u)` follows from the same pointwise bounds, and the
`boxM2` integrals over `B(u) × B(u)` may be replaced by global integrals because `χ_{B(u)}` is
supported in `B(u)` (`chiSmallB_support_mem_dlBox`).
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Elementary analytic facts -/

/-- **The sharp pointwise bound for the sliding profile, with the numerator itself on the right.**
This is `abs_wSmallScaled_div_convScale_le` with the constant `Bv` replaced by the value `|f z|`
(valid because the bound is proved pointwise in `z`). -/
theorem abs_wSmallScaled_div_convScale_le_self {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {f : E3 → ℝ}
    (hfsupp : ∀ z : E3, R ≤ ‖z‖ → f z = 0) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (z : E3) :
    |Submission.BoseGases.wSmallScaled M (ℓ * d) f z / Submission.BoseGases.convScale ℓ z|
      ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * |f z| := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hscl : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  by_cases hnorm : ‖z‖ ≤ R
  · have hcv : (1 : ℝ) / 2 ≤ Submission.BoseGases.convScale ℓ z :=
      Submission.BoseGases.convScale_ge_half_ball hℓ (norm_nonneg z)
        (le_trans hnorm hRχ) le_rfl
    have hpos : 0 < Submission.BoseGases.convScale ℓ z := by linarith
    have hinv : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ 2 := by
      rw [abs_of_pos (inv_pos.mpr hpos), inv_le_iff_one_le_mul₀ hpos]
      linarith
    have hD : |Submission.BoseGases.wSmallScaled M (ℓ * d) f z|
        ≤ |f z| / Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hc hfsupp hRd z
    rw [div_eq_mul_inv, abs_mul]
    calc |Submission.BoseGases.wSmallScaled M (ℓ * d) f z|
            * |(Submission.BoseGases.convScale ℓ z)⁻¹|
        ≤ (|f z| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
          mul_le_mul hD hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) hscl.le)
      _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * |f z| := by
          rw [div_eq_mul_inv]; ring
  · push_neg at hnorm
    have hz0 : f z = 0 := hfsupp z (le_of_lt hnorm)
    have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) f z = 0 := by
      rw [Submission.BoseGases.wSmallScaled, hz0, zero_div]
    rw [hw0, zero_div, abs_zero, hz0, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hscl.le)) le_rfl

/-- Pointwise absolute domination of the sliding pair kernel by `χ ⊗ |f| ⊗ χ`. -/
theorem abs_wSmallPair_le_self {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {f : E3 → ℝ}
    (hfsupp : ∀ z : E3, R ≤ ‖z‖ → f z = 0) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u x y : E3) :
    |Submission.BoseGases.wSmallPair M ℓ d u f x y|
      ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
        (Submission.BoseGases.chiSmallB M ℓ d u x * |f (x - y)|
          * Submission.BoseGases.chiSmallB M ℓ d u y) := by
  have hx0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hy0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hscl : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hmid := abs_wSmallScaled_div_convScale_le_self (M := M) hM hℓ hd hfsupp hRd hRχ (x - y)
  have hunfold : Submission.BoseGases.wSmallPair M ℓ d u f x y
      = Submission.BoseGases.chiSmallB M ℓ d u x *
        (Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
          / Submission.BoseGases.convScale ℓ (x - y)) *
        Submission.BoseGases.chiSmallB M ℓ d u y := rfl
  rw [hunfold, abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hy0]
  calc Submission.BoseGases.chiSmallB M ℓ d u x *
          |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
            / Submission.BoseGases.convScale ℓ (x - y)| *
          Submission.BoseGases.chiSmallB M ℓ d u y
      ≤ Submission.BoseGases.chiSmallB M ℓ d u x *
          (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * |f (x - y)|) *
          Submission.BoseGases.chiSmallB M ℓ d u y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid hx0) hy0
    _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
          (Submission.BoseGases.chiSmallB M ℓ d u x * |f (x - y)|
            * Submission.BoseGases.chiSmallB M ℓ d u y) := by ring

/-- **Pointwise truncation bound at the level of the numerator.**  If `f` is supported in
`ball 0 R` and `f (x−y) ≤ F (x−y)` with `0 ≤ F (x−y)`, then the sliding kernel of `f` is dominated
by `2/smallConvLower M · χ(x)·F(x−y)·χ(y)`. -/
theorem wSmallPair_le_of_sub_le {f F : E3 → ℝ} {R : ℝ} {M : ℕ} {ℓ d : ℝ}
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hfsupp : ∀ z : E3, R ≤ ‖z‖ → f z = 0) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : E3) (hz : f (x - y) ≤ F (x - y)) (hFnn : 0 ≤ F (x - y)) :
    Submission.BoseGases.wSmallPair M ℓ d u f x y
      ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
        (Submission.BoseGases.chiSmallB M ℓ d u x * F (x - y)
          * Submission.BoseGases.chiSmallB M ℓ d u y) := by
  have hscl : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hx0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hy0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hcoef : 0 ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hscl.le)
  have key : (f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
        / Submission.BoseGases.convScale ℓ (x - y)
      ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * F (x - y) := by
    by_cases hf : f (x - y) ≤ 0
    · have h1 : f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) ≤ 0 := by
        rw [div_eq_mul_inv]
        exact mul_nonpos_of_nonpos_of_nonneg hf
          (inv_nonneg.mpr (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y)))
      have h2 : (f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
          / Submission.BoseGases.convScale ℓ (x - y) ≤ 0 := by
        rw [div_eq_mul_inv]
        exact mul_nonpos_of_nonpos_of_nonneg h1
          (inv_nonneg.mpr (Submission.BoseGases.convScale_nonneg ℓ (x - y)))
      exact le_trans h2 (mul_nonneg hcoef hFnn)
    · have hfpos : 0 < f (x - y) := lt_of_not_ge hf
      have habs :=
        abs_wSmallScaled_div_convScale_le_self (M := M) hM hℓ hd hfsupp hRd hRχ (x - y)
      have hle : (f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
          / Submission.BoseGases.convScale ℓ (x - y)
          ≤ |(f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
            / Submission.BoseGases.convScale ℓ (x - y)| := le_abs_self _
      have habs2 : |f (x - y)| = f (x - y) := abs_of_pos hfpos
      calc (f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
              / Submission.BoseGases.convScale ℓ (x - y)
          ≤ |(f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
              / Submission.BoseGases.convScale ℓ (x - y)| := hle
        _ ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * |f (x - y)| := habs
        _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * f (x - y) := by rw [habs2]
        _ ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * F (x - y) :=
            mul_le_mul_of_nonneg_left hz hcoef
  have hunfold : Submission.BoseGases.wSmallPair M ℓ d u f x y
      = Submission.BoseGases.chiSmallB M ℓ d u x *
        ((f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
          / Submission.BoseGases.convScale ℓ (x - y)) *
        Submission.BoseGases.chiSmallB M ℓ d u y := rfl
  rw [hunfold]
  calc Submission.BoseGases.chiSmallB M ℓ d u x *
          ((f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
            / Submission.BoseGases.convScale ℓ (x - y)) *
          Submission.BoseGases.chiSmallB M ℓ d u y
      ≤ Submission.BoseGases.chiSmallB M ℓ d u x *
          (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * F (x - y)) *
          Submission.BoseGases.chiSmallB M ℓ d u y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hx0) hy0
    _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
          (Submission.BoseGases.chiSmallB M ℓ d u x * F (x - y)
            * Submission.BoseGases.chiSmallB M ℓ d u y) := by ring

/-- Linearity of the sliding pair kernel in its numerator. -/
theorem wSmallPair_sub_eq {M : ℕ} {ℓ d : ℝ} {u : E3} (f₁ f₂ : E3 → ℝ) (x y : E3) :
    Submission.BoseGases.wSmallPair M ℓ d u f₁ x y
      - Submission.BoseGases.wSmallPair M ℓ d u f₂ x y
      = Submission.BoseGases.wSmallPair M ℓ d u (fun z => f₁ z - f₂ z) x y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  ring

/-- The pure-real core: `a − min(v, K) ≤ (a − K)₊` when `a ≤ v`, `0 ≤ v`, `0 ≤ K`. -/
theorem sub_min_le_posPart {a v K : ℝ} (h : a ≤ v) (hv : 0 ≤ v) (hK : 0 ≤ K) :
    a - min v K ≤ max (a - K) 0 := by
  by_cases ha : a ≤ 0
  · have h0 : 0 ≤ min v K := le_min hv hK
    exact le_trans (by linarith) (le_max_right _ _)
  · by_cases hvK : v ≤ K
    · rw [min_eq_left hvK]
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hvK))]
      exact le_max_left _ _

/-! ## 1. The truncation comparison -/

theorem boxM2SubLeOfPosPart {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hm : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) => min (v z) K) MeasureTheory.volume)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
      - Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K))
    ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Work.SmallBoxSliding.chiMass M ℓ d u
        * (∫ z : EuclideanSpace ℝ (Fin 3), max (Submission.BoseGases.g0 v h z - K) 0) := by
  -- ## abbreviations
  set g : E3 → ℝ := Submission.BoseGases.g0 v h with hgdef
  set gt : E3 → ℝ := fun z => min (v z) K with hgtdef
  set F : E3 → ℝ := fun z => max (Submission.BoseGases.g0 v h z - K) 0 with hFdef
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hscl : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hcoef : 0 ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hscl.le)
  have hχ0 : ∀ x : E3, 0 ≤ χ x := fun x => Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχc : Continuous χ := Submission.BoseGases.chiSmallB_continuous hM hℓ hd u
  have hχs : HasCompactSupport χ := Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u
  have hFnn : ∀ z : E3, 0 ≤ F z := fun z => le_max_right _ _
  -- ## basic support and integrability facts
  have hAmeas : MeasurableSet A := by
    have hd1 : Submission.BoseGases.dlBox ℓ d u
        = Submission.BoseGases.acube ℓ
          ∩ (fun x : E3 => x - (ℓ * d) • u) ⁻¹' Submission.BoseGases.acube (ℓ * d) := rfl
    rw [hAdef, hd1]
    exact (Submission.BoseGases.acube_measurable ℓ).inter
      ((Submission.BoseGases.acube_measurable (ℓ * d)).preimage
        (continuous_id.sub continuous_const).measurable)
  have hχz : ∀ z : E3, z ∉ A → Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
    intro z hz
    by_contra hne
    exact hz (by rw [hAdef]; exact Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
  have hWsupp : ∀ (f : E3 → ℝ) (p : E3 × E3), p ∉ A ×ˢ A →
      Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2 = 0 := by
    intro f p hp
    have h1 : p.1 ∉ A ∨ p.2 ∉ A := by
      by_contra hcon
      rw [not_or] at hcon
      exact hp (Set.mk_mem_prod (of_not_not hcon.1) (of_not_not hcon.2))
    rcases h1 with h1 | h1
    · simp only [Submission.BoseGases.wSmallPair, hχz p.1 h1, zero_mul]
    · simp only [Submission.BoseGases.wSmallPair, hχz p.2 h1, mul_zero]
  have hboxeq : ∀ (W : E3 × E3 → ℝ), (∀ p : E3 × E3, p ∉ A ×ˢ A → W p = 0) →
      (∫ p in A ×ˢ A, W p) = ∫ p : E3 × E3, W p := by
    intro W hW
    rw [← MeasureTheory.integral_indicator (hAmeas.prod hAmeas)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ A ×ˢ A
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, hW p hp]
  have hgsupp : ∀ z : E3, R ≤ ‖z‖ → g z = 0 := fun z hz =>
    Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hgtsupp : ∀ z : E3, R ≤ ‖z‖ → gt z = 0 := by
    intro z hz
    have h1 : v z = 0 := Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
    rw [show gt z = min (v z) K from rfl, h1, min_eq_left hK]
  have hg_int : Integrable g := Submission.BoseGases.g0_integrable hR hv_supp h
  have hgt_int : Integrable gt := by
    have hsupp_eq : (Metric.ball (0 : E3) R).indicator gt = gt := by
      funext z
      by_cases hz : z ∈ Metric.ball (0 : E3) R
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        have hRz : R ≤ ‖z‖ := by
          rw [Metric.mem_ball, dist_zero_right] at hz
          exact le_of_not_gt hz
        exact (hgtsupp z hRz).symm
    rw [← hsupp_eq, MeasureTheory.integrable_indicator_iff measurableSet_ball]
    refine MeasureTheory.IntegrableOn.of_bound measure_ball_lt_top
      (hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) K ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hv z) hK)]
    exact min_le_right _ _
  have hF_int : Integrable F := by
    refine Integrable.mono' hg_int.abs ?_ ?_
    · exact ((hg_int.aemeasurable.sub
        (aemeasurable_const : AEMeasurable (fun _ : E3 => K) volume)).max
          (aemeasurable_const : AEMeasurable (fun _ : E3 => (0 : ℝ)) volume)).aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      change max (g z - K) 0 ≤ |g z|
      by_cases h0 : (0 : ℝ) ≤ g z
      · calc max (g z - K) 0 ≤ max (g z) 0 := max_le_max (by linarith) le_rfl
          _ = g z := max_eq_left h0
          _ ≤ |g z| := le_abs_self _
      · rw [max_eq_right (by linarith : g z - K ≤ 0)]
        exact abs_nonneg _
  -- ## the pairing bound behind the right-hand side
  have hpairF := Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral hχ0 hχc hχs hF_int
  have hstep3 : (∫ p : E3 × E3, χ p.1 * F (p.1 - p.2) * χ p.2)
      ≤ (∫ x : E3, χ x ^ 2) * (∫ z : E3, F z) := by
    have h1 : (fun p : E3 × E3 => χ p.1 * F (p.1 - p.2) * χ p.2)
        = fun p : E3 × E3 => χ p.1 * |F (p.1 - p.2)| * χ p.2 := by
      funext p
      rw [abs_of_nonneg (hFnn _)]
    have h2 : (∫ z : E3, |F z|) = ∫ z : E3, F z :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => abs_of_nonneg (hFnn z)))
    rw [h1]
    refine le_trans hpairF.2 ?_
    exact le_of_eq (by rw [h2])
  -- ## pointwise domination of the difference kernel
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      (volume : Measure (E3 × E3)) (volume : Measure E3) :=
    Measure.quasiMeasurePreserving_snd.comp
      (MeasureTheory.measurePreserving_prod_sub_swap (volume : Measure E3)
        (volume : Measure E3)).quasiMeasurePreserving
  have hgv : ∀ᵐ p ∂(volume : Measure (E3 × E3)), g (p.1 - p.2) ≤ v (p.1 - p.2) := by
    have h0 := hqmp.ae (Submission.BoseGases.g0_abs_le_v_ae hR hv hvrad hv_supp h)
    filter_upwards [h0] with p hp
    exact le_trans (le_abs_self _) hp
  have hfsupp : ∀ z : E3, R ≤ ‖z‖ → g z - gt z = 0 := by
    intro z hz
    rw [hgsupp z hz, hgtsupp z hz, sub_zero]
  have hpt : ∀ᵐ p ∂(volume : Measure (E3 × E3)),
      Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2
        - Submission.BoseGases.wSmallPair M ℓ d u gt p.1 p.2
      ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * (χ p.1 * F (p.1 - p.2) * χ p.2) := by
    filter_upwards [hgv] with p hp
    rw [wSmallPair_sub_eq (f₁ := g) (f₂ := gt) p.1 p.2]
    have hFr : g (p.1 - p.2) - min (v (p.1 - p.2)) K ≤ F (p.1 - p.2) :=
      sub_min_le_posPart hp (hv _) hK
    exact wSmallPair_le_of_sub_le hM hℓ hd hfsupp hRd hRχ u p.1 p.2 hFr (hFnn _)
  -- ## integrability of the three kernels
  have hpair_of : ∀ (f : E3 → ℝ), Integrable f → Integrable (fun p : E3 × E3 =>
      χ p.1 * |f (p.1 - p.2)| * χ p.2) (volume : Measure (E3 × E3)) :=
    fun f hf => (Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral hχ0 hχc hχs hf).1
  have haesm_of : ∀ (f : E3 → ℝ), AEMeasurable f volume → AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      (volume : Measure (E3 × E3)) := by
    intro f hf
    have hfm : AEMeasurable (fun p : E3 × E3 => f (p.1 - p.2)) (volume : Measure (E3 × E3)) :=
      Work.BoseFixB1S.subPair_aemeasurable hf
    have hcsm : AEMeasurable
        (fun p : E3 × E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
        (volume : Measure (E3 × E3)) :=
      ((Submission.BoseGases.conv3Small_continuous hM).comp
        ((continuous_fst.sub continuous_snd).const_smul ((ℓ * d)⁻¹))).aemeasurable
    have hcs : AEMeasurable
        (fun p : E3 × E3 => Submission.BoseGases.convScale ℓ (p.1 - p.2))
        (volume : Measure (E3 × E3)) :=
      ((Submission.BoseGases.convScale_continuous ℓ).comp
        (continuous_fst.sub continuous_snd)).aemeasurable
    have hχ1 : AEMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1)
        (volume : Measure (E3 × E3)) :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp continuous_fst).aemeasurable
    have hχ2 : AEMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.2)
        (volume : Measure (E3 × E3)) :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp continuous_snd).aemeasurable
    have hmid : AEMeasurable (fun p : E3 × E3 =>
        (f (p.1 - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
          / Submission.BoseGases.convScale ℓ (p.1 - p.2)) (volume : Measure (E3 × E3)) :=
      (hfm.div hcsm).div hcs
    have hfinal : AEMeasurable (fun p : E3 × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d u p.1 * ((f (p.1 - p.2)
          / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
          / Submission.BoseGases.convScale ℓ (p.1 - p.2))
        * Submission.BoseGases.chiSmallB M ℓ d u p.2) (volume : Measure (E3 × E3)) :=
      (hχ1.mul hmid).mul hχ2
    simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
      using hfinal.aestronglyMeasurable
  have hint : ∀ (f : E3 → ℝ), Integrable f →
      (∀ z : E3, R ≤ ‖z‖ → f z = 0) →
      Integrable (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
        (volume : Measure (E3 × E3)) := by
    intro f hf hfsp
    refine Integrable.mono'
      ((hpair_of f hf).const_mul (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹))
      (haesm_of f hf.aemeasurable) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact abs_wSmallPair_le_self hM hℓ hd hfsp hRd hRχ u p.1 p.2
  have hint_g : Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2) (volume : Measure (E3 × E3)) :=
    hint g hg_int hgsupp
  have hint_gt : Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.wSmallPair M ℓ d u gt p.1 p.2) (volume : Measure (E3 × E3)) :=
    hint gt hgt_int hgtsupp
  have hint_rhs : Integrable (fun p : E3 × E3 =>
      2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * (χ p.1 * F (p.1 - p.2) * χ p.2))
      (volume : Measure (E3 × E3)) := by
    refine MeasureTheory.Integrable.congr
      ((hpair_of F hF_int).const_mul (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)) ?_
    filter_upwards with p
    rw [abs_of_nonneg (hFnn _)]
  -- ## the two `boxM2` integrals and the final chain
  have hb1 : Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
        (Submission.BoseGases.wSmallPair M ℓ d u g)
      = ∫ p : E3 × E3, Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2 :=
    hboxeq _ (hWsupp g)
  have hb2 : Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
        (Submission.BoseGases.wSmallPair M ℓ d u gt)
      = ∫ p : E3 × E3, Submission.BoseGases.wSmallPair M ℓ d u gt p.1 p.2 :=
    hboxeq _ (hWsupp gt)
  have hcChiMass : Work.SmallBoxSliding.chiMass M ℓ d u = ∫ x : E3, χ x ^ 2 := rfl
  have hstep1 : (∫ p : E3 × E3, (Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2
        - Submission.BoseGases.wSmallPair M ℓ d u gt p.1 p.2))
      ≤ ∫ p : E3 × E3,
          2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * (χ p.1 * F (p.1 - p.2) * χ p.2) :=
    MeasureTheory.integral_mono_ae (hint_g.sub hint_gt) hint_rhs hpt
  calc Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
          (Submission.BoseGases.wSmallPair M ℓ d u g)
        - Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
          (Submission.BoseGases.wSmallPair M ℓ d u gt)
      = (∫ p : E3 × E3, Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2)
        - ∫ p : E3 × E3, Submission.BoseGases.wSmallPair M ℓ d u gt p.1 p.2 := by
        rw [hb1, hb2]
    _ = ∫ p : E3 × E3, (Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2
          - Submission.BoseGases.wSmallPair M ℓ d u gt p.1 p.2) :=
        (MeasureTheory.integral_sub hint_g hint_gt).symm
    _ ≤ ∫ p : E3 × E3,
          2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * (χ p.1 * F (p.1 - p.2) * χ p.2) := hstep1
    _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹
          * ∫ p : E3 × E3, χ p.1 * F (p.1 - p.2) * χ p.2 := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹
          * ((∫ x : E3, χ x ^ 2) * (∫ z : E3, F z)) :=
        mul_le_mul_of_nonneg_left hstep3 hcoef
    _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Work.SmallBoxSliding.chiMass M ℓ d u
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              max (Submission.BoseGases.g0 v h z - K) 0) := by
        rw [hcChiMass]
        ring

end Work.BoseB1Cube
