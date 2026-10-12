import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.QCrossQuarterD2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# eq:dvapriori `w := wPairC v` per-pair bound (the w-version of qcross_d2)

Mirror of `QCrossQuarterD2.qcross_d2_pair_quarter` with the numerator
`g0 v h ↦ v` in the mass/kernel parts only (the q4B-square term is
unchanged — it already uses `wPair ℓ v`).  Substitutions:
`Integrable (g0 v h)` ↦ `Integrable v` (`memLp_one_iff_integrable.mp
hv_memL1`), support `g0_zero_of_norm_ge` ↦ `PotSupport.v_eq_zero_of_norm_ge`,
the ae bound `WW ≤ wt` (from |w₁| ≤ w) becomes POINTWISE `|wPair(v)| ≤
wPair(v)` (`wPairC_nonneg hv_nonneg`, v ≥ 0 pointwise), and the mass tail
constants scale with `∫v`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
set_option maxHeartbeats 400000

/-- Per-pair `w`-version (eq:dvapriori T₄-form): with `w := wPairC v`,
`|∫(P_iP_jΦ)(Q_jQ_iΦ)·w| ≤ (5/2)∫(PP)²|w| + (1/2)∫(SS)²|w| + (1/8)∫q4B²·w`. -/
lemma qcross_w_d2_pair_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
      ≤ (5 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ v (x i) (x j)|))
        + (1 / 8) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let FF : X N → ℝ := fun x => aP ℓ i (aP ℓ j Φ) x
  let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
  let WW : X N → ℝ := fun x => |wPair ℓ v (x i) (x j)|
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  have hFc : Continuous FF := by
    dsimp [FF]
    exact aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : X N => aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hvi : MeasureTheory.Integrable v := (memLp_one_iff_integrable.mp hv_memL1)
  have hvsupp : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    v_eq_zero_of_norm_ge (h := hv_supp) hz
  have hF2W : Integrable (fun x : X N => (FF x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : X N => (FF x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hvi hvsupp hRℓ hij (S := FF) hFc
    simpa [FF, WW, μ, IntegrableOn] using hs
  have hS2W : Integrable (fun x : X N => (SS x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : X N => (SS x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hvi hvsupp hRℓ hij (S := SS) hSc
    simpa [SS, WW, μ, IntegrableOn] using hs
  have hB2wt : Integrable (fun x : X N => (BB x) ^ 2 * wt x) μ := by
    have hs := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, wt, μ, IntegrableOn] using hs
  have hU : Integrable (fun x : X N =>
      (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) μ := by
    have h1 : Integrable (fun x : X N =>
        (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      (hF2W.const_mul (5 / 2)).add (hS2W.const_mul (1 / 2))
    refine (h1.add (hB2wt.const_mul (1 / 8))).congr ?_
    filter_upwards with x
    rfl
  have hWnn : ∀ x : X N, 0 ≤ WW x := by
    intro x
    dsimp [WW]
    exact abs_nonneg _
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hWlewt : ∀ x : X N, WW x ≤ wt x := by
    intro x
    dsimp [WW, wt]
    have hw0 : 0 ≤ wPair ℓ v (x i) (x j) := wPairC_nonneg hv_nonneg ℓ (x i) (x j)
    rw [abs_of_nonneg hw0]
  have hmain : ∀ᵐ x ∂μ,
      |FF x * (QQ x * wPair ℓ v (x i) (x j))|
        ≤ (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x) := by
    filter_upwards [homxb] with x homx1
    have hQQ : QQ x = BB x - omx x * SS x := by
      dsimp [QQ, BB, SS, omx, q4B, omC]
      ring
    have hQQb : |QQ x| ≤ |BB x| + |SS x| := by
      rw [hQQ]
      calc
        |BB x - omx x * SS x| = |BB x + (-(omx x * SS x))| := by rw [sub_eq_add_neg]
        _ ≤ |BB x| + |-(omx x * SS x)| := abs_add_le _ _
        _ = |BB x| + |omx x * SS x| := by rw [abs_neg]
        _ = |BB x| + |omx x| * |SS x| := by rw [abs_mul]
        _ ≤ |BB x| + 1 * |SS x| := by
          nlinarith [mul_le_mul_of_nonneg_right homx1 (abs_nonneg (SS x))]
        _ = |BB x| + |SS x| := by ring
    have hW0 : 0 ≤ WW x := hWnn x
    have hF1 : |FF x| * |QQ x| * WW x ≤ |FF x| * (|BB x| + |SS x|) * WW x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQQb (abs_nonneg (FF x))) hW0
    have hFB1 : |FF x| * |BB x| ≤ 2 * (FF x) ^ 2 + (1 / 8) * (BB x) ^ 2 := by
      rw [← sq_abs (FF x), ← sq_abs (BB x)]
      have hq : 0 ≤ (4 * |FF x| - |BB x|) ^ 2 := sq_nonneg _
      nlinarith
    have hFB2 : |FF x| * |BB x| * WW x ≤ (2 * (FF x) ^ 2 + (1 / 8) * (BB x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFB1 hW0
    have hFS1 : |FF x| * |SS x| ≤ (1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2 :=
      abs_mul_le_half_sq_sq (FF x) (SS x)
    have hFS2 : |FF x| * |SS x| * WW x ≤ ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFS1 hW0
    have hBW : (1 / 8) * ((BB x) ^ 2 * WW x) ≤ (1 / 8) * ((BB x) ^ 2 * wt x) := by
      have h1 : (BB x) ^ 2 * WW x ≤ (BB x) ^ 2 * wt x := by
        nlinarith [mul_le_mul_of_nonneg_left (hWlewt x) (sq_nonneg (BB x))]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    calc
      |FF x * (QQ x * wPair ℓ v (x i) (x j))|
          = |FF x| * |QQ x * wPair ℓ v (x i) (x j)| := abs_mul _ _
      _ = |FF x| * (|QQ x| * |wPair ℓ v (x i) (x j)|) := by rw [abs_mul]
      _ = |FF x| * (|QQ x| * WW x) := by rfl
      _ = |FF x| * |QQ x| * WW x := by ring
      _ ≤ |FF x| * (|BB x| + |SS x|) * WW x := hF1
      _ = |FF x| * |BB x| * WW x + |FF x| * |SS x| * WW x := by ring
      _ ≤ (2 * (FF x) ^ 2 + (1 / 8) * (BB x) ^ 2) * WW x
          + ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
          exact add_le_add hFB2 hFS2
      _ = (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * WW x) := by ring
      _ ≤ (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x) := by
          nlinarith [hBW]
  have hL1 : |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
      ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ v (x i) (x j))| := by
    have hEq : (fun x : X N =>
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j))
        =ᵐ[μ] (fun x : X N => FF x * (QQ x * wPair ℓ v (x i) (x j))) := by
      refine ae_of_all _ (fun x => ?_)
      dsimp [FF, QQ]
      ring
    calc
      |∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
          = |∫ x : X N, FF x * (QQ x * wPair ℓ v (x i) (x j)) ∂μ| := by
            congr 1
            rw [integral_congr_ae (μ := μ) hEq]
      _ ≤ ∫ x : X N, |FF x * (QQ x * wPair ℓ v (x i) (x j))| ∂μ := by
            exact abs_integral_le_integral_abs (μ := μ)
  have hL2 : (∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ v (x i) (x j))|)
      ≤ ∫ x in abox N ℓ,
          ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) := by
    refine integral_mono_of_nonneg (μ := μ) ?_ hU ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hmain
  have hL3 : (∫ x : X N,
          ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) ∂μ)
      = (5 / 2) * (∫ x : X N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : X N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 8) * (∫ x : X N, (BB x) ^ 2 * wt x ∂μ) := by
    have hF5 : Integrable (fun x : X N => (5 / 2) * ((FF x) ^ 2 * WW x)) μ :=
      hF2W.const_mul (5 / 2)
    have hT2 : Integrable (fun x : X N => (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hS2W.const_mul (1 / 2)
    have hT3 : Integrable (fun x : X N => (1 / 8) * ((BB x) ^ 2 * wt x)) μ :=
      hB2wt.const_mul (1 / 8)
    have h12 : Integrable (fun x : X N =>
        (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hF5.add hT2
    calc
      (∫ x, ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) ∂μ)
          = (∫ x, ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) ∂μ)
            + (∫ x, (1 / 8) * ((BB x) ^ 2 * wt x) ∂μ) := by
              rw [← integral_add h12 hT3]
      _ = (∫ x, (5 / 2) * ((FF x) ^ 2 * WW x) ∂μ) + (∫ x, (1 / 2) * ((SS x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / 8) * ((BB x) ^ 2 * wt x) ∂μ) := by
              rw [integral_add hF5 hT2]
      _ = (5 / 2) * (∫ x, (FF x) ^ 2 * WW x ∂μ) + (1 / 2) * (∫ x, (SS x) ^ 2 * WW x ∂μ)
          + (1 / 8) * (∫ x, (BB x) ^ 2 * wt x ∂μ) := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
  calc
    |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
        ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ v (x i) (x j))| := hL1
    _ ≤ ∫ x in abox N ℓ,
        ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) := hL2
    _ = (5 / 2) * (∫ x : X N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : X N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 8) * (∫ x : X N, (BB x) ^ 2 * wt x ∂μ) := by
          simpa [μ] using hL3
    _ = (5 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ v (x i) (x j)|))
        + (1 / 8) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
          simp [μ, FF, QQ, SS, BB, WW, wt, mul_assoc, add_assoc]


/-- Absolute-value fibre bound for `|wPair(v)|` over the centred cube (the
`w := wPairC v` kernel); constant `chiSup²·2·(∫v)` (from the generic
`fibre_acube_abs_le` with `h := |v|` and `∫|v| = ∫v` pointwise by
`hv_nonneg`). -/
lemma vabs_fibre_acube_abs_le {R ℓ : ℝ} (hR : 0 < R) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvi : MeasureTheory.Integrable v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |(∫ y in acube ℓ, |wPair ℓ v x y|)| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, v z) := by
  let hAbs : ℝ³ → ℝ := fun z => |v z|
  have hAbsI : MeasureTheory.Integrable hAbs := by
    simpa [hAbs] using hvi.abs
  have hAbs_supp : ∀ z : ℝ³, R ≤ ‖z‖ → hAbs z = 0 := by
    intro z hz
    dsimp [hAbs]
    rw [v_eq_zero_of_norm_ge (h := hv_supp) hz, abs_zero]
  have hAbs_eq : (∫ z : ℝ³, |hAbs z|) = ∫ z : ℝ³, v z := by
    have hEq1 : (∫ z : ℝ³, |hAbs z|) = ∫ z : ℝ³, |v z| := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [hAbs]
      exact abs_abs (v z)
    have hEq2 : (∫ z : ℝ³, |v z|) = ∫ z : ℝ³, v z := by
      apply integral_congr_ae
      filter_upwards with z
      exact abs_of_nonneg (hv_nonneg z)
    rw [hEq1, hEq2]
  have hint : (∫ y in acube ℓ, |wPair ℓ v x y|)
      = ∫ y in acube ℓ, wPair ℓ hAbs x y := by
    apply integral_congr_ae
    filter_upwards with y
    exact wPair_abs_eq ℓ v x y
  calc
    |(∫ y in acube ℓ, |wPair ℓ v x y|)|
        = |∫ y in acube ℓ, wPair ℓ hAbs x y| := by
            rw [hint]
    _ ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |hAbs z|) := by
            exact fibre_acube_abs_le (h := hAbs) hℓ (le_of_lt hR) hRℓ hAbsI hAbs_supp x
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, v z) := by
            rw [hAbs_eq]


/-- Per-pair `w`-version of the q3 cross bound (eq:dvapriori Q3-form): with
`w := wPairC v`, `|∫(P_iQ_jΦ)(Q_jQ_iΦ)·w| ≤ (9/2)∫(P_iQ_jΦ)²|w| + (1/2)∫(SS)²|w|
+ (1/16)∫q4B²·w`.  Mirror of `qcross_w_d2_pair_quarter` (numerator `v`) with
`FF := aP_i(aQ_jΦ)` and the d13 coefficient rebalance (hFB1 : 4FF² + (1/16)BB²). -/
lemma qcross_w_d13_pair_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
      ≤ (9 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ v (x i) (x j)|))
        + (1 / 16) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let FF : X N → ℝ := fun x => aP ℓ i (aQ ℓ j Φ) x
  let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
  let WW : X N → ℝ := fun x => |wPair ℓ v (x i) (x j)|
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  have hFc : Continuous FF := by
    dsimp [FF]
    exact aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : X N => aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hvi : MeasureTheory.Integrable v := (memLp_one_iff_integrable.mp hv_memL1)
  have hvsupp : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    v_eq_zero_of_norm_ge (h := hv_supp) hz
  have hF2W : Integrable (fun x : X N => (FF x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : X N => (FF x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hvi hvsupp hRℓ hij (S := FF) hFc
    simpa [FF, WW, μ, IntegrableOn] using hs
  have hS2W : Integrable (fun x : X N => (SS x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : X N => (SS x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hvi hvsupp hRℓ hij (S := SS) hSc
    simpa [SS, WW, μ, IntegrableOn] using hs
  have hB2wt : Integrable (fun x : X N => (BB x) ^ 2 * wt x) μ := by
    have hs := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, wt, μ, IntegrableOn] using hs
  have hU : Integrable (fun x : X N =>
      (9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x)) μ := by
    have h1 : Integrable (fun x : X N =>
        (9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      (hF2W.const_mul (9 / 2)).add (hS2W.const_mul (1 / 2))
    refine (h1.add (hB2wt.const_mul (1 / 16))).congr ?_
    filter_upwards with x
    rfl
  have hWnn : ∀ x : X N, 0 ≤ WW x := by
    intro x
    dsimp [WW]
    exact abs_nonneg _
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hWlewt : ∀ x : X N, WW x ≤ wt x := by
    intro x
    dsimp [WW, wt]
    have hw0 : 0 ≤ wPair ℓ v (x i) (x j) := wPairC_nonneg hv_nonneg ℓ (x i) (x j)
    rw [abs_of_nonneg hw0]
  have hmain : ∀ᵐ x ∂μ,
      |FF x * (QQ x * wPair ℓ v (x i) (x j))|
        ≤ (9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x) := by
    filter_upwards [homxb] with x homx1
    have hQQ : QQ x = BB x - omx x * SS x := by
      dsimp [QQ, BB, SS, omx, q4B, omC]
      ring
    have hQQb : |QQ x| ≤ |BB x| + |SS x| := by
      rw [hQQ]
      calc
        |BB x - omx x * SS x| = |BB x + (-(omx x * SS x))| := by rw [sub_eq_add_neg]
        _ ≤ |BB x| + |-(omx x * SS x)| := abs_add_le _ _
        _ = |BB x| + |omx x * SS x| := by rw [abs_neg]
        _ = |BB x| + |omx x| * |SS x| := by rw [abs_mul]
        _ ≤ |BB x| + 1 * |SS x| := by
          nlinarith [mul_le_mul_of_nonneg_right homx1 (abs_nonneg (SS x))]
        _ = |BB x| + |SS x| := by ring
    have hW0 : 0 ≤ WW x := hWnn x
    have hF1 : |FF x| * |QQ x| * WW x ≤ |FF x| * (|BB x| + |SS x|) * WW x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQQb (abs_nonneg (FF x))) hW0
    have hFB1 : |FF x| * |BB x| ≤ 4 * (FF x) ^ 2 + (1 / 16) * (BB x) ^ 2 := by
      rw [← sq_abs (FF x), ← sq_abs (BB x)]
      have hq : 0 ≤ (8 * |FF x| - |BB x|) ^ 2 := sq_nonneg _
      nlinarith
    have hFB2 : |FF x| * |BB x| * WW x ≤ (4 * (FF x) ^ 2 + (1 / 16) * (BB x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFB1 hW0
    have hFS1 : |FF x| * |SS x| ≤ (1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2 :=
      abs_mul_le_half_sq_sq (FF x) (SS x)
    have hFS2 : |FF x| * |SS x| * WW x ≤ ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFS1 hW0
    have hBW : (1 / 16) * ((BB x) ^ 2 * WW x) ≤ (1 / 16) * ((BB x) ^ 2 * wt x) := by
      have h1 : (BB x) ^ 2 * WW x ≤ (BB x) ^ 2 * wt x := by
        nlinarith [mul_le_mul_of_nonneg_left (hWlewt x) (sq_nonneg (BB x))]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    calc
      |FF x * (QQ x * wPair ℓ v (x i) (x j))|
          = |FF x| * |QQ x * wPair ℓ v (x i) (x j)| := abs_mul _ _
      _ = |FF x| * (|QQ x| * |wPair ℓ v (x i) (x j)|) := by rw [abs_mul]
      _ = |FF x| * (|QQ x| * WW x) := by rfl
      _ = |FF x| * |QQ x| * WW x := by ring
      _ ≤ |FF x| * (|BB x| + |SS x|) * WW x := hF1
      _ = |FF x| * |BB x| * WW x + |FF x| * |SS x| * WW x := by ring
      _ ≤ (4 * (FF x) ^ 2 + (1 / 16) * (BB x) ^ 2) * WW x
          + ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
          exact add_le_add hFB2 hFS2
      _ = (9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * WW x) := by ring
      _ ≤ (9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x) := by
          nlinarith [hBW]
  have hL1 : |∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
      ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ v (x i) (x j))| := by
    have hEq : (fun x : X N =>
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j))
        =ᵐ[μ] (fun x : X N => FF x * (QQ x * wPair ℓ v (x i) (x j))) := by
      refine ae_of_all _ (fun x => ?_)
      dsimp [FF, QQ]
      ring
    calc
      |∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
          = |∫ x : X N, FF x * (QQ x * wPair ℓ v (x i) (x j)) ∂μ| := by
            congr 1
            rw [integral_congr_ae (μ := μ) hEq]
      _ ≤ ∫ x : X N, |FF x * (QQ x * wPair ℓ v (x i) (x j))| ∂μ := by
            exact abs_integral_le_integral_abs (μ := μ)
  have hL2 : (∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ v (x i) (x j))|)
      ≤ ∫ x in abox N ℓ,
          ((9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x)) := by
    refine integral_mono_of_nonneg (μ := μ) ?_ hU ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hmain
  have hL3 : (∫ x : X N,
          ((9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x)) ∂μ)
      = (9 / 2) * (∫ x : X N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : X N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 16) * (∫ x : X N, (BB x) ^ 2 * wt x ∂μ) := by
    have hF5 : Integrable (fun x : X N => (9 / 2) * ((FF x) ^ 2 * WW x)) μ :=
      hF2W.const_mul (9 / 2)
    have hT2 : Integrable (fun x : X N => (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hS2W.const_mul (1 / 2)
    have hT3 : Integrable (fun x : X N => (1 / 16) * ((BB x) ^ 2 * wt x)) μ :=
      hB2wt.const_mul (1 / 16)
    have h12 : Integrable (fun x : X N =>
        (9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hF5.add hT2
    calc
      (∫ x, ((9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x)) ∂μ)
          = (∫ x, ((9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) ∂μ)
            + (∫ x, (1 / 16) * ((BB x) ^ 2 * wt x) ∂μ) := by
              rw [← integral_add h12 hT3]
      _ = (∫ x, (9 / 2) * ((FF x) ^ 2 * WW x) ∂μ) + (∫ x, (1 / 2) * ((SS x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / 16) * ((BB x) ^ 2 * wt x) ∂μ) := by
              rw [integral_add hF5 hT2]
      _ = (9 / 2) * (∫ x, (FF x) ^ 2 * WW x ∂μ) + (1 / 2) * (∫ x, (SS x) ^ 2 * WW x ∂μ)
          + (1 / 16) * (∫ x, (BB x) ^ 2 * wt x ∂μ) := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
  calc
    |∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ v (x i) (x j)|
        ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ v (x i) (x j))| := hL1
    _ ≤ ∫ x in abox N ℓ,
        ((9 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 16) * ((BB x) ^ 2 * wt x)) := hL2
    _ = (9 / 2) * (∫ x : X N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : X N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 16) * (∫ x : X N, (BB x) ^ 2 * wt x ∂μ) := by
          simpa [μ] using hL3
    _ = (9 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ v (x i) (x j)|))
        + (1 / 16) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
          simp [μ, FF, QQ, SS, BB, WW, wt, mul_assoc, add_assoc]


theorem qcross_w_d2_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ v (x p.1) (x p.2)| ≤
      qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  have hvi : MeasureTheory.Integrable v := (memLp_one_iff_integrable.mp hv_memL1)
  have hvs : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    v_eq_zero_of_norm_ge (h := hv_supp) hz
  have heven : ∀ z : ℝ³, v (-z) = v z := fun z => radial_neg hvrad z
  have hIv0 : 0 ≤ ∫ z : ℝ³, v z := by
    exact integral_nonneg (μ := (volume : Measure ℝ³)) (fun z => hv_nonneg z)
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ v (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ v (x p.1) (x p.2)|)
      ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((5 / 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ v (x p.1) (x p.2)|)
              + (1 / 8) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_w_d2_pair_quarter hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := by
            simp [mA, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ v (x p.1) (x p.2)| ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4word (N := N) ℓ
          (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    calc
      |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)|
          ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)| := by
              simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                  wPairC ℓ v (x p.1) (x p.2)))
      _ ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := hsum_le
      _ = (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rw [hq4]
          ring
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ v (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          simpa [wPairC] using (sq3_mass_pair_le hℓ hvi hvs hRℓ
            (a := fun x => aP ℓ p.2 (aP ℓ p.1 Φ) x)
            (hac := aP_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
            (b := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
            (hbc := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
            (c := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
            (hcc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)) hne)
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  
  have hC1nn : 0 ≤ C1 := by
    dsimp [C1]
    positivity
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hM : C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≥ 0 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1nn hLinv) (sq_nonneg (N : ℝ))) hJ0
  have hmA : mA ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
      masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      mA = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mA, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := hmm
      _ = C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            rw [pairSum_A_eq]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cS1 ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (cS2_le_n_mul_cS1 hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG2 : mG2 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
      masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      mG2 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mG2, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_Q_swap_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG3 : mG3 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_aQ_comm hℓ hne hΦc x]
    calc
      mG3 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mG3, wPairC]
      _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := hEq
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hC1le : 7 * C1 ≤ qcrossC * (∫ z : ℝ³, v z) := by
    dsimp [C1, qcrossC]
    have hpos : 0 ≤ chiSup ^ 2 * (∫ z : ℝ³, v z) := by
      exact mul_nonneg (sq_nonneg chiSup) hIv0
    have h14 : (14 : ℝ) ≤ (1000000 * 8 * π : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have hmul : (14 : ℝ) * (chiSup ^ 2 * (∫ z : ℝ³, v z))
        ≤ (1000000 * 8 * π) * (chiSup ^ 2 * (∫ z : ℝ³, v z)) :=
      mul_le_mul_of_nonneg_right h14 hpos
    nlinarith [hmul]
  have hX0 : 0 ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ := by positivity
  have hMainAbs : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ v (x p.1) (x p.2)| ≤
      7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    let M : ℝ := C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
    have hD' : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ v (x p.1) (x p.2)| ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4 := by
      simpa [q4] using hD
    calc
      |∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ v (x p.1) (x p.2)| ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4 := hD'
      _ ≤ 7 * M + (1 / 4) * q4 := by
            nlinarith [hSsplit, hmA, hmG2, hmG3]
      _ = 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J + (1 / 4) * q4 := by
            dsimp [M]
            ring
      _ = 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hAbs : 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≤
      qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    have h1 : 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
      calc
        7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2
            = (7 * C1) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by ring
        _ ≤ (qcrossC * (∫ z : ℝ³, v z)) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by
            exact mul_le_mul_of_nonneg_right hC1le hX0
        _ = qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
            rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hJ0
  calc
    |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ v (x p.1) (x p.2)|
        ≤ 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hMainAbs
    _ ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hAbs]
    _ = qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rfl


theorem qcross_w_d13_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤
      qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  have hvi : MeasureTheory.Integrable v := (memLp_one_iff_integrable.mp hv_memL1)
  have hvs : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    v_eq_zero_of_norm_ge (h := hv_supp) hz
  have heven : ∀ z : ℝ³, v (-z) = v z := fun z => radial_neg hvrad z
  have hIv0 : 0 ≤ ∫ z : ℝ³, v z := by
    exact integral_nonneg (μ := (volume : Measure ℝ³)) (fun z => hv_nonneg z)
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ v (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  let mG : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ v (x p.1) (x p.2)|)
      ≤ (9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((9 / 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ v (x p.1) (x p.2)|)
              + (1 / 16) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_w_d13_pair_quarter hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ := by
            simp [mG, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤
      9 * mG + mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    have hq4' : (1 / 2) * mQ = q4 := by
      dsimp [q4]
      rw [hq4]
      ring
    have h1 : |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤ 2 * ((9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ) := by
      calc
        |q3word (N := N) ℓ (wPairC ℓ v) Φ|
            = |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2))| := by
                rfl
        _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)|) := by
                have habs := Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                  ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2))
                have h2 : (0 : ℝ) ≤ 2 := by norm_num
                calc
                  |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2))|
                      = 2 * |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)| := by
                          rw [abs_mul, abs_of_nonneg h2]
                  _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ v (x p.1) (x p.2)|) := by
                          exact mul_le_mul_of_nonneg_left habs h2
        _ ≤ 2 * ((9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ) := by
                exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    calc
      |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤ 2 * ((9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ) := h1
      _ = 9 * mG + mS + (1 / 8) * mQ := by ring
      _ = 9 * mG + mS + (1 / 4) * q4 := by
            rw [← hq4']
            ring
      _ = 9 * mG + mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ v (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          simpa [wPairC] using (sq3_mass_pair_le hℓ hvi hvs hRℓ
            (a := fun x => aP ℓ p.2 (aP ℓ p.1 Φ) x)
            (hac := aP_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
            (b := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
            (hbc := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
            (c := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
            (hcc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)) hne)
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ v (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hC1nn : 0 ≤ C1 := by
    dsimp [C1]
    positivity
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmA : mA ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
      masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      mA = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mA, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := hmm
      _ = C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            rw [pairSum_A_eq]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cS1 ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (cS2_le_n_mul_cS1 hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG2 : mG2 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
      masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      mG2 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mG2, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_Q_swap_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG3 : mG3 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_aQ_comm hℓ hne hΦc x]
    calc
      mG3 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mG3, wPairC]
      _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := hEq
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG : mG ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
        (C := C1) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      mG = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [mG, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hC1le : (18 : ℝ) * C1 ≤ qcrossC * (∫ z : ℝ³, v z) := by
    dsimp [C1, qcrossC]
    have hpos : 0 ≤ chiSup ^ 2 * (∫ z : ℝ³, v z) := by
      exact mul_nonneg (sq_nonneg chiSup) hIv0
    have h36 : (36 : ℝ) ≤ (1000000 * 8 * π : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have hmul : (36 : ℝ) * (chiSup ^ 2 * (∫ z : ℝ³, v z))
        ≤ (1000000 * 8 * π) * (chiSup ^ 2 * (∫ z : ℝ³, v z)) :=
      mul_le_mul_of_nonneg_right h36 hpos
    nlinarith [hmul]
  have hX0 : 0 ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ := by positivity
  have hMain : |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤
      (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    let M : ℝ := C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
    have hD' : |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤ 9 * mG + mS + (1 / 4) * q4 := by
      simpa [q4] using hD
    calc
      |q3word (N := N) ℓ (wPairC ℓ v) Φ| ≤ 9 * mG + mS + (1 / 4) * q4 := hD'
      _ ≤ 18 * M + (1 / 4) * q4 := by
            nlinarith [hSsplit, hmA, hmG2, hmG3, hmG]
      _ = (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J + (1 / 4) * q4 := by
            dsimp [M]
            ring
      _ = (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hAbs : (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≤
      qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    have h1 : (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
      calc
        (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2
            = ((18 : ℝ) * C1) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by ring
        _ ≤ (qcrossC * (∫ z : ℝ³, v z)) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by
            exact mul_le_mul_of_nonneg_right hC1le hX0
        _ = qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
            rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hJ0
  calc
    |q3word (N := N) ℓ (wPairC ℓ v) Φ|
        ≤ (18 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hMain
    _ ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hAbs]
    _ = qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rfl


/-- Cross part of the one-body mass at the ACTUAL kernel `w := wPairC v`,
per particle (the q1-type `w`-cross atom): with `C0v := chiSup²·2·(∫v)`,
`|∫(PᵢΦ)(QᵢΦ)·fibre(xᵢ)| ≤ (C0v/2)·(‖PᵢΦ‖² + ‖QᵢΦ‖²)`.  Mirror of
`OneBodyCross.onebody_cross_per` (g0-kernel) with the fibre bound from
`vabs_fibre_acube_abs_le` and `|wPair(v)| = wPair(v)` pointwise
(`wPairC_nonneg hv_nonneg`); no scattering branch needed. -/
lemma onebody_cross_w_per {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvi : MeasureTheory.Integrable v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))|
      ≤ (1 / 2) * (chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)) *
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
  classical
  let F : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ v) z
  let C0 : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  have hIv0 : 0 ≤ ∫ z : ℝ³, v z := by
    exact integral_nonneg (μ := (volume : Measure ℝ³)) (fun z => hv_nonneg z)
  have hC0nn : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) hIv0
  have hfib : ∀ z : ℝ³, |F z| ≤ C0 := by
    intro z
    dsimp [F, C0]
    have hb := vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ z
    have hEq : (∫ y in acube ℓ, wPairC ℓ v z y) = ∫ y in acube ℓ, |wPair ℓ v z y| := by
      apply integral_congr_ae
      filter_upwards with y
      have hw0 : 0 ≤ wPairC ℓ v z y := wPairC_nonneg hv_nonneg ℓ z y
      simpa [wPairC] using (abs_of_nonneg hw0).symm
    rw [w1Fibre, hEq]
    exact hb
  have hFm : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
    dsimp [F]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := v) hvi
    simpa [w1Fibre, wPairC] using hfac
  have hPc : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hQc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPQc : Continuous (fun x : X N => (aP ℓ i Φ x) * (aQ ℓ i Φ x)) := hPc.mul hQc
  let g : X N → ℝ := fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i)
  let b : X N → ℝ := fun x => (1 / 2) * ((aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2)
  -- integrability (exact, NO `simpa [IntegrableOn]`)
  have hgI : Integrable g μ := by
    have hh : IntegrableOn (fun x : X N =>
        (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i)) (abox N ℓ) volume :=
      integrableOn_slot_fibre hℓ i hFm (fun z hz => by
        have hb := hfib z
        simpa [C0] using hb) hPQc
    exact hh
  have hP2i : Integrable (fun x : X N => (aP ℓ i Φ x) ^ 2) μ := by
    exact integrableOn_abox_of_continuous hℓ (hPc.pow 2)
  have hQ2i : Integrable (fun x : X N => (aQ ℓ i Φ x) ^ 2) μ := by
    exact integrableOn_abox_of_continuous hℓ (hQc.pow 2)
  have hbI : Integrable b μ := by
    have hsum : Integrable (fun x : X N => (aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) μ := hP2i.add hQ2i
    exact hsum.const_mul (1 / 2)
  have hC0bI : Integrable (fun x : X N => C0 * b x) μ := hbI.const_mul C0
  -- |g x| ≤ C0 · b x pointwise (fibre bound + AM–GM)
  have hgb : ∀ x : X N, |g x| ≤ C0 * b x := by
    intro x
    have hF : |F (x i)| ≤ C0 := hfib (x i)
    have ham : |(aP ℓ i Φ x) * (aQ ℓ i Φ x)| ≤
        (1 / 2) * ((aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) := by
      calc
        |(aP ℓ i Φ x) * (aQ ℓ i Φ x)| = |aP ℓ i Φ x| * |aQ ℓ i Φ x| := by rw [abs_mul]
        _ ≤ (1 / 2) * (aP ℓ i Φ x) ^ 2 + (1 / 2) * (aQ ℓ i Φ x) ^ 2 :=
                abs_mul_le_half_sq_sq (aP ℓ i Φ x) (aQ ℓ i Φ x)
        _ = (1 / 2) * ((aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) := by ring
    calc
      |g x| = |(aP ℓ i Φ x) * (aQ ℓ i Φ x)| * |F (x i)| := by
              dsimp [g, F]
              rw [abs_mul, abs_mul]
      _ ≤ |(aP ℓ i Φ x) * (aQ ℓ i Φ x)| * C0 := by
              exact mul_le_mul_of_nonneg_left hF (abs_nonneg _)
      _ ≤ b x * C0 := by
              dsimp [b]
              exact mul_le_mul_of_nonneg_right ham hC0nn
      _ = C0 * b x := by ring
  have h1 : |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ :=
    abs_integral_le_integral_abs (μ := μ) (f := g)
  have h2 : (∫ x, |g x| ∂μ) ≤ ∫ x, C0 * b x ∂μ :=
    integral_mono_ae (μ := μ) hgI.abs hC0bI (by filter_upwards with x; exact hgb x)
  have hbE : (∫ x, b x ∂μ)
      = (1 / 2) * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
    calc
      (∫ x, b x ∂μ)
          = ∫ x in abox N ℓ, (1 / 2) * ((aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) := by
              dsimp [b, μ]
      _ = (1 / 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) := by
              rw [integral_const_mul]
      _ = (1 / 2) * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
              congr 1
              calc
                (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2)
                    = ∫ x, ((fun x => (aP ℓ i Φ x) ^ 2) + (fun x => (aQ ℓ i Φ x) ^ 2)) x ∂μ := by
                        dsimp [μ]
                _ = (∫ x, (fun x => (aP ℓ i Φ x) ^ 2) x ∂μ)
                    + (∫ x, (fun x => (aQ ℓ i Φ x) ^ 2) x ∂μ) := by
                        exact integral_add hP2i hQ2i
                _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
                        dsimp [μ]
  calc
    |∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))|
        = |∫ x, g x ∂μ| := by
            dsimp [g, F, μ]
    _ ≤ ∫ x, |g x| ∂μ := h1
    _ ≤ ∫ x, C0 * b x ∂μ := h2
    _ = C0 * (∫ x, b x ∂μ) := by rw [integral_const_mul]
    _ = C0 * ((1 / 2) * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2))) := by
            rw [hbE]
    _ = (1 / 2) * C0 *
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by ring
    _ = (1 / 2) * (chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)) *
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
            dsimp [C0]

/-- Cross part of the one-body mass at the ACTUAL kernel `w := wPairC v`
(summed): `|cross| ≤ (C0v/2)·(cS1+cnPlus)`, `C0v := chiSup²·2·(∫v)`. -/
lemma onebody_cross_w_sum_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvi : MeasureTheory.Integrable v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))|
      ≤ (1 / 2) * (chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
  classical
  let C0 : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)
  have hper : ∀ i : Fin N,
      |∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))|
        ≤ (1 / 2) * C0 *
            ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
    intro i
    simpa [C0] using
      (onebody_cross_w_per hℓ hv_nonneg hvi hR hv_supp hRℓ i hΦc)
  calc
    |∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))|
        ≤ ∑ i : Fin N, |∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun i : Fin N => ∫ x in abox N ℓ,
                (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))))
    _ ≤ ∑ i : Fin N, (1 / 2) * C0 *
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
          exact Finset.sum_le_sum (fun i hi => hper i)
    _ = (1 / 2) * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib]
          dsimp [cS1, cnPlus]
    _ = (1 / 2) * (chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
          dsimp [C0]



/-- Summed `w := wPairC v` version of the q1 cross bound (eq:dvapriori
Q1/Q2-form): with BOTH kernels of `q1word` equal to the ACTUAL pair kernel
`w := wPairC v` (FS eq:dvapriori's `Σ(Q_jP_i w P_iP_j+h.c.)` pair term and
`μΣ(P∫w Q+h.c.)` one-body term; the `+h.c.` doubling is the factor 2 inside
`q1word`),
`|q1word(N,ℓ,μ, wPairC v, wPairC v) Φ| ≤ qcrossC·(∫v)·Xbig·J`,
`Xbig := N̂²/ℓ³ + μ²ℓ³` — the corpus word-form mirror of
`QCrossD.qcross_d11` with `g0,g2 ↦ v`, `8πa ↦ ∫v` (closes
`APrioriBounds.q1word_w_bound_statement`).  Proof: q1 decomposes into its
pair part `2·T1` and one-body part `-2μ·T2`; `|T1| ≤ ½M1+½M2` via the generic
`q1pair_abs_le (h := v)`; `|2μT2| ≤ μ·C0·N̂·J` via
`onebody_cross_w_sum_abs_le` (kernel `v`, constant `C0 := chiSup²·2·∫v`) and
`cS1+cnPlus = N̂J`; mass tails `M1,M2 ≤ C2·(ℓ³)⁻¹·N̂²·J`, `C2 := chiSup²·2·∫v`
via `masssum_PP_abs_le`/`masssum_PQ_abs_le (h := v)`; tail absorption
`2·N̂²(ℓ³)⁻¹+μN̂ ≤ (5/2)·Xbig` and `5·chiSup² ≤ qcrossC·…/…` arithmetic with
`nlinarith [Real.pi_gt_three]`. -/
theorem qcross_w_d11 {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |q1word (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ v) Φ| ≤
      qcrossC * (∫ z : ℝ³, v z) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  have hvi : MeasureTheory.Integrable v := (memLp_one_iff_integrable.mp hv_memL1)
  have hvs : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    v_eq_zero_of_norm_ge (h := hv_supp) hz
  have heven : ∀ z : ℝ³, v (-z) = v z := fun z => radial_neg hvrad z
  have hIv0 : 0 ≤ ∫ z : ℝ³, v z := by
    exact integral_nonneg (μ := (volume : Measure ℝ³)) (fun z => hv_nonneg z)
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC ℓ v
  let w2 : ℝ³ → ℝ³ → ℝ := wPairC ℓ v
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let Xbig : ℝ := (N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3
  let M1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |w2 (x p.1) (x p.2)|
  let M2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |w2 (x p.1) (x p.2)|
  let T1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2)
  let T2 : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ w1 (x i))
  let S : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ w1 (x i)) * (aQ ℓ i Φ x)
  let C0 : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)
  let C2 : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hX0 : 0 ≤ Xbig := by
    have h1 : 0 ≤ (N : ℝ) ^ 2 / ℓ ^ 3 := by positivity
    have h2 : 0 ≤ μ ^ 2 * ℓ ^ 3 := by positivity
    dsimp [Xbig]
    nlinarith
  have hC0nn : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) hIv0
  have hC2nn : 0 ≤ C2 := by
    dsimp [C2]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) hIv0
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  -- decomposition of q1word into pair part and one-body part
  have hq1eq : q1word (N := N) ℓ μ w1 w2 Φ = 2 * T1 - 2 * μ * T2 := by
    dsimp [q1word, T1, T2, w1, w2]
  have hB1 : |q1word (N := N) ℓ μ w1 w2 Φ| ≤ 2 * |T1| + |2 * μ * T2| := by
    rw [hq1eq]
    calc
      |2 * T1 - 2 * μ * T2| = |2 * T1 + (-(2 * μ * T2))| := by rw [sub_eq_add_neg]
      _ ≤ |2 * T1| + |-(2 * μ * T2)| := abs_add_le (2 * T1) (-(2 * μ * T2))
      _ = |2 * T1| + |2 * μ * T2| := by rw [abs_neg]
      _ = 2 * |T1| + |2 * μ * T2| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  -- pair part: |T1| ≤ ½M1 + ½M2
  have hpair : |T1| ≤ (1 / 2) * M1 + (1 / 2) * M2 := by
    have hh := q1pair_abs_le hℓ (h := v) hvi hvs hRℓ hΦc
    simpa [T1, M1, M2, w2, wPairC] using hh
  have hpairb : 2 * |T1| ≤ M1 + M2 := by
    calc
      2 * |T1| ≤ 2 * ((1 / 2) * M1 + (1 / 2) * M2) :=
            mul_le_mul_of_nonneg_left hpair (by norm_num)
      _ = M1 + M2 := by ring
  -- one-body part: |2·μ·T2| ≤ μ·C0·N̂·J
  have hTS : T2 = S := by
    dsimp [T2, S]
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    filter_upwards with x
    dsimp [w1]
    ring
  have hob : |2 * μ * T2| ≤ μ * C0 * (N : ℝ) * J := by
    have hcross := onebody_cross_w_sum_abs_le (N := N) hℓ hv_nonneg hvi hR hv_supp hRℓ hΦc
    have hSabs : |S| ≤ (1 / 2) * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
      calc
        |S| = |∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ v) (x i))| := by
              apply congrArg abs
              dsimp [S, w1]
              apply Finset.sum_congr rfl
              intro i hi
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ ≤ (1 / 2) * (chiSup ^ 2 * 2 * (∫ z : ℝ³, v z)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
              simpa [C0] using hcross
        _ = (1 / 2) * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
              dsimp [C0]
    have h2S : |2 * μ * S| ≤ μ * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
      calc
        |2 * μ * S| = 2 * μ * |S| := by
              rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμ)]
        _ ≤ 2 * μ * ((1 / 2) * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ)) := by
              exact mul_le_mul_of_nonneg_left hSabs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμ)
        _ = μ * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by ring
    have h : |2 * μ * S| ≤ μ * C0 * (N : ℝ) * J := by
      calc
        |2 * μ * S| ≤ μ * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := h2S
        _ = μ * C0 * (cnPlus ℓ Φ + cS1 ℓ Φ) := by ring
        _ = μ * C0 * (N : ℝ) * J := by
              rw [cnPlus_add_cS1 hℓ hΦc]
              dsimp [J]
              ring
    rw [hTS]
    exact h
  -- mass bounds for the two families
  have hm2 : M2 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm := masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
      (C := C2) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      M2 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [M2, w2, wPairC]
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := hmm
      _ = C2 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            rw [pairSum_A_eq]
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cS1 ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (cS2_le_n_mul_cS1 hℓ hΦc) (mul_nonneg hC2nn hLinv)
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2nn hLinv)
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
      _ = C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hm1 : M1 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm := masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ hvi hvs heven
      (C := C2) (fun x => vabs_fibre_acube_abs_le hR hv_nonneg hvi hv_supp hℓ hRℓ x) hΦc
    calc
      M1 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
            simp [M1, w2, wPairC]
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC2nn hLinv)
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  -- assemble: |q1word| ≤ (M1+M2) + μ·C0·N̂·J
  have hc1 : 2 * |T1| + |2 * μ * T2| ≤ (M1 + M2) + μ * C0 * (N : ℝ) * J := by
    nlinarith [hpairb, hob]
  have hc2 : (M1 + M2) + μ * C0 * (N : ℝ) * J ≤
      (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J := by
    nlinarith [hm1, hm2]
  -- expand the constants: C0 = C2 = chiSup²·2·∫v
  have hconst :
      (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J =
        (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J *
          (2 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + μ * (N : ℝ)) := by
    dsimp [C0, C2]
    ring
  -- G := 2·N̂²·(ℓ³)⁻¹ + μ·N̂ ≤ (5/2)·Xbig ; the N̂²-term and μ-term bounds
  have hN2inv : (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ ≤ Xbig := by
    have hmu2 : 0 ≤ μ ^ 2 * ℓ ^ 3 := by positivity
    have h : (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ + μ ^ 2 * ℓ ^ 3 := by
      linarith
    dsimp [Xbig]
    rw [div_eq_mul_inv]
    exact h
  -- the linear-μ term: μ·N̂ ≤ ½·Xbig (AM–GM, cf. qcross_d11)
  have hℓ3 : 0 < ℓ ^ 3 := pow_pos hℓ 3
  have hℓ3nz : ℓ ^ 3 ≠ 0 := ne_of_gt hℓ3
  have hmain : 2 * μ * (N : ℝ) * ℓ ^ 3 ≤ μ ^ 2 * ℓ ^ 6 + (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (μ * ℓ ^ 3 - (N : ℝ))]
  have h2muN : 2 * μ * (N : ℝ) ≤ μ ^ 2 * ℓ ^ 3 + (N : ℝ) ^ 2 / ℓ ^ 3 := by
    calc
      2 * μ * (N : ℝ) ≤ (μ ^ 2 * ℓ ^ 6 + (N : ℝ) ^ 2) * (ℓ ^ 3)⁻¹ := by
        calc
          2 * μ * (N : ℝ) = (2 * μ * (N : ℝ) * ℓ ^ 3) * (ℓ ^ 3)⁻¹ := by
            field_simp [hℓ3nz]
          _ ≤ (μ ^ 2 * ℓ ^ 6 + (N : ℝ) ^ 2) * (ℓ ^ 3)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hℓ3.le)
      _ = μ ^ 2 * ℓ ^ 3 + (N : ℝ) ^ 2 / ℓ ^ 3 := by
        field_simp [hℓ3nz]
  have hmuN : μ * (N : ℝ) ≤ (1 / 2) * Xbig := by
    dsimp [Xbig]
    nlinarith
  have hGle : 2 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + μ * (N : ℝ) ≤ (5 / 2) * Xbig := by
    have h1 : 2 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) ≤ 2 * Xbig := by
      exact mul_le_mul_of_nonneg_left hN2inv (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : μ * (N : ℝ) ≤ (1 / 2) * Xbig := hmuN
    nlinarith
  have hFnn : 0 ≤ (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J := by
    have h1 : 0 ≤ (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) :=
      mul_nonneg hIv0 (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2))
    exact mul_nonneg h1 hJ
  have hBmid :
      (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J * (2 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + μ * (N : ℝ))
        ≤ (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J * ((5 / 2) * Xbig) := by
    exact mul_le_mul_of_nonneg_left hGle hFnn
  -- final absorption: 5·(chiSup²·∫v·Xbig·J) ≤ qcrossC·(∫v)·Xbig·J
  have hBtarget :
      (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J * ((5 / 2) * Xbig) ≤
        qcrossC * (∫ z : ℝ³, v z) * Xbig * J := by
    have hW : 0 ≤ chiSup ^ 2 * (∫ z : ℝ³, v z) * Xbig * J := by
      have h1 : 0 ≤ chiSup ^ 2 * (∫ z : ℝ³, v z) := mul_nonneg (sq_nonneg chiSup) hIv0
      have h2 : 0 ≤ chiSup ^ 2 * (∫ z : ℝ³, v z) * Xbig := mul_nonneg h1 hX0
      exact mul_nonneg h2 hJ
    have h5 : (5 : ℝ) ≤ 1000000 * 8 * π := by
      nlinarith [Real.pi_gt_three]
    calc
      (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J * ((5 / 2) * Xbig)
          = (5 : ℝ) * (chiSup ^ 2 * (∫ z : ℝ³, v z) * Xbig * J) := by ring
      _ ≤ (1000000 * 8 * π) * (chiSup ^ 2 * (∫ z : ℝ³, v z) * Xbig * J) := by
            exact mul_le_mul_of_nonneg_right h5 hW
      _ = qcrossC * (∫ z : ℝ³, v z) * Xbig * J := by
            dsimp [qcrossC]
            ring
  -- assemble the whole chain
  calc
    |q1word (N := N) ℓ μ w1 w2 Φ| ≤ 2 * |T1| + |2 * μ * T2| := hB1
    _ ≤ (M1 + M2) + μ * C0 * (N : ℝ) * J := hc1
    _ ≤ (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J := hc2
    _ = (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J *
          (2 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + μ * (N : ℝ)) := hconst
    _ ≤ (∫ z : ℝ³, v z) * (chiSup ^ 2 * 2) * J * ((5 / 2) * Xbig) := hBmid
    _ ≤ qcrossC * (∫ z : ℝ³, v z) * Xbig * J := hBtarget
    _ = qcrossC * (∫ z : ℝ³, v z) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
          dsimp [Xbig, J]



/-- Mass bridge used by the eq:dvapriori post-window conversion
(`q4word ≤ Cμ²aℓ³` ↦ `≤ Cμ²ℓ³∫v`): the full potential integrates to at least
the g₀-mass, `8π·(a v) ≤ ∫v`, since `g₀ = v(1−ω₀)` with `0 ≤ ω₀ ≤ 1` a.e.
and `v ≥ 0` pointwise (`∫g₀ = 8πa` + a.e. `g₀ ≤ v`). -/
lemma integral_v_ge_eight_pi_av {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    8 * π * a v ≤ ∫ z : ℝ³, v z := by
  have hvi : MeasureTheory.Integrable v := (memLp_one_iff_integrable.mp hv_memL1)
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hle_ae : (fun z : ℝ³ => g0 v h z) ≤ᵐ[volume] v := by
    have hg0v : ∀ᵐ z : ℝ³, |g0 v h z| ≤ v z :=
      g0_abs_le_v_ae hR hv_nonneg hvrad hv_supp h
    have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
    filter_upwards [hg0v, hnn] with z hzle hznn
    calc
      g0 v h z ≤ |g0 v h z| := le_abs_self _
      _ ≤ v z := hzle
  calc
    8 * π * a v = ∫ z : ℝ³, g0 v h z := (g0_integral hR hv_supp h).symm
    _ ≤ ∫ z : ℝ³, v z := integral_mono_ae (μ := (volume : Measure ℝ³)) hg0i hvi hle_ae


/-- **Post-window final eq:dvapriori form (bookkeeping)** — at the NORMALIZED
level `J := ∫Φ² = 1`, given the a-priori WINDOW `|N̂/ℓ³ − μ| ≤ μδ` (`δ ≤ 1`)
and the q4-CONCENTRATION `q4word ≤ Cq·μ²aℓ³` (both are exactly the
eq:apriorinn+ / eq:Q4apriori outputs of thm:aprioribounds, here assumed),
the three `w := wPairC v` words are each bounded by
`(6·qcrossC + Cq)·(μ²ℓ³·∫v)` — the corpus per-sector form of FS eq:dvapriori
(with `∫v` replacing `a`, using `8πa ≤ ∫v`).  Steps: the window gives
`Xbig := N̂²/ℓ³ + μ²ℓ³ ≤ 5μ²ℓ³` (`δ ≤ 1`), so q1 ≤ qcrossC·∫v·Xbig ≤
5qcrossC·(μ²ℓ³∫v); q3/T₄ ≤ qcrossC·∫v·N̂²/ℓ³ + ¼q4word ≤
5qcrossC·(μ²ℓ³∫v) + Cq·(μ²ℓ³∫v) (¼q4word ≤ q4word by q4_nonneg, then hq4,
then `a ≤ ∫v/(8π)` via `integral_v_ge_eight_pi_av`); absorbed into one
universal constant.  All `coefficient·(μ²ℓ³∫v)` inequalities are handled with
the common nonneg factor `M0 := μ²ℓ³·∫v` (`mul_le_mul_of_nonneg_right`). -/
lemma eq_dva_priori_final_of_window {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    {δ Cq : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hCq : 0 ≤ Cq)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hJ1 : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    (hwin : |((N : ℝ) / ℓ ^ 3) - μ| ≤ μ * δ)
    (hq4 : q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        ≤ Cq * μ ^ 2 * (a v) * ℓ ^ 3) :
    (|q1word (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ v) Φ|
        ≤ (6 * qcrossC + Cq) * (μ ^ 2 * ℓ ^ 3 * (∫ z : ℝ³, v z)))
      ∧ (|q3word (N := N) ℓ (wPairC ℓ v) Φ|
        ≤ (6 * qcrossC + Cq) * (μ ^ 2 * ℓ ^ 3 * (∫ z : ℝ³, v z)))
      ∧ (|∑ p ∈ pairSet N,
            ∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                wPairC ℓ v (x p.1) (x p.2)|
        ≤ (6 * qcrossC + Cq) * (μ ^ 2 * ℓ ^ 3 * (∫ z : ℝ³, v z))) := by
  classical
  let Xbig : ℝ := (N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3
  let M0 : ℝ := μ ^ 2 * ℓ ^ 3 * (∫ z : ℝ³, v z)
  let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
  have hIv0 : 0 ≤ ∫ z : ℝ³, v z := by
    exact integral_nonneg (μ := (volume : Measure ℝ³)) (fun z => hv_nonneg z)
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hq0 : 0 ≤ qcrossC := by
    dsimp [qcrossC]
    positivity
  have hℓ3nz : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  have hℓ3nn : 0 ≤ ℓ ^ 3 := pow_nonneg hℓ.le 3
  have hM0 : 0 ≤ M0 := by
    dsimp [M0]
    exact mul_nonneg (mul_nonneg (sq_nonneg μ) hℓ3nn) hIv0
  have hc : (5 * qcrossC + Cq) * M0 ≤ (6 * qcrossC + Cq) * M0 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [hq0]) hM0
  -- window ⟹ Xbig ≤ 5μ²ℓ³
  have hxnn : 0 ≤ (N : ℝ) / ℓ ^ 3 := div_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) hℓ3nn
  have hx : (N : ℝ) / ℓ ^ 3 ≤ μ * (1 + δ) := by
    have hsub : (N : ℝ) / ℓ ^ 3 - μ ≤ μ * δ := le_trans (le_abs_self ((N : ℝ) / ℓ ^ 3 - μ)) hwin
    nlinarith
  have hmu1nn : 0 ≤ μ * (1 + δ) := mul_nonneg hμ.le (by nlinarith)
  have hsq : ((N : ℝ) / ℓ ^ 3) ^ 2 ≤ (μ * (1 + δ)) ^ 2 := by
    exact sq_le_sq.mpr (by rw [abs_of_nonneg hxnn, abs_of_nonneg hmu1nn]; exact hx)
  have hN2L : (N : ℝ) ^ 2 / ℓ ^ 3 ≤ μ ^ 2 * (1 + δ) ^ 2 * ℓ ^ 3 := by
    have hstep : (N : ℝ) ^ 2 / ℓ ^ 3 = ((N : ℝ) / ℓ ^ 3) ^ 2 * ℓ ^ 3 := by
      field_simp [hℓ3nz]
    rw [hstep]
    calc
      ((N : ℝ) / ℓ ^ 3) ^ 2 * ℓ ^ 3
          ≤ (μ * (1 + δ)) ^ 2 * ℓ ^ 3 := mul_le_mul_of_nonneg_right hsq hℓ3nn
      _ = μ ^ 2 * (1 + δ) ^ 2 * ℓ ^ 3 := by ring
  have h14 : (1 + δ) ^ 2 ≤ 4 := by
    have hf : 0 ≤ (1 - δ) * (3 + δ) :=
      mul_nonneg (sub_nonneg.mpr hδ1) (by nlinarith [hδ0])
    nlinarith [hf]
  have hN2L4 : (N : ℝ) ^ 2 / ℓ ^ 3 ≤ 4 * μ ^ 2 * ℓ ^ 3 := by
    calc
      (N : ℝ) ^ 2 / ℓ ^ 3 ≤ μ ^ 2 * (1 + δ) ^ 2 * ℓ ^ 3 := hN2L
      _ = (μ ^ 2 * ℓ ^ 3) * (1 + δ) ^ 2 := by ring
      _ ≤ (μ ^ 2 * ℓ ^ 3) * 4 := mul_le_mul_of_nonneg_left h14 (mul_nonneg (sq_nonneg μ) hℓ3nn)
      _ = 4 * μ ^ 2 * ℓ ^ 3 := by ring
  have hXbig : Xbig ≤ 5 * μ ^ 2 * ℓ ^ 3 := by
    calc
      Xbig = (N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3 := rfl
      _ ≤ 4 * μ ^ 2 * ℓ ^ 3 + μ ^ 2 * ℓ ^ 3 := by
            exact add_le_add_left hN2L4 (μ ^ 2 * ℓ ^ 3)
      _ = 5 * μ ^ 2 * ℓ ^ 3 := by ring
  have hN2X : (N : ℝ) ^ 2 / ℓ ^ 3 ≤ Xbig := by
    dsimp [Xbig]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg μ) hℓ3nn)
  -- ¼q4word ≤ Cq·M0 (hq4 + q4_nonneg + a ≤ ∫v/(8π))
  have hq4nn : 0 ≤ q4 := by
    dsimp [q4]
    exact q4_nonneg (N := N) hℓ (wPairC_nonneg hv_nonneg ℓ)
  have hq4le : (1 / 4) * q4 ≤ Cq * M0 := by
    have hCqMa : 0 ≤ Cq * μ ^ 2 * (a v) * ℓ ^ 3 := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hCq (sq_nonneg μ)) hav) hℓ3nn
    have hq4a : (1 / 4) * q4 ≤ (1 / 4) * (Cq * μ ^ 2 * (a v) * ℓ ^ 3) := by
      dsimp [q4]
      exact mul_le_mul_of_nonneg_left hq4 (by norm_num)
    have hq4b : (1 / 4) * (Cq * μ ^ 2 * (a v) * ℓ ^ 3) ≤ Cq * μ ^ 2 * (a v) * ℓ ^ 3 := by
      nlinarith
    have hM : 0 ≤ Cq * μ ^ 2 * ℓ ^ 3 := by
      exact mul_nonneg (mul_nonneg hCq (sq_nonneg μ)) hℓ3nn
    have h8 : 1 ≤ 8 * π := by nlinarith [Real.pi_gt_three]
    have ha8 : a v ≤ 8 * π * (a v) := by
      calc
        a v = 1 * (a v) := by ring
        _ ≤ (8 * π) * (a v) := mul_le_mul_of_nonneg_right h8 hav
    have hIv : 8 * π * (a v) ≤ ∫ z : ℝ³, v z :=
      integral_v_ge_eight_pi_av hR hv_nonneg hvrad hv_memL1 hv_supp h
    calc
      (1 / 4) * q4 ≤ Cq * μ ^ 2 * (a v) * ℓ ^ 3 := le_trans hq4a hq4b
      _ = (Cq * μ ^ 2 * ℓ ^ 3) * (a v) := by ring
      _ ≤ (Cq * μ ^ 2 * ℓ ^ 3) * (8 * π * (a v)) := by
            exact mul_le_mul_of_nonneg_left ha8 hM
      _ ≤ (Cq * μ ^ 2 * ℓ ^ 3) * (∫ z : ℝ³, v z) := by
            exact mul_le_mul_of_nonneg_left hIv hM
      _ = Cq * M0 := by
            dsimp [M0]
            ring
  -- feed the three atoms
  have hq1 := qcross_w_d11 hℓ hμ.le hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hq3 := qcross_w_d13_quarter hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hT4 := qcross_w_d2_quarter hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hq1' : |q1word (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ v) Φ|
      ≤ qcrossC * (∫ z : ℝ³, v z) * Xbig := by
    simpa [hJ1, Xbig] using hq1
  have hq3' : |q3word (N := N) ℓ (wPairC ℓ v) Φ|
      ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) + (1 / 4) * q4 := by
    simpa [hJ1, q4] using hq3
  have hT4' : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ v (x p.1) (x p.2)|
      ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) + (1 / 4) * q4 := by
    simpa [hJ1, q4] using hT4
  -- the common chains
  have hq1b : |q1word (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ v) Φ| ≤ (5 * qcrossC) * M0 := by
    dsimp [M0]
    calc
      |q1word (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ v) Φ|
          ≤ qcrossC * (∫ z : ℝ³, v z) * Xbig := hq1'
      _ ≤ qcrossC * (∫ z : ℝ³, v z) * (5 * μ ^ 2 * ℓ ^ 3) := by
            exact mul_le_mul_of_nonneg_left hXbig (mul_nonneg hq0 hIv0)
      _ = (5 * qcrossC) * (μ ^ 2 * ℓ ^ 3 * (∫ z : ℝ³, v z)) := by ring
  have hb_chain {B : ℝ} (h : B ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) + (1 / 4) * q4) :
      B ≤ (6 * qcrossC + Cq) * M0 := by
    calc
      B ≤ qcrossC * (∫ z : ℝ³, v z) * ((N : ℝ) ^ 2 / ℓ ^ 3) + (1 / 4) * q4 := h
      _ ≤ qcrossC * (∫ z : ℝ³, v z) * (5 * μ ^ 2 * ℓ ^ 3) + (1 / 4) * q4 := by
            have hm := mul_le_mul_of_nonneg_left (le_trans hN2X hXbig) (mul_nonneg hq0 hIv0)
            nlinarith [hm]
      _ = (5 * qcrossC) * M0 + (1 / 4) * q4 := by
            dsimp [M0]
            ring
      _ ≤ (5 * qcrossC) * M0 + Cq * M0 := by
            exact add_le_add_right hq4le ((5 * qcrossC) * M0)
      _ = (5 * qcrossC + Cq) * M0 := by ring
      _ ≤ (6 * qcrossC + Cq) * M0 := hc
  refine ⟨?_, ?_, ?_⟩
  · calc
      |q1word (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ v) Φ|
          ≤ (5 * qcrossC) * M0 := hq1b
      _ ≤ (6 * qcrossC + Cq) * M0 := by
            have hm := mul_le_mul_of_nonneg_right (by nlinarith [hCq, hq0] : (5 * qcrossC : ℝ) ≤ 6 * qcrossC + Cq) hM0
            nlinarith [hm]
  · exact hb_chain hq3'
  · exact hb_chain hT4'

end BoseGases

end Submission
