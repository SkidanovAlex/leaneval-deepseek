import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.QCrossD
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `qcross_d2_pair_quarter` / `qcross_d2_quarter` — ¼-`q4word` variants of
`QCrossD.qcross_d2_pair` / `qcross_d2` (FS `eq:d2apriori` shape).
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

lemma qcross_d2_pair_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ (5 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ (g0 v h) (x i) (x j)|))
        + (1 / 8) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  let FF : XN N → ℝ := fun x => aP ℓ i (aP ℓ j Φ) x
  let QQ : XN N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : XN N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : XN N → ℝ := fun x => Classical.choose h (x i - x j)
  let WW : XN N → ℝ := fun x => |wPair ℓ (g0 v h) (x i) (x j)|
  let wt : XN N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let BB : XN N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  have hFc : Continuous FF := by
    dsimp [FF]
    exact aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : XN N => aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0supp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hF2W : Integrable (fun x : XN N => (FF x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : XN N => (FF x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := FF) hFc
    simpa [FF, WW, μ, IntegrableOn] using hs
  have hS2W : Integrable (fun x : XN N => (SS x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : XN N => (SS x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := SS) hSc
    simpa [SS, WW, μ, IntegrableOn] using hs
  have hB2wt : Integrable (fun x : XN N => (BB x) ^ 2 * wt x) μ := by
    have hs := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, wt, μ, IntegrableOn] using hs
  have hU : Integrable (fun x : XN N =>
      (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) μ := by
    have h1 : Integrable (fun x : XN N =>
        (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      (hF2W.const_mul (5 / 2)).add (hS2W.const_mul (1 / 2))
    refine (h1.add (hB2wt.const_mul (1 / 8))).congr ?_
    filter_upwards with x
    rfl
  have hWnn : ∀ x : XN N, 0 ≤ WW x := by
    intro x
    dsimp [WW]
    exact abs_nonneg _
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hWlewt : ∀ᵐ x ∂μ, WW x ≤ wt x := by
    dsimp [WW, wt, μ]
    simpa using (w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hmain : ∀ᵐ x ∂μ,
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
        ≤ (5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x) := by
    filter_upwards [homxb, hWlewt] with x homx1 hWle
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
        nlinarith [mul_le_mul_of_nonneg_left hWle (sq_nonneg (BB x))]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    calc
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
          = |FF x| * |QQ x * wPair ℓ (g0 v h) (x i) (x j)| := abs_mul _ _
      _ = |FF x| * (|QQ x| * |wPair ℓ (g0 v h) (x i) (x j)|) := by rw [abs_mul]
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
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := by
    have hEq : (fun x : XN N =>
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j))
        =ᵐ[μ] (fun x : XN N => FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))) := by
      refine ae_of_all _ (fun x => ?_)
      dsimp [FF, QQ]
      ring
    calc
      |∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
          = |∫ x : XN N, FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j)) ∂μ| := by
            congr 1
            rw [integral_congr_ae (μ := μ) hEq]
      _ ≤ ∫ x : XN N, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| ∂μ := by
            exact abs_integral_le_integral_abs (μ := μ)
  have hL2 : (∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|)
      ≤ ∫ x in abox N ℓ,
          ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) := by
    refine integral_mono_of_nonneg (μ := μ) ?_ hU ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hmain
  have hL3 : (∫ x : XN N,
          ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) ∂μ)
      = (5 / 2) * (∫ x : XN N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 8) * (∫ x : XN N, (BB x) ^ 2 * wt x ∂μ) := by
    have hF5 : Integrable (fun x : XN N => (5 / 2) * ((FF x) ^ 2 * WW x)) μ :=
      hF2W.const_mul (5 / 2)
    have hT2 : Integrable (fun x : XN N => (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hS2W.const_mul (1 / 2)
    have hT3 : Integrable (fun x : XN N => (1 / 8) * ((BB x) ^ 2 * wt x)) μ :=
      hB2wt.const_mul (1 / 8)
    have h12 : Integrable (fun x : XN N =>
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
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
        ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := hL1
    _ ≤ ∫ x in abox N ℓ,
        ((5 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 8) * ((BB x) ^ 2 * wt x)) := hL2
    _ = (5 / 2) * (∫ x : XN N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 8) * (∫ x : XN N, (BB x) ^ 2 * wt x ∂μ) := by
          simpa [μ] using hL3
    _ = (5 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ (g0 v h) (x i) (x j)|))
        + (1 / 8) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
          simp [μ, FF, QQ, SS, BB, WW, wt, mul_assoc, add_assoc]

/-- Pointwise square-3 estimate against the `|wPair h|` weight: for
`(a+b+c)² ≤ 3(a²+b²+c²)` pointwise, so integrating against the nonnegative
weight `|wPair h (x_i,x_j)|` gives the same for the integrals. -/


theorem qcross_d2_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤
      qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((5 / 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 8) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_d2_pair_quarter hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := by
            simp [mA, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4word (N := N) ℓ
          (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    calc
      |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|
          ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
              simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                  wPairC ℓ (g0 v h) (x p.1) (x p.2)))
      _ ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := hsum_le
      _ = (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rw [hq4]
          ring
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
          have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
          simpa [wPairC] using (sq3_mass_pair_le hℓ hg0i hg0s hRℓ
            (a := fun x => aP ℓ p.2 (aP ℓ p.1 Φ) x)
            (hac := aP_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
            (b := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
            (hbc := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
            (c := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
            (hcc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)) hne)
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1nn : 0 ≤ C1 := by
    dsimp [C1]
    positivity
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hM : C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≥ 0 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1nn hLinv) (sq_nonneg (N : ℝ))) hJ0
  have hmA : mA ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
      masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mA = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
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
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
      masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mG2 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
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
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_aQ_comm hℓ hne hΦc x]
    calc
      mG3 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mG3, wPairC]
      _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := hEq
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hC1le : 7 * C1 ≤ qcrossC * (a v) := by
    dsimp [C1, qcrossC]
    have hpos : 0 ≤ chiSup ^ 2 * π * (a v) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) Real.pi_nonneg) hav0
    have h112 : (112 : ℝ) ≤ (1000000 * 8 : ℝ) := by norm_num
    have hmul : (112 : ℝ) * (chiSup ^ 2 * π * (a v)) ≤ (1000000 * 8) * (chiSup ^ 2 * π * (a v)) :=
      mul_le_mul_of_nonneg_right h112 hpos
    nlinarith [hmul]
  have hX0 : 0 ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ := by positivity
  have hMainAbs : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤
      7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    let M : ℝ := C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
    have hD' : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4 := by
      simpa [q4] using hD
    calc
      |∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4 := hD'
      _ ≤ 7 * M + (1 / 4) * q4 := by
            nlinarith [hSsplit, hmA, hmG2, hmG3]
      _ = 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J + (1 / 4) * q4 := by
            dsimp [M]
            ring
      _ = 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hAbs : 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≤
      qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    have h1 : 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
      calc
        7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2
            = (7 * C1) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by ring
        _ ≤ (qcrossC * (a v)) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by
            exact mul_le_mul_of_nonneg_right hC1le hX0
        _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
            rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hJ0
  calc
    |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|
        ≤ 7 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hMainAbs
    _ ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hAbs]
    _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rfl




end BoseGases

end Submission
