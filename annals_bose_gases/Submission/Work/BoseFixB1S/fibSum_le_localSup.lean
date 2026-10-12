import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.flatArmFibreLocalSup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

theorem fibSum_le_localSup {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (hΦc : Continuous Φ)
    {S : EuclideanSpace ℝ (Fin 3) → ℝ} (hSm : Measurable S) {B : ℝ} (hB : 0 ≤ B)
    (hSb : ∀ x y : EuclideanSpace ℝ (Fin 3), ‖y - x‖ ≤ R →
      Submission.BoseGases.chiSmallB M ℓ d u y ≤ S x)
    (hSB : ∀ x : EuclideanSpace ℝ (Fin 3), S x ≤ B) :
    Work.BoseFixB1.fibSum h M ℓ d u Φ
      ≤ (16 * Real.pi * _root_.BoseGases.a v / Work.SmallBoxSliding.smallConvLower M)
        * ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * ∑ i : Fin n,
              Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i) := by
  -- The value of `∫ |g₀|` is `8π·a v`.
  set G : ℝ := ∫ w : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h w| with hGdef
  have hGval : G = 8 * Real.pi * (_root_.BoseGases.a v) := by
    rw [hGdef]
    have habs : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z := by
      refine integral_congr_ae ?_
      filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h]
        with z hz
      exact abs_of_nonneg hz
    rw [habs, Submission.BoseGases.g0_integral hR hv_supp h]
  -- The constant of the fibre estimate.
  set c : ℝ := 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * G with hcdef
  have hceq : c = 16 * Real.pi * (_root_.BoseGases.a v) / Work.SmallBoxSliding.smallConvLower M := by
    rw [hcdef, hGval]; ring
  -- `S` is nonnegative (it dominates the nonnegative cutoff at distance `0`).
  have hSnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ S x := fun x =>
    le_trans (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)
      (hSb x x (by simpa using hR.le))
  -- The pointwise (local-sup) fibre bound.
  have hfib : ∀ x : Submission.BoseGases.X n, ∀ i : Fin n,
      (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) := by
    intro x i
    have h1 := fibre_abs_le_chiB_mul_localSup (v := v) (R0 := R) h hR hv_supp hM hℓ hd hR16 hRχ
      u (x i) (fun y hy => hSb (x i) y hy)
    rw [← hGdef] at h1
    calc (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ |∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y| := le_abs_self _
      _ ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * G)
            * Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i) := h1
      _ = c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) := by
          rw [hcdef]; ring
  -- The pointwise comparison of the integrands.
  have hpoint : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ c * ((Φ x) ^ 2 *
            ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) := by
    intro x
    have hsum : (∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
        ≤ ∑ i : Fin n, c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) :=
      Finset.sum_le_sum fun i _ => hfib x i
    calc (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ (Φ x) ^ 2 * ∑ i : Fin n,
            c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = c * ((Φ x) ^ 2
            * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) := by
          have h1 : (∑ i : Fin n,
                c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)))
              = c * ∑ i : Fin n,
                  Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i) :=
            (Finset.mul_sum Finset.univ (fun i : Fin n =>
              Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) c).symm
          rw [h1]
          ring
  -- The dominating integrand is integrable on the compact box (this is where the measurability of
  -- `S` and its bound `B` are used).
  have hAbox : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Work.UBBInputs9.B.abox_isCompact n ℓ
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  have hHmeas : Measurable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) :=
    ((hΦc.measurable).pow_const 2).mul
      (Finset.measurable_sum _ fun i _ =>
        (hcB.measurable.comp (measurable_pi_apply i)).mul
          (hSm.comp (measurable_pi_apply i)))
  set Cs : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hCsdef
  have hCs0 : 0 ≤ Cs := by
    rw [hCsdef]
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  obtain ⟨BΦ, hBΦ⟩ := hAbox.exists_bound_of_continuousOn hΦc.continuousOn
  set Bd : ℝ := max BΦ 0 with hBddef
  have hBd0 : 0 ≤ Bd := le_max_right _ _
  have hBΦ' : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ Bd := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hBΦ x hx) (le_max_left _ _)
  have hHbound : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ‖(Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)‖
        ≤ Bd ^ 2 * ((n : ℝ) * (Cs * B)) := by
    intro x hx
    have hterm : ∀ i : Fin n,
        |Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)| ≤ Cs * B := by
      intro i
      have hχ : |Submission.BoseGases.chiSmallB M ℓ d u (x i)| ≤ Cs := by
        rw [abs_of_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i)), hCsdef]
        exact Work.BoseFixB1.chiSmallB_le_sup hM u (x i)
      have hSabs : |S (x i)| ≤ B := by
        rw [abs_of_nonneg (hSnn (x i))]
        exact hSB (x i)
      rw [abs_mul]
      exact mul_le_mul hχ hSabs (abs_nonneg _) hCs0
    have hsum : |∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)|
        ≤ (n : ℝ) * (Cs * B) := by
      calc |∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)|
          ≤ ∑ i : Fin n, |Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, Cs * B := Finset.sum_le_sum fun i _ => hterm i
        _ = (n : ℝ) * (Cs * B) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
    have hsq : (Φ x) ^ 2 ≤ Bd ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg (Φ x)) (hBΦ' x hx) 2
    exact mul_le_mul hsq hsum (abs_nonneg _) (by positivity)
  have hH_int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i))
      (Submission.BoseGases.abox n ℓ) := by
    refine MeasureTheory.IntegrableOn.of_bound hAbox.measure_lt_top
      hHmeas.aestronglyMeasurable (Bd ^ 2 * ((n : ℝ) * (Cs * B))) ?_
    rw [MeasureTheory.ae_restrict_iff' hAbox.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hHbound x hx
  -- The monotone integration.
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, c * ((Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
          Work.BoseFixB1.wSmall1Pair_fibre_nonneg (v := v) (R0 := R) hR hv hvrad hv_supp h
            u (x i)))
      (hH_int.const_mul c) (Filter.Eventually.of_forall fun x => hpoint x)
  calc Work.BoseFixB1.fibSum h M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) := by
        rw [Work.BoseFixB1.fibSum]
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, c * ((Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) := hmono
    _ = c * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) :=
        integral_const_mul _ _
    _ = (16 * Real.pi * _root_.BoseGases.a v / Work.SmallBoxSliding.smallConvLower M)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * S (x i)) := by
        rw [hceq]

end Work.BoseFixB1S
