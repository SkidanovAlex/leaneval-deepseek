import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Up.Core
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.FlatFib.fibMeasurableRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.integrableOn_fibSum_abox` — the abox integrability of the flat fibre integrand

The localised one-body fibre `fib z = ∫_{acube ℓ} wSmall1Pair h M ℓ d u z y dy` is dominated by
`K·(a v)·(chiSupAbs·chiSmall M ((ℓd)⁻¹•z − u))` (`Work.BoseFixB1.Up.wSmall1Pair_fibre_le_chiM`),
which is bounded on the analysis box, so `Φ²·Σᵢfib(xᵢ)` is integrable there for a continuous `Φ`.
This is the `hint` hypothesis of `Work.BoseFixB1S.flatFibreMeanFieldB1Oper` (the exactly-flat fibre
identity).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option maxHeartbeats 1000000

namespace Work.BoseFixB1.Up

theorem integrableOn_fibSum_abox {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R0 : ℝ} (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      (Submission.BoseGases.abox n ℓ) := by
  classical
  have hfb := Work.BoseFixB1.Up.wSmall1Pair_fibre_le_chiM (v := v) (R0 := R0) hv_supp hR0 hv hvrad
    h hM hℓ hd hR16 hRχ u
  obtain ⟨fib', hfib'm, hfib'eq⟩ :=
    Work.BoseFixB1S.FlatFib.fibMeasurableRep (v := v) h hM hℓ hd u
  have hfibm : Measurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y) := by
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
        = fib' from funext (fun z => (hfib'eq z).symm)]
    exact hfib'm
  have hCχ : (0:ℝ) ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    have := Submission.BoseGases.chiSupAbs_nonneg
    have := Submission.BoseGases.chiSmallDecay_nonneg M
    positivity
  have hK1 : (0:ℝ) ≤ 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M := by
    have h1 : (0:ℝ) ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
    have h2 : (0:ℝ) ≤ Submission.BoseGases.chiSmallDecay M :=
      Submission.BoseGases.chiSmallDecay_nonneg M
    have h3 : (0:ℝ) < Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.smallConvLower_pos M
    positivity
  obtain ⟨CΦ, hCΦ0, hCΦb⟩ := Work.BoseFixB1S.exists_abox_bound (N := n) (ℓ := ℓ) hℓ hΦc
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ((hΦc.measurable.pow_const 2).aestronglyMeasurable).mul
      (Finset.measurable_sum _ (fun i _ =>
        hfibm.comp (measurable_pi_apply i))).aestronglyMeasurable
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le) hmeas
    ((n : ℝ) * (CΦ ^ 2 * (16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M
      * (_root_.BoseGases.a v) * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay M)))) ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  have hfibb : ∀ i : Fin n,
      |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y|
        ≤ 16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M * (_root_.BoseGases.a v)
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
    intro i
    have h3 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x i - u)
        ≤ Submission.BoseGases.chiSmallDecay M :=
      le_trans (le_abs_self _) (Submission.BoseGases.chiSmall_decay_coord_le_decay hM _)
    have h5 : Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x i - u)
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
      mul_le_mul_of_nonneg_left h3 Submission.BoseGases.chiSupAbs_nonneg
    have h4 : (0:ℝ) ≤ 16 * π * Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M
        * (_root_.BoseGases.a v) := mul_nonneg hK1 hav.le
    exact le_trans (hfb (x i)) (mul_le_mul_of_nonneg_left h5 h4)
  have hsum : |∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y|
      ≤ (n : ℝ) * (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M
          * (_root_.BoseGases.a v) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul Finset.univ
      (fun i : Fin n => |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y|)
      (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
        / Work.SmallBoxSliding.smallConvLower M * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M))
      (fun i _ => hfibb i)
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hle
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
  have hΦb : |Φ x| ≤ CΦ := hCΦb x hx
  have hΦ2 : Φ x ^ 2 ≤ CΦ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hΦb 2
  have hKn : 0 ≤ 16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
      / Work.SmallBoxSliding.smallConvLower M * (_root_.BoseGases.a v)
      * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
    mul_nonneg (mul_nonneg hK1 hav.le) hCχ
  calc Φ x ^ 2 * |∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y|
      ≤ CΦ ^ 2 * ((n : ℝ) * (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M
          * (_root_.BoseGases.a v) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M))) :=
        mul_le_mul hΦ2 hsum (abs_nonneg _) (by positivity)
    _ = (n : ℝ) * (CΦ ^ 2 * (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M
          * (_root_.BoseGases.a v) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M))) := by ring

end Work.BoseFixB1.Up
