import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.CompletePartialOrder

namespace Commons.Measure.HardyLittlewood

open MeasureTheory
open scoped BigOperators ENNReal

open Metric Module

/-- Dilation of balls scales their Lebesgue measure by the dilating factor to the power of
the dimension, in `EuclideanSpace ℝ (Fin n)`. -/
lemma volume_ball_mul_of_pos (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t)
    (r : ℝ) :
    volume (Metric.ball x (t * r)) = ENNReal.ofReal (t ^ n) * volume (Metric.ball x r) := by
  rw [MeasureTheory.Measure.addHaar_ball_mul_of_pos volume x ht r,
      ← MeasureTheory.Measure.addHaar_ball_center volume x r]
  simp [finrank_euclideanSpace]

theorem weak_type_one_finite_balls (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n)) (r : ι → ℝ)
      (hr : ∀ i, 0 < r i) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f)
      (lam : ℝ≥0∞) (hlam0 : lam ≠ 0) (hlamtop : lam ≠ ⊤)
      (havg : ∀ i, lam * volume (Metric.ball (c i) (r i))
        ≤ ∫⁻ x in Metric.ball (c i) (r i), f x),
      lam * volume (⋃ i, Metric.ball (c i) (r i)) ≤ ENNReal.ofReal C * ∫⁻ x, f x := by
  refine ⟨5 ^ n, pow_pos (by norm_num) n, ?_⟩
  intro ι _inst c r hr f hf lam hlam0 hlamtop havg
  let B : ι → Set (EuclideanSpace ℝ (Fin n)) := fun i => Metric.ball (c i) (r i)
  let D : ι → Set (EuclideanSpace ℝ (Fin n)) := fun i => Metric.ball (c i) (5 * r i)
  set R : ℝ := ∑ i, r i with hR
  have hRle : ∀ i, r i ≤ R := by
    intro i
    rw [hR]
    exact Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)
  obtain ⟨u, _hu_sub, hu_disj, hu_cov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (α := EuclideanSpace ℝ (Fin n)) (t := Set.univ) c r R (fun a _ => hRle a) 5 (by norm_num)
  have hcover : (⋃ i, B i) ⊆ ⋃ b ∈ u, D b := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨b, hbu, hsub⟩ := hu_cov i (Set.mem_univ i)
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hbu, hsub hi⟩⟩
  have hu_count : u.Countable := (Set.toFinite u).countable
  have hvol : volume (⋃ i, B i) ≤ ENNReal.ofReal (5 ^ n) * ∑' b : u, volume (B (b : ι)) := by
    calc volume (⋃ i, B i)
        ≤ volume (⋃ b : u, D (b : ι)) := by
          apply measure_mono
          intro x hx
          have hx' : x ∈ ⋃ b ∈ u, D b := hcover hx
          rwa [Set.iUnion_subtype (p := fun b : ι => b ∈ u) (s := fun b : u => D (b : ι))]
      _ ≤ ∑' b : u, volume (D (b : ι)) := measure_iUnion_le _
      _ = ∑' b : u, ENNReal.ofReal (5 ^ n) * volume (B (b : ι)) := by
          apply tsum_congr
          intro b
          exact volume_ball_mul_of_pos n (c (b : ι)) (by norm_num) (r (b : ι))
      _ = ENNReal.ofReal (5 ^ n) * ∑' b : u, volume (B (b : ι)) := by
          rw [ENNReal.tsum_mul_left]
  have hdisj_u : Pairwise (Function.onFun Disjoint fun b : u => B (b : ι)) := by
    intro a b hab
    exact hu_disj a.property b.property (fun h => hab (Subtype.ext h))
  have hsum_int : ∑' b : u, ∫⁻ x in B (b : ι), f x = ∫⁻ x in (⋃ b ∈ u, B b), f x := by
    rw [← lintegral_biUnion hu_count (fun i _ => measurableSet_ball) hu_disj f]
  calc lam * volume (⋃ i, B i)
      ≤ lam * (ENNReal.ofReal (5 ^ n) * ∑' b : u, volume (B (b : ι))) :=
        mul_le_mul_right hvol lam
    _ = ENNReal.ofReal (5 ^ n) * (lam * ∑' b : u, volume (B (b : ι))) :=
        mul_left_comm lam (ENNReal.ofReal (5 ^ n)) (∑' b : u, volume (B (b : ι)))
    _ = ENNReal.ofReal (5 ^ n) * ∑' b : u, lam * volume (B (b : ι)) := by
        rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (5 ^ n) * ∑' b : u, ∫⁻ x in B (b : ι), f x := by
        apply mul_le_mul_right
        exact ENNReal.tsum_le_tsum (fun b => havg (b : ι))
    _ = ENNReal.ofReal (5 ^ n) * ∫⁻ x in (⋃ b ∈ u, B b), f x := by rw [← hsum_int]
    _ ≤ ENNReal.ofReal (5 ^ n) * ∫⁻ x, f x := by
        apply mul_le_mul_right
        simpa using lintegral_mono_set (μ := volume) (Set.subset_univ _) (f := f)

end Commons.Measure.HardyLittlewood