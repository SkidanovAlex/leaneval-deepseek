import Mathlib
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Int.Lemmas
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Submission.Commons.Analysis.ExponentialSums.hilbert_separated
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable

set_option maxHeartbeats 1000000
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

namespace Commons.Analysis.Hilbert

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The truncated Hilbert kernel on `ℤ` -/

/-- The kernel of the truncated Hilbert transform on `ℤ`: `1/z` when `1 ≤ |z| ≤ N`, and `0`
otherwise. -/
def vvK (N : ℕ) (z : ℤ) : ℂ :=
  if z.natAbs = 0 ∨ N < z.natAbs then 0 else (((z : ℤ) : ℂ))⁻¹

lemma vvK_of_ne_zero {N : ℕ} {z : ℤ} (hz : z.natAbs ≠ 0) :
    vvK N z = if N < z.natAbs then 0 else (((z : ℤ) : ℂ))⁻¹ := by
  unfold vvK
  by_cases h : N < z.natAbs
  · rw [if_pos (Or.inr h), if_pos h]
  · rw [if_neg (fun hh => hh.elim hz h), if_neg h]

/-- Triangle-inequality case analysis for the truncated Hilbert kernel. -/
lemma vvK_sub_le {N : ℕ} {u v : ℤ} (hu : u.natAbs ≠ 0) (hv : v.natAbs ≠ 0) :
    ‖vvK N u - vvK N v‖ ≤
      ‖(((u : ℤ) : ℂ))⁻¹ - (((v : ℤ) : ℂ))⁻¹‖
      + (if u.natAbs ≤ N ∧ N < v.natAbs then ‖(((u : ℤ) : ℂ))⁻¹‖ else 0)
      + (if v.natAbs ≤ N ∧ N < u.natAbs then ‖(((v : ℤ) : ℂ))⁻¹‖ else 0) := by
  rw [vvK_of_ne_zero hu, vvK_of_ne_zero hv]
  have h1 : (0:ℝ) ≤ ‖(((u : ℤ) : ℂ))⁻¹ - (((v : ℤ) : ℂ))⁻¹‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖(((u : ℤ) : ℂ))⁻¹‖ := norm_nonneg _
  have h3 : (0:ℝ) ≤ ‖(((v : ℤ) : ℂ))⁻¹‖ := norm_nonneg _
  by_cases hNu : N < u.natAbs
  · rw [if_pos hNu]
    by_cases hNv : N < v.natAbs
    · rw [if_pos hNv, sub_zero, norm_zero]
      rw [if_neg (by omega : ¬ (u.natAbs ≤ N ∧ N < v.natAbs)),
        if_neg (by omega : ¬ (v.natAbs ≤ N ∧ N < u.natAbs))]
      linarith
    · rw [if_neg hNv]
      rw [if_neg (by omega : ¬ (u.natAbs ≤ N ∧ N < v.natAbs)),
        if_pos (by omega : v.natAbs ≤ N ∧ N < u.natAbs)]
      simp only [zero_sub, norm_neg]
      linarith
  · rw [if_neg hNu]
    by_cases hNv : N < v.natAbs
    · rw [if_pos hNv]
      rw [if_pos (by omega : u.natAbs ≤ N ∧ N < v.natAbs),
        if_neg (by omega : ¬ (v.natAbs ≤ N ∧ N < u.natAbs))]
      simp only [sub_zero]
      linarith
    · rw [if_neg hNv]
      rw [if_neg (by omega : ¬ (u.natAbs ≤ N ∧ N < v.natAbs)),
        if_neg (by omega : ¬ (v.natAbs ≤ N ∧ N < u.natAbs))]
      linarith

/-! ### Chebyshev-type lemmas for `eLpNorm` with exponent `2` -/

lemma sq_eLpNorm_two {E : Type*} [NormedAddCommGroup E] (u : ℤ → E) :
    (eLpNorm u (ENNReal.ofReal 2) (Measure.count : Measure ℤ)) ^ (2:ℝ)
      = ∫⁻ n : ℤ, ‖u n‖ₑ ^ (2:ℝ) ∂(Measure.count : Measure ℤ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) .of_discrete,
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Chebyshev for a nonnegative `ℝ≥0∞`-valued function: the measure of the level set is controlled
by the integral of the square. -/
lemma mul_count_le_lintegral_sq {F : ℤ → ℝ≥0∞} {ε : ℝ≥0∞} :
    Measure.count {n : ℤ | ε ≤ F n} * ε ^ (2:ℝ) ≤ ∫⁻ n : ℤ, (F n) ^ (2:ℝ) ∂Measure.count := by
  classical
  set s : Set ℤ := {n : ℤ | ε ≤ F n} with hs
  have hsmeas : MeasurableSet s := (Set.countable_univ.mono (Set.subset_univ s)).measurableSet
  have hconst : ∫⁻ n in s, ε ^ (2:ℝ) ∂(Measure.count : Measure ℤ)
      = ε ^ (2:ℝ) * Measure.count s := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hmono : ∫⁻ n in s, ε ^ (2:ℝ) ∂(Measure.count : Measure ℤ)
      ≤ ∫⁻ n in s, (F n) ^ (2:ℝ) ∂(Measure.count : Measure ℤ) := by
    rw [← lintegral_indicator hsmeas, ← lintegral_indicator hsmeas]
    apply lintegral_mono
    intro n
    by_cases hn : n ∈ s
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
      have hn' : ε ≤ F n := by rwa [hs] at hn
      exact ENNReal.rpow_le_rpow hn' (by norm_num)
    · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]
  have hsplit : ∫⁻ n : ℤ, (F n) ^ (2:ℝ) ∂(Measure.count : Measure ℤ)
      = ∫⁻ n in s, (F n) ^ (2:ℝ) ∂Measure.count
        + ∫⁻ n in sᶜ, (F n) ^ (2:ℝ) ∂Measure.count :=
    (lintegral_add_compl (fun n : ℤ => (F n) ^ (2:ℝ)) (A := s) hsmeas).symm
  rw [hconst] at hmono
  calc Measure.count s * ε ^ (2:ℝ) = ε ^ (2:ℝ) * Measure.count s := by ring
    _ ≤ ∫⁻ n in s, (F n) ^ (2:ℝ) ∂(Measure.count : Measure ℤ) := hmono
    _ ≤ ∫⁻ n : ℤ, (F n) ^ (2:ℝ) ∂Measure.count := by
        rw [hsplit]
        exact le_add_right le_rfl

/-! ### Tails of `∑ 1/k²` -/

lemma sum_inv_sq_le_of_ge {R : ℕ} (hR : 2 ≤ R) {t : Finset ℕ} (ht : ∀ d ∈ t, R ≤ d) :
    ∑ d ∈ t, ((1:ℝ) / (d:ℝ)^2) ≤ 2 / R := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; positivity
  · set M : ℕ := t.max' hne with hM
    have hsub : t ⊆ Finset.Ioc (R - 1) M := by
      intro d hd
      rw [Finset.mem_Ioc]
      exact ⟨by have := ht d hd; omega, Finset.le_max' t d hd⟩
    have hkey : ((R - 1 : ℕ) : ℝ)⁻¹ ≤ 2 / R := by
      have h1 : (0:ℝ) < ((R - 1 : ℕ) : ℝ) := by
        have : 0 < R - 1 := by omega
        exact_mod_cast this
      have h2 : (0:ℝ) < (R:ℝ) := by
        have : 0 < R := by omega
        exact_mod_cast this
      rw [div_eq_mul_inv, mul_comm]
      rw [inv_le_comm₀ h1 (by positivity)]
      rw [mul_inv, inv_inv]
      have h3 : (2:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
      have h5 : (((R - 1 : ℕ)) : ℝ) = (R:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one]
      rw [h5]
      linarith
    calc ∑ d ∈ t, ((1:ℝ) / (d:ℝ)^2)
        ≤ ∑ d ∈ Finset.Ioc (R - 1) M, ((1:ℝ) / (d:ℝ)^2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
      _ = ∑ d ∈ Finset.Ioc (R - 1) M, ((d:ℝ)^2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [one_div]
      _ ≤ ((R - 1 : ℕ) : ℝ)⁻¹ - ((M:ℕ):ℝ)⁻¹ := by
          refine sum_Ioc_inv_sq_le_sub (by omega : R - 1 ≠ 0) ?_
          obtain ⟨d, hd⟩ := hne
          have h1 : R ≤ d := ht d hd
          have h2 : d ≤ M := by
            rw [hM]; exact Finset.le_max' t d hd
          omega
      _ ≤ 2 / R := by
          have : (0:ℝ) ≤ ((M:ℕ):ℝ)⁻¹ := by positivity
          linarith

lemma tsum_nat_ite_inv_sq_le {R : ℕ} (hR : 2 ≤ R) :
    ∑' n : ℕ, (if R ≤ n then ((1:ℝ) / (n:ℝ)^2) else 0) ≤ 2 / R := by
  have hnn : ∀ n : ℕ, 0 ≤ (if R ≤ n then ((1:ℝ) / (n:ℝ)^2) else 0) := by
    intro n; by_cases h : R ≤ n <;> simp [h]
  refine Real.tsum_le_of_sum_le hnn (fun s => ?_)
  rw [← Finset.sum_filter]
  exact sum_inv_sq_le_of_ge hR (fun d hd => (Finset.mem_filter.mp hd).2)

lemma summable_nat_ite_inv_sq (R : ℕ) (hR : 2 ≤ R) :
    Summable (fun n : ℕ => (if R ≤ n then ((1:ℝ) / (n:ℝ)^2) else 0)) := by
  have hnn : ∀ n : ℕ, 0 ≤ (if R ≤ n then ((1:ℝ) / (n:ℝ)^2) else 0) := by
    intro n; by_cases h : R ≤ n <;> simp [h]
  refine summable_of_sum_le hnn (c := 2 / R) (fun s => ?_)
  rw [← Finset.sum_filter]
  exact sum_inv_sq_le_of_ge hR (fun d hd => (Finset.mem_filter.mp hd).2)

lemma tsum_nat_shift_ite_inv_sq_le {R : ℕ} (hR : 2 ≤ R) :
    ∑' n : ℕ, (if R ≤ n + 1 then ((1:ℝ) / ((n:ℝ) + (1:ℝ))^2) else 0) ≤ 2 / R := by
  have hnn : ∀ n : ℕ, 0 ≤ (if R ≤ n + 1 then ((1:ℝ) / ((n:ℝ) + (1:ℝ))^2) else 0) := by
    intro n
    by_cases h : R ≤ n + 1
    · rw [if_pos h]
      exact div_nonneg zero_le_one (sq_nonneg _)
    · rw [if_neg h]
  refine Real.tsum_le_of_sum_le hnn (fun s => ?_)
  rw [← Finset.sum_filter]
  set t : Finset ℕ := s.filter fun n => R ≤ n + 1 with ht
  have hinj : Set.InjOn (fun n : ℕ => n + 1) ↑t := by
    intro a _ b _ hab
    simpa using hab
  have himg : ∑ n ∈ t, ((1:ℝ) / ((n:ℝ) + (1:ℝ))^2)
      = ∑ d ∈ t.image (fun n : ℕ => n + 1), ((1:ℝ) / (d:ℝ)^2) := by
    rw [show (∑ n ∈ t, ((1:ℝ) / ((n:ℝ) + (1:ℝ))^2))
        = ∑ n ∈ t, (fun d : ℕ => (1:ℝ) / (d:ℝ)^2) (n + 1) from
      Finset.sum_congr rfl (fun n _ => by
        have hcast : (((n + 1 : ℕ)) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
        rw [← hcast])]
    exact (Finset.sum_image (f := fun d : ℕ => (1:ℝ) / (d:ℝ)^2)
      (g := fun n : ℕ => n + 1) hinj).symm
  rw [himg]
  refine sum_inv_sq_le_of_ge hR (fun d hd => ?_)
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
  exact (Finset.mem_filter.mp hn).2

lemma tsum_int_ite_inv_sq_le {R : ℕ} (hR : 2 ≤ R) :
    ∑' x : ℤ, (if R ≤ x.natAbs then ((1:ℝ) / (x.natAbs : ℝ)^2) else 0) ≤ 4 / R := by
  have hnn : ∀ x : ℤ, 0 ≤ (if R ≤ x.natAbs then ((1:ℝ) / (x.natAbs : ℝ)^2) else 0) := by
    intro x
    by_cases h : R ≤ x.natAbs
    · rw [if_pos h]
      exact div_nonneg zero_le_one (sq_nonneg _)
    · rw [if_neg h]
  refine Real.tsum_le_of_sum_le hnn (fun s => ?_)
  rw [← Finset.sum_filter]
  set t : Finset ℤ := s.filter fun x => R ≤ x.natAbs with ht
  have hsplit : ∑ x ∈ t, ((1:ℝ) / (x.natAbs : ℝ)^2)
      = ∑ x ∈ t.filter (fun x : ℤ => 0 ≤ x), ((1:ℝ) / (x.natAbs : ℝ)^2)
        + ∑ x ∈ t.filter (fun x : ℤ => ¬ (0 ≤ x)), ((1:ℝ) / (x.natAbs : ℝ)^2) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := t) (p := fun x : ℤ => 0 ≤ x)]
  rw [hsplit]
  have hpos : ∑ x ∈ t.filter (fun x : ℤ => 0 ≤ x), ((1:ℝ) / (x.natAbs : ℝ)^2) ≤ 2 / R := by
    have hinj : Set.InjOn (fun x : ℤ => x.natAbs) ↑(t.filter (fun x : ℤ => 0 ≤ x)) := by
      intro a ha b hb hab
      have ha' : 0 ≤ a := (Finset.mem_filter.mp ha).2
      have hb' : 0 ≤ b := (Finset.mem_filter.mp hb).2
      simp only at hab
      omega
    have himg : ∑ x ∈ t.filter (fun x : ℤ => 0 ≤ x), ((1:ℝ) / (x.natAbs : ℝ)^2)
        = ∑ d ∈ (t.filter (fun x : ℤ => 0 ≤ x)).image (fun x : ℤ => x.natAbs), ((1:ℝ) / (d:ℝ)^2) := by
      exact (Finset.sum_image (f := fun d : ℕ => (1:ℝ) / (d:ℝ)^2)
        (g := fun x : ℤ => x.natAbs) hinj).symm
    rw [himg]
    refine sum_inv_sq_le_of_ge hR (fun d hd => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hneg : ∑ x ∈ t.filter (fun x : ℤ => ¬ (0 ≤ x)), ((1:ℝ) / (x.natAbs : ℝ)^2) ≤ 2 / R := by
    have hinj : Set.InjOn (fun x : ℤ => x.natAbs) ↑(t.filter (fun x : ℤ => ¬ (0 ≤ x))) := by
      intro a ha b hb hab
      have ha' : ¬ (0 ≤ a) := (Finset.mem_filter.mp ha).2
      have hb' : ¬ (0 ≤ b) := (Finset.mem_filter.mp hb).2
      simp only at hab
      omega
    have himg : ∑ x ∈ t.filter (fun x : ℤ => ¬ (0 ≤ x)), ((1:ℝ) / (x.natAbs : ℝ)^2)
        = ∑ d ∈ (t.filter (fun x : ℤ => ¬ (0 ≤ x))).image (fun x : ℤ => x.natAbs), ((1:ℝ) / (d:ℝ)^2) := by
      exact (Finset.sum_image (f := fun d : ℕ => (1:ℝ) / (d:ℝ)^2)
        (g := fun x : ℤ => x.natAbs) hinj).symm
    rw [himg]
    refine sum_inv_sq_le_of_ge hR (fun d hd => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have : (2:ℝ) / R + 2 / R = 4 / R := by ring
  linarith

lemma summable_finset_sum_int {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) : Summable (fun n : ℤ => ∑ i ∈ s, f i n) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    simpa using (summable_zero : Summable (fun _ : ℤ => (0:ℝ)))
  · intro a s has ih hf
    have hs : ∀ i ∈ s, Summable (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha : Summable (f a) := hf a (Finset.mem_insert_self a s)
    rw [show (fun n : ℤ => ∑ i ∈ insert a s, f i n)
        = fun n : ℤ => f a n + ∑ i ∈ s, f i n from funext (fun n => Finset.sum_insert has)]
    exact ha.add (ih hs)

lemma tsum_finset_sum_int {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    ∑' n : ℤ, ∑ i ∈ s, f i n = ∑ i ∈ s, ∑' n : ℤ, f i n := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    simp
  · intro a s has ih hf
    have hs : ∀ i ∈ s, Summable (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha : Summable (f a) := hf a (Finset.mem_insert_self a s)
    have hsum : Summable (fun n : ℤ => ∑ i ∈ s, f i n) :=
      summable_finset_sum_int s f hs
    rw [show (∑' n : ℤ, ∑ i ∈ insert a s, f i n) = ∑' n : ℤ, (f a n + ∑ i ∈ s, f i n) from
        tsum_congr (fun n => Finset.sum_insert has),
      Summable.tsum_add ha hsum, Finset.sum_insert has, ih hs]

lemma summable_int_ite_inv_sq (R : ℕ) (hR : 2 ≤ R) :
    Summable (fun x : ℤ => (if R ≤ x.natAbs then ((1:ℝ) / (x.natAbs : ℝ)^2) else 0)) := by
  have hnn : ∀ x : ℤ, 0 ≤ (if R ≤ x.natAbs then ((1:ℝ) / (x.natAbs : ℝ)^2) else 0) := by
    intro x
    by_cases h : R ≤ x.natAbs
    · rw [if_pos h]; exact div_nonneg zero_le_one (sq_nonneg _)
    · rw [if_neg h]
  refine summable_of_sum_le hnn (c := 4 / R) (fun s => ?_)
  rw [← Finset.sum_filter]
  set t : Finset ℤ := s.filter fun x => R ≤ x.natAbs with ht
  have hsplit : ∑ x ∈ t, ((1:ℝ) / (x.natAbs : ℝ)^2)
      = ∑ x ∈ t.filter (fun x : ℤ => 0 ≤ x), ((1:ℝ) / (x.natAbs : ℝ)^2)
        + ∑ x ∈ t.filter (fun x : ℤ => ¬ (0 ≤ x)), ((1:ℝ) / (x.natAbs : ℝ)^2) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := t) (p := fun x : ℤ => 0 ≤ x)]
  rw [hsplit]
  have hpos : ∑ x ∈ t.filter (fun x : ℤ => 0 ≤ x), ((1:ℝ) / (x.natAbs : ℝ)^2) ≤ 2 / R := by
    have hinj : Set.InjOn (fun x : ℤ => x.natAbs) ↑(t.filter (fun x : ℤ => 0 ≤ x)) := by
      intro a ha b hb hab
      have ha' : 0 ≤ a := (Finset.mem_filter.mp ha).2
      have hb' : 0 ≤ b := (Finset.mem_filter.mp hb).2
      simp only at hab
      omega
    have himg : ∑ x ∈ t.filter (fun x : ℤ => 0 ≤ x), ((1:ℝ) / (x.natAbs : ℝ)^2)
        = ∑ d ∈ (t.filter (fun x : ℤ => 0 ≤ x)).image (fun x : ℤ => x.natAbs), ((1:ℝ) / (d:ℝ)^2) := by
      exact (Finset.sum_image (f := fun d : ℕ => (1:ℝ) / (d:ℝ)^2)
        (g := fun x : ℤ => x.natAbs) hinj).symm
    rw [himg]
    refine sum_inv_sq_le_of_ge hR (fun d hd => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hneg : ∑ x ∈ t.filter (fun x : ℤ => ¬ (0 ≤ x)), ((1:ℝ) / (x.natAbs : ℝ)^2) ≤ 2 / R := by
    have hinj : Set.InjOn (fun x : ℤ => x.natAbs) ↑(t.filter (fun x : ℤ => ¬ (0 ≤ x))) := by
      intro a ha b hb hab
      have ha' : ¬ (0 ≤ a) := (Finset.mem_filter.mp ha).2
      have hb' : ¬ (0 ≤ b) := (Finset.mem_filter.mp hb).2
      simp only at hab
      omega
    have himg : ∑ x ∈ t.filter (fun x : ℤ => ¬ (0 ≤ x)), ((1:ℝ) / (x.natAbs : ℝ)^2)
        = ∑ d ∈ (t.filter (fun x : ℤ => ¬ (0 ≤ x))).image (fun x : ℤ => x.natAbs), ((1:ℝ) / (d:ℝ)^2) := by
      exact (Finset.sum_image (f := fun d : ℕ => (1:ℝ) / (d:ℝ)^2)
        (g := fun x : ℤ => x.natAbs) hinj).symm
    rw [himg]
    refine sum_inv_sq_le_of_ge hR (fun d hd => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have : (2:ℝ) / R + 2 / R = 4 / R := by ring
  linarith

lemma setLIntegral_shift_int (g : ℤ → ℝ≥0∞) (c : ℤ) (S : Set ℤ) :
    ∫⁻ x in {x : ℤ | x + c ∈ S}, g (x + c) ∂(Measure.count : Measure ℤ)
      = ∫⁻ y in S, g y ∂(Measure.count : Measure ℤ) := by
  rw [← MeasureTheory.lintegral_indicator
        (by exact (Set.countable_univ.mono (Set.subset_univ _)).measurableSet)
        (fun x => g (x + c)),
      ← MeasureTheory.lintegral_indicator
        (by exact (Set.countable_univ.mono (Set.subset_univ _)).measurableSet) g]
  rw [← MeasureTheory.lintegral_add_right_eq_self (fun x : ℤ => S.indicator g x) c]
  apply lintegral_congr_ae
  filter_upwards with x
  by_cases h : x + c ∈ S
  · rw [Set.indicator_of_mem (show x ∈ {x : ℤ | x + c ∈ S} from h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℤ | x + c ∈ S} from h), Set.indicator_of_notMem h]

lemma lintegral_natAbs_tail_inv_sq_le (c : ℤ) (R : ℕ) (hR : 2 ≤ R) :
    ∫⁻ x in {x : ℤ | R ≤ (x - c).natAbs},
        ENNReal.ofReal ((1:ℝ) / ((x - c).natAbs : ℝ)^2) ∂(Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (4 / R) := by
  rw [show (fun x : ℤ => ENNReal.ofReal ((1:ℝ) / ((x - c).natAbs : ℝ)^2))
      = (fun x : ℤ => ENNReal.ofReal ((1:ℝ) / ((x + (-c)).natAbs : ℝ)^2)) from by
        funext x; simp only [sub_eq_add_neg]]
  rw [show {x : ℤ | R ≤ (x - c).natAbs} = {x : ℤ | x + (-c) ∈ {y : ℤ | R ≤ y.natAbs}} from by
        ext x; simp [sub_eq_add_neg]]
  rw [setLIntegral_shift_int (fun y : ℤ => ENNReal.ofReal ((1:ℝ) / (y.natAbs : ℝ)^2))
    (-c) {y : ℤ | R ≤ y.natAbs}]
  rw [← MeasureTheory.lintegral_indicator
      (by exact (Set.countable_univ.mono (Set.subset_univ _)).measurableSet)
      (fun y : ℤ => ENNReal.ofReal ((1:ℝ) / (y.natAbs : ℝ)^2))]
  rw [lintegral_count]
  rw [show (∑' a : ℤ, {y : ℤ | R ≤ y.natAbs}.indicator
        (fun y : ℤ => ENNReal.ofReal ((1:ℝ) / (y.natAbs : ℝ)^2)) a)
      = ∑' a : ℤ, ENNReal.ofReal (if R ≤ a.natAbs then ((1:ℝ) / (a.natAbs : ℝ)^2) else 0) from
    tsum_congr (fun a => by
      by_cases h : R ≤ a.natAbs
      · rw [if_pos h, Set.indicator_of_mem (show a ∈ {y : ℤ | R ≤ y.natAbs} from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show a ∉ {y : ℤ | R ≤ y.natAbs} from h),
          ENNReal.ofReal_zero])]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (f := fun y : ℤ => (if R ≤ y.natAbs then ((1:ℝ) / (y.natAbs : ℝ)^2) else 0))
      (fun y => by
        by_cases h : R ≤ y.natAbs
        · rw [if_pos h]; exact div_nonneg zero_le_one (sq_nonneg _)
        · rw [if_neg h])
      (summable_int_ite_inv_sq R hR)]
  apply ENNReal.ofReal_le_ofReal
  exact tsum_int_ite_inv_sq_le hR

lemma sq_eLpNorm_two' {E : Type*} [ENorm E] [TopologicalSpace E] (u : ℤ → E) :
    (eLpNorm u (ENNReal.ofReal 2) (Measure.count : Measure ℤ)) ^ (2:ℝ)
      = ∫⁻ n : ℤ, ‖u n‖ₑ ^ (2:ℝ) ∂(Measure.count : Measure ℤ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) .of_discrete,
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)]
  rw [← ENNReal.rpow_mul]
  norm_num
