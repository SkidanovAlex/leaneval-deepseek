import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.LIntegral

namespace Commons.Analysis.DiscreteCZ

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Translation invariance of the Lebesgue integral on `ℤ` against the counting measure. -/
private lemma lintegral_sub_shift (f : ℤ → ℝ≥0∞) (c : ℤ) :
    ∫⁻ x, f (x - c) ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = ∫⁻ x, f x ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have h := MeasureTheory.lintegral_add_right_eq_self
    (μ := (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) f (-c)
  simpa [sub_eq_add_neg] using h

/-- Translation invariance of the Lebesgue integral over a shifted set on `ℤ`. -/
private lemma setLIntegral_sub_shift (f : ℤ → ℝ≥0∞) (c : ℤ) (T : Set ℤ) :
    ∫⁻ x in {x : ℤ | x - c ∈ T}, f (x - c) ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = ∫⁻ z in T, f z ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  rw [← MeasureTheory.lintegral_indicator
        (by measurability : MeasurableSet {x : ℤ | x - c ∈ T}) (fun x => f (x - c)),
      ← MeasureTheory.lintegral_indicator (by measurability : MeasurableSet T) f]
  rw [← lintegral_sub_shift (fun x => T.indicator f x) c]
  apply lintegral_congr_ae
  filter_upwards with x
  by_cases h : x - c ∈ T
  · rw [Set.indicator_of_mem (show x ∈ {x : ℤ | x - c ∈ T} from h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℤ | x - c ∈ T} from h),
        Set.indicator_of_notMem h]

/-- Discrete Hörmander bad–part estimate on `ℤ`. `w` is supported on the integer interval
`[a,b)`, has zero integral there, `c ∈ [a,b)`, and the kernel satisfies the discrete Hörmander
condition. Then the convolution is controlled on the far set `{x | 2(b-a) ≤ |x - c|}`. -/
theorem cz_bad_part_int_lintegral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (K : ℤ → ℂ) (Ak : ℝ) (hAk : 0 ≤ Ak)
    (hker : ∀ y : ℤ, y ≠ 0 →
      ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, ‖K (x - y) - K x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal Ak)
    (a b c : ℤ) (hab : a ≤ b) (hca : a ≤ c) (hcb : c < b)
    (w : ℤ → H) (hw : Summable w)
    (hwsupp : ∀ x, x ∉ Set.Ico a b → w x = 0)
    (hwmean : ∑ x ∈ Finset.Ico a b, w x = 0) :
    ∫⁻ x in {x : ℤ | 2 * (b - a).toNat ≤ (x - c).natAbs},
        ‖∑' y : ℤ, K (x - y) • w y‖ₑ ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal Ak * ∫⁻ y, ‖w y‖ₑ ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  set s : Finset ℤ := Finset.Ico a b with hs
  set T : Set ℤ := {z : ℤ | 2 * (b - a).toNat ≤ z.natAbs} with hT
  have hs_mem : ∀ z : ℤ, z ∈ s ↔ a ≤ z ∧ z < b := by
    intro z; rw [hs, Finset.mem_Ico]
  have hwmean' : ∑ z ∈ s, w z = 0 := by rw [hs]; exact hwmean
  -- pointwise rewriting of the convolution using the zero-mean hypothesis
  have hpoint : ∀ x : ℤ, ∑' y : ℤ, K (x - y) • w y
      = ∑ y ∈ s, (K (x - y) - K (x - c)) • w y := by
    intro x
    rw [tsum_eq_sum (s := s)]
    · have hcalc : ∑ y ∈ s, (K (x - y) - K (x - c)) • w y
          = ∑ y ∈ s, K (x - y) • w y - K (x - c) • ∑ y ∈ s, w y := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun z _ => by rw [sub_smul])
      rw [hcalc, hwmean']; simp
    · intro z hz
      rw [hwsupp z (fun h => hz (by rw [hs_mem]; exact h)), smul_zero]
  have hnorm : ∀ x : ℤ, ‖∑' y : ℤ, K (x - y) • w y‖ₑ
      ≤ ∑ y ∈ s, ‖w y‖ₑ * ‖K (x - y) - K (x - c)‖ₑ := by
    intro x
    rw [hpoint x]
    calc ‖∑ y ∈ s, (K (x - y) - K (x - c)) • w y‖ₑ
        ≤ ∑ y ∈ s, ‖(K (x - y) - K (x - c)) • w y‖ₑ := enorm_sum_le s _
      _ = ∑ y ∈ s, ‖w y‖ₑ * ‖K (x - y) - K (x - c)‖ₑ :=
          Finset.sum_congr rfl (fun z _ => by rw [enorm_smul, mul_comm])
  -- the bad-part estimate on the far set
  have hfar_bound : ∀ y : ℤ, y ∈ s →
      ∫⁻ x in {x : ℤ | x - c ∈ T}, ‖K (x - y) - K (x - c)‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal Ak := by
    intro y hy
    have hy' : a ≤ y ∧ y < b := (hs_mem y).mp hy
    by_cases hyc : y = c
    · rw [hyc]; simp
    · have hu_ne : y - c ≠ 0 := sub_ne_zero.mpr hyc
      have hu_le : (y - c).natAbs ≤ (b - a).toNat := by
        rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Int.toNat_of_nonneg (by omega)]
        rw [abs_le]; constructor <;> omega
      have hcongr : ∫⁻ x in {x : ℤ | x - c ∈ T}, ‖K (x - y) - K (x - c)‖ₑ
            ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          = ∫⁻ x in {x : ℤ | x - c ∈ T},
              ‖K ((x - c) - (y - c)) - K (x - c)‖ₑ
              ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
        apply setLIntegral_congr_fun (by measurability : MeasurableSet {x : ℤ | x - c ∈ T})
        intro x _
        change ‖K (x - y) - K (x - c)‖ₑ = ‖K ((x - c) - (y - c)) - K (x - c)‖ₑ
        rw [show x - y = (x - c) - (y - c) by ring]
      rw [hcongr, setLIntegral_sub_shift (fun z => ‖K (z - (y - c)) - K z‖ₑ) c T]
      refine le_trans (lintegral_mono_set ?_) (hker (y - c) hu_ne)
      intro z hz
      simp only [hT, Set.mem_ofPred_eq] at hz ⊢
      omega
  have hfar_eq : {x : ℤ | 2 * (b - a).toNat ≤ (x - c).natAbs} = {x : ℤ | x - c ∈ T} := by
    ext x; simp [hT]
  have hw_sum : ∑ y ∈ s, ‖w y‖ₑ
      = ∫⁻ y, ‖w y‖ₑ ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    rw [MeasureTheory.lintegral_count, tsum_eq_sum (s := s)]
    intro z hz
    rw [hwsupp z (fun h => hz (by rw [hs_mem]; exact h))]
    simp
  rw [hfar_eq]
  calc ∫⁻ x in {x : ℤ | x - c ∈ T}, ‖∑' y : ℤ, K (x - y) • w y‖ₑ
        ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ∫⁻ x in {x : ℤ | x - c ∈ T}, ∑ y ∈ s, ‖w y‖ₑ * ‖K (x - y) - K (x - c)‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
        setLIntegral_mono (by measurability) (fun x _ => hnorm x)
    _ = ∑ y ∈ s, ∫⁻ x in {x : ℤ | x - c ∈ T}, ‖w y‖ₑ * ‖K (x - y) - K (x - c)‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
        rw [lintegral_finsetSum s (fun b _ => by measurability)]
    _ = ∑ y ∈ s, ‖w y‖ₑ * ∫⁻ x in {x : ℤ | x - c ∈ T}, ‖K (x - y) - K (x - c)‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [lintegral_const_mul _
          (by measurability : Measurable (fun x : ℤ => ‖K (x - y) - K (x - c)‖ₑ))]
    _ ≤ ∑ y ∈ s, ‖w y‖ₑ * ENNReal.ofReal Ak := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul' le_rfl (hfar_bound y hy)
    _ = ENNReal.ofReal Ak * ∑ y ∈ s, ‖w y‖ₑ := by
        rw [← Finset.sum_mul, mul_comm]
    _ = ENNReal.ofReal Ak * ∫⁻ y, ‖w y‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
        rw [hw_sum]

end Commons.Analysis.DiscreteCZ