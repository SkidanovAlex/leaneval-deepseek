import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped Interval

namespace Commons.Analysis.Integral

/-- Integrals over a larger interval of the indicator of a sub-interval reduce to the
integral over the sub-interval.  No integrability hypothesis is needed. -/
lemma intervalIntegral_indicator_Icc_eq {F : ℝ → ℝ} {c d a b : ℝ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    (∫ β in c..d, (Set.Icc a b).indicator F β) = ∫ β in a..b, F β := by
  have hcd : c ≤ d := le_trans hca (le_trans hab hbd)
  rw [intervalIntegral.integral_of_le hcd, setIntegral_indicator measurableSet_Icc]
  rcases lt_or_eq_of_le hca with hlt | heq
  · have hset : Set.Ioc c d ∩ Set.Icc a b = Set.Icc a b := by
      ext x; constructor
      · intro hx; exact hx.2
      · intro hx
        exact ⟨⟨lt_of_lt_of_le hlt hx.1, le_trans hx.2 hbd⟩, hx⟩
    rw [hset, intervalIntegral.integral_of_le hab]
    exact (setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))).symm
  · have hset : Set.Ioc c d ∩ Set.Icc a b = Set.Ioc a b := by
      ext x; constructor
      · intro hx
        exact ⟨heq ▸ hx.1.1, hx.2.2⟩
      · intro hx
        exact ⟨⟨heq.symm ▸ hx.1, le_trans hx.2 hbd⟩, ⟨le_of_lt hx.1, hx.2⟩⟩
    rw [hset, intervalIntegral.integral_of_le hab]

theorem layer_cake_interval_integral (F : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (R : ℕ)
    (hF : MeasureTheory.IntegrableOn F (Set.Icc (-C) C)) :
    (∑ r ∈ Finset.Icc 1 R, ∫ β in (-(C / (r : ℝ)))..(C / (r : ℝ)), F β)
      = ∫ β in (-C)..C, F β *
          (((Finset.Icc 1 R).filter (fun r : ℕ => (r : ℝ) * |β| ≤ C)).card : ℝ) := by
  have hC' : -C ≤ C := by linarith
  set g : ℕ → ℝ → ℝ := fun r β => F β * (if (r : ℝ) * |β| ≤ C then (1 : ℝ) else 0)
    with hg_def
  have hF_Ioc : Integrable F (volume.restrict (Set.Ioc (-C) C)) :=
    hF.mono_set Set.Ioc_subset_Icc_self
  have hg_eq : ∀ r ∈ Finset.Icc 1 R,
      g r = (Set.Icc (-(C / (r : ℝ))) (C / (r : ℝ))).indicator F := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1
    funext β
    simp only [hg_def]
    by_cases h : (r : ℝ) * |β| ≤ C
    · have hle : |β| ≤ C / (r : ℝ) := by
        rw [le_div_iff₀ hrpos]; rwa [mul_comm]
      have hmem : β ∈ Set.Icc (-(C / (r : ℝ))) (C / (r : ℝ)) := by
        rw [Set.mem_Icc]
        exact abs_le.mp hle
      rw [Set.indicator_of_mem hmem]
      simp [h]
    · have hmem : β ∉ Set.Icc (-(C / (r : ℝ))) (C / (r : ℝ)) := by
        intro hmem
        rw [Set.mem_Icc] at hmem
        exact h (by
          have hle : |β| ≤ C / (r : ℝ) := abs_le.mpr hmem
          have h2 := (le_div_iff₀ hrpos).mp hle
          rwa [mul_comm] at h2)
      rw [Set.indicator_of_notMem hmem]
      simp [h]
  have hInd : ∀ r ∈ Finset.Icc 1 R,
      (∫ β in (-C)..C, g r β) = ∫ β in (-(C / (r : ℝ)))..(C / (r : ℝ)), F β := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1
    have hCdiv_le : C / (r : ℝ) ≤ C := by
      rw [div_le_iff₀ hrpos]; nlinarith [hC]
    have hneg : -C ≤ -(C / (r : ℝ)) := by linarith
    have hab : -(C / (r : ℝ)) ≤ C / (r : ℝ) := by
      have : 0 ≤ C / (r : ℝ) := div_nonneg hC (le_of_lt hrpos)
      linarith
    rw [hg_eq r hr]
    exact intervalIntegral_indicator_Icc_eq hneg hab hCdiv_le
  have hint_g : ∀ r ∈ Finset.Icc 1 R, IntervalIntegrable (g r) volume (-C) C := by
    intro r hr
    have hgint : IntegrableOn (g r) (Set.Ioc (-C) C) volume := by
      rw [hg_eq r hr]; exact hF_Ioc.indicator measurableSet_Icc
    rw [intervalIntegrable_iff, uIoc_of_le hC']
    exact hgint
  have hsum_pt : ∀ β : ℝ,
      (∑ r ∈ Finset.Icc 1 R, g r β)
        = F β * (((Finset.Icc 1 R).filter (fun r : ℕ => (r : ℝ) * |β| ≤ C)).card : ℝ) := by
    intro β
    have h1 : (∑ r ∈ Finset.Icc 1 R, g r β)
        = F β * ∑ r ∈ Finset.Icc 1 R,
            (if (r : ℝ) * |β| ≤ C then (1 : ℝ) else 0) := by
      simp only [hg_def]
      rw [Finset.mul_sum]
    have h2 : (((Finset.Icc 1 R).filter (fun r : ℕ => (r : ℝ) * |β| ≤ C)).card : ℝ)
        = ∑ r ∈ Finset.Icc 1 R,
            (if (r : ℝ) * |β| ≤ C then (1 : ℝ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [h1, ← h2]
  rw [Finset.sum_congr rfl (fun r hr => (hInd r hr).symm)]
  rw [← intervalIntegral.integral_finsetSum (μ := volume) (a := -C) (b := C) (f := g) hint_g]
  exact intervalIntegral.integral_congr (fun β _ => hsum_pt β)

end Commons.Analysis.Integral