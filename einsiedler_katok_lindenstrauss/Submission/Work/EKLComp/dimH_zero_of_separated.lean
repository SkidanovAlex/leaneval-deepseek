import Mathlib
import Submission.Work.EKLComp.exists_cover_of_separated
import Submission.Work.EKLComp.sum_rpow_ediam_le
import Submission.Work.EKLComp.tendsto_exp_mul_rpow_exp

open MeasureTheory Filter Metric
open scoped ENNReal NNReal MeasureTheory

namespace Work.EKLComp

/-- `ENNReal.ofReal` of a quantity decaying like `exp (-a * f N)` tends to `0`. -/
theorem tendsto_ofReal_mul_exp_neg {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {c ε a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun N : ℕ => ENNReal.ofReal (c * (ε * Real.exp (-(a * f N))))) atTop (nhds 0) := by
  have h1 : Tendsto (fun N : ℕ => a * f N) atTop atTop := hf.const_mul_atTop ha
  have h2 : Tendsto (fun N : ℕ => Real.exp (-(a * f N))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atBot_iff.mpr h1)
  have h3 : Tendsto (fun N : ℕ => c * (ε * Real.exp (-(a * f N)))) atTop (nhds 0) := by
    have h4 : Tendsto (fun N : ℕ => ε * Real.exp (-(a * f N))) atTop (nhds 0) := by
      simpa using h2.const_mul ε
    simpa using h4.const_mul c
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h3

/-- Squeeze in `ℝ≥0∞`: a pointwise bound by `ofReal` of a real sequence tending to `0`. -/
theorem tendsto_zero_of_le_ofReal {u : ℕ → ENNReal} {C : ℕ → ℝ}
    (hC : Tendsto C atTop (nhds 0)) (h : ∀ N, u N ≤ ENNReal.ofReal (C N)) :
    Tendsto u atTop (nhds 0) := by
  have h1 : Tendsto (fun N => ENNReal.ofReal (C N)) atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hC
    simpa [Function.comp_def, ENNReal.ofReal_zero] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun N => bot_le) (fun N => h N)

/-- If all positive-dimensional Hausdorff measures of `S` vanish, then `dimH S = 0`. -/
theorem dimH_eq_zero_of_forall_hausdorffMeasure_zero {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {S : Set X}
    (h : ∀ d : ℝ≥0, 0 < d → μH[(d : ℝ)] S = 0) : dimH S = 0 := by
  refine le_antisymm ?_ (bot_le : (0 : ℝ≥0∞) ≤ dimH S)
  apply dimH_le
  intro d' hd'inf
  by_cases h0 : d' = 0
  · simp [h0]
  · exfalso
    have hpos : (0 : ℝ) < (d' : ℝ) := by
      have : (0 : ℝ≥0) < d' := pos_iff_ne_zero.mpr h0
      exact_mod_cast this
    rw [h d' (pos_iff_ne_zero.mpr h0)] at hd'inf
    exact ENNReal.zero_ne_top hd'inf

/-- **Main estimate.** Under the separation hypothesis, `S` has Hausdorff dimension `0`. -/
theorem dimH_zero_of_separated {S : Set (ℝ × ℝ)} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ b : ℝ, 0 < b → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ F : Finset (ℝ × ℝ), (F : Set (ℝ × ℝ)) ⊆ S →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → ε * Real.exp (-(3 * (N : ℝ))) ≤ dist x y) →
      (F.card : ℝ) < Real.exp (3 * b * (N : ℝ))) :
    dimH S = 0 := by
  refine dimH_eq_zero_of_forall_hausdorffMeasure_zero ?_
  intro d hd
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) / 2 := by linarith
  have hbd : (d : ℝ) / 2 < (d : ℝ) := by linarith
  obtain ⟨N₀, hN₀⟩ := h ((d : ℝ) / 2) hb
  -- For every `N`, a cover of `S` by `< exp (3 * (d/2) * (N + N₀))` balls of radius `ε exp (-3 (N+N₀))`.
  have hcover : ∀ N : ℕ, ∃ F : Finset (ℝ × ℝ),
      (F : Set (ℝ × ℝ)) ⊆ S ∧
        (F.card : ℝ) < Real.exp (3 * ((d : ℝ) / 2) * (((N + N₀ : ℕ) : ℝ))) ∧
        S ⊆ ⋃ a ∈ F, Metric.ball a (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ))))) := by
    intro N
    refine exists_cover_of_separated S ?_ (Real.exp_pos _) ?_
    · exact mul_pos hε (Real.exp_pos _)
    · intro F hFS hsep
      exact hN₀ (N + N₀) (Nat.le_add_left N₀ N) F hFS hsep
  choose F hFS hFcard hFcov using hcover
  -- the cover family, indexed by the elements of `F N`
  let t : (N : ℕ) → {a : ℝ × ℝ // a ∈ F N} → Set (ℝ × ℝ) := fun N a =>
    Metric.ball a.1 (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ)))))
  let r : ℕ → ℝ≥0∞ := fun N =>
    ENNReal.ofReal (2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ))))))
  have hf : Tendsto (fun N : ℕ => (((N + N₀ : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N₀)
  have hr : Tendsto r atTop (nhds 0) := by
    have := tendsto_ofReal_mul_exp_neg (c := 2) (ε := ε) (a := 3) hf (by norm_num)
    simpa [r] using this
  have ht : ∀ᶠ N in atTop, ∀ i, Metric.ediam (t N i) ≤ r N := by
    refine Eventually.of_forall fun N i => ?_
    show Metric.ediam (Metric.ball i.1 (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ)))))) ≤
      ENNReal.ofReal (2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ))))))
    refine Metric.ediam_le_of_forall_dist_le ?_
    intro x hx y hy
    rw [Metric.mem_ball] at hx hy
    have hcomm : dist i.1 y = dist y i.1 := dist_comm _ _
    have htri := dist_triangle x i.1 y
    linarith
  have hst : ∀ᶠ N in atTop, S ⊆ ⋃ i, t N i := by
    refine Eventually.of_forall fun N => ?_
    rw [Set.iUnion_subtype]
    exact hFcov N
  have hbound : ∀ N : ℕ, (∑ i : {a : ℝ × ℝ // a ∈ F N}, Metric.ediam (t N i) ^ (d : ℝ))
      ≤ ENNReal.ofReal (Real.exp (3 * ((d : ℝ) / 2) * (((N + N₀ : ℕ) : ℝ))) *
          (2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ)))))) ^ (d : ℝ)) := by
    intro N
    have hδnn : (0 : ℝ) ≤ 2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ))))) := by
      have := mul_pos hε (Real.exp_pos (-(3 * (((N + N₀ : ℕ) : ℝ)))))
      linarith
    have hstep : ∀ i, Metric.ediam (t N i) ≤
        ENNReal.ofReal (2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ)))))) := by
      intro i
      show Metric.ediam (Metric.ball i.1 (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ)))))) ≤
        ENNReal.ofReal (2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ))))))
      refine Metric.ediam_le_of_forall_dist_le ?_
      intro x hx y hy
      rw [Metric.mem_ball] at hx hy
      have hcomm : dist i.1 y = dist y i.1 := dist_comm _ _
      have htri := dist_triangle x i.1 y
      linarith
    have h2 := sum_rpow_ediam_le (u := t N) hδnn (le_of_lt hd') hstep
    have hcard : (Fintype.card {a : ℝ × ℝ // a ∈ F N} : ℝ) = ((F N).card : ℝ) := by
      rw [show Fintype.card {a : ℝ × ℝ // a ∈ F N} = (F N).card by simp]
    rw [hcard] at h2
    refine le_trans h2 (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_of_lt (hFcard N)) (Real.rpow_nonneg hδnn _)
  have hC : Tendsto (fun N : ℕ => Real.exp (3 * ((d : ℝ) / 2) * (((N + N₀ : ℕ) : ℝ))) *
      (2 * (ε * Real.exp (-(3 * (((N + N₀ : ℕ) : ℝ)))))) ^ (d : ℝ)) atTop (nhds 0) := by
    have := tendsto_exp_mul_rpow_exp (b := (d : ℝ) / 2) (d := (d : ℝ)) hf hε hbd
    simpa using this
  have htend : Tendsto (fun N : ℕ => ∑ i : {a : ℝ × ℝ // a ∈ F N},
      Metric.ediam (t N i) ^ (d : ℝ)) atTop (nhds 0) :=
    tendsto_zero_of_le_ofReal hC hbound
  refine le_antisymm ?_ bot_le
  calc μH[(d : ℝ)] S
      ≤ liminf (fun N : ℕ => ∑ i : {a : ℝ × ℝ // a ∈ F N}, Metric.ediam (t N i) ^ (d : ℝ)) atTop :=
        MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (d : ℝ) S r hr t ht hst
    _ = 0 := htend.liminf_eq

end Work.EKLComp
