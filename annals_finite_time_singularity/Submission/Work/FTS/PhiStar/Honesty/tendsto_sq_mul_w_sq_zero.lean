import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

/-- The square of the radial weight `w(z) = (1+z)²/z²` in closed form.
Because Lean's division is total, this holds for every `t` (both sides vanish at `t = 0`). -/
private lemma w_sq_eq (t : ℝ) : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  ring_nf

/-- `(w t)² = ((1+t)/t)⁴`; the form in which the factor is genuinely continuous on `(0,∞)`. -/
private lemma div_w_sq_eq (t : ℝ) : ((1 + t) / t) ^ 4 = (Work.Spaces.w t) ^ 2 := by
  rw [w_sq_eq, div_pow]

/-- Pointwise domination on the near field `(0,1]`: `w(t)² ≤ 16/t⁴` there. -/
private lemma sq_mul_w_sq_le_near {x t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    x ^ 2 * (Work.Spaces.w t) ^ 2 ≤ 16 * (x ^ 2 / t ^ 4) := by
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht0 4
  have h1t : (1 + t) ^ 4 ≤ 16 := by
    have hle : 1 + t ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + t := by linarith
    calc (1 + t) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 hle 4
      _ = 16 := by norm_num
  have hw : x ^ 2 * (Work.Spaces.w t) ^ 2 = (x ^ 2 * (1 + t) ^ 4) / t ^ 4 := by
    rw [w_sq_eq, mul_div_assoc]
  rw [hw, ← mul_div_assoc, div_le_div_iff_of_pos_right ht4]
  calc x ^ 2 * (1 + t) ^ 4 ≤ x ^ 2 * 16 := mul_le_mul_of_nonneg_left h1t (sq_nonneg x)
    _ = 16 * x ^ 2 := by ring

/-- Pointwise domination on the far field `[1,∞)`: `w(t)² ≤ 16` there. -/
private lemma sq_mul_w_sq_le_far {x t : ℝ} (ht : 1 ≤ t) :
    x ^ 2 * (Work.Spaces.w t) ^ 2 ≤ 16 * x ^ 2 := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht0 4
  have hle : (1 + t) ^ 4 ≤ 16 * t ^ 4 := by
    have h1 : 1 + t ≤ 2 * t := by linarith
    have h0 : (0 : ℝ) ≤ 1 + t := by linarith
    calc (1 + t) ^ 4 ≤ (2 * t) ^ 4 := pow_le_pow_left₀ h0 h1 4
      _ = 16 * t ^ 4 := by ring
  have hw16 : (Work.Spaces.w t) ^ 2 ≤ 16 := by
    rw [w_sq_eq, div_le_iff₀ ht4]
    exact hle
  calc x ^ 2 * (Work.Spaces.w t) ^ 2 ≤ x ^ 2 * 16 :=
        mul_le_mul_of_nonneg_left hw16 (sq_nonneg x)
    _ = 16 * x ^ 2 := by ring

/-- The half-line `(0,∞)` is the (a.e. equal) disjoint union `(0,1) ∪ (1,∞)`. -/
private lemma Ioi_zero_ae_eq_Ioo_union_Ioi :
    Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  have h₁ : Set.Ioi (0 : ℝ) \ (Set.Ioo 0 1 ∪ Set.Ioi 1) = {1} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, hnot⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hnot (Or.inl ⟨h0, h⟩)
      · exact hnot (Or.inr h)
    · rintro rfl
      norm_num
  have h₂ : (Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi 1) \ Set.Ioi 0 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx | hx, hx0⟩
    · exact hx0 hx.1
    · exact hx0 (Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp hx)))
  exact ⟨by rw [h₁, measure_singleton], by rw [h₂, measure_empty]⟩

theorem tendsto_sq_mul_w_sq_zero {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (h1 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (h2 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1))
    (h1c : Filter.Tendsto (fun n => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4) Filter.atTop (nhds 0))
    (h2c : Filter.Tendsto (fun n => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop (nhds 0) := by
  -- ### Integrability of the weighted square on the two halves
  have hF1 : ∀ n, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioo (0:ℝ) 1) := by
    intro n
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
      have hg : AEStronglyMeasurable (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4)
          (volume.restrict (Set.Ioo (0:ℝ) 1)) := (h1 n).aestronglyMeasurable
      have hc : AEStronglyMeasurable (fun t : ℝ => (1 + t) ^ 4)
          (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
        ((continuous_const.add continuous_id).pow 4).aestronglyMeasurable
      refine (hg.mul hc).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t _
      show ((c_ n t - c t) ^ 2 / t ^ 4) * (1 + t) ^ 4
        = (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2
      rw [w_sq_eq]
      ring_nf
    refine Integrable.mono' (g := fun t : ℝ => 16 * ((c_ n t - c t) ^ 2 / t ^ 4)) ?_ hmeas ?_
    · exact (h1 n).const_mul 16
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact sq_mul_w_sq_le_near ht.1 ht.2.le
  have hF2 : ∀ n, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi (1:ℝ)) := by
    intro n
    have hcont : ContinuousOn (fun t : ℝ => ((1 + t) / t) ^ 4) (Set.Ioi (1:ℝ)) := by
      apply ContinuousOn.pow
      apply ContinuousOn.div
      · exact (continuous_const.add continuous_id).continuousOn
      · exact continuous_id.continuousOn
      · intro t ht
        exact ne_of_gt (lt_trans one_pos ht)
    have hc : AEStronglyMeasurable (fun t : ℝ => ((1 + t) / t) ^ 4)
        (volume.restrict (Set.Ioi (1:ℝ))) := hcont.aestronglyMeasurable measurableSet_Ioi
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (volume.restrict (Set.Ioi (1:ℝ))) := by
      refine ((h2 n).aestronglyMeasurable.mul hc).congr ?_
      filter_upwards with t
      show (c_ n t - c t) ^ 2 * ((1 + t) / t) ^ 4
        = (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2
      rw [div_w_sq_eq]
    refine Integrable.mono' (g := fun t : ℝ => 16 * (c_ n t - c t) ^ 2) ?_ hmeas ?_
    · exact (h2 n).const_mul 16
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact sq_mul_w_sq_le_far ht.le
  -- ### Splitting the half-line
  have hdisj : Disjoint (Set.Ioo (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
    rw [disjoint_left]
    intro x hx1 hx2
    exact absurd hx2 (not_lt.mpr hx1.2.le)
  have hsplit : ∀ n, (∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      = (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        + (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
    intro n
    rw [MeasureTheory.setIntegral_congr_set Ioi_zero_ae_eq_Ioo_union_Ioi]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi (hF1 n) (hF2 n)
  -- ### The two half-line bounds
  have hb1 : ∀ n, (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      ≤ 16 * ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4 := by
    intro n
    have h := MeasureTheory.setIntegral_mono_of_nonneg
      (s := Set.Ioo (0:ℝ) 1)
      (f := fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (g := fun t : ℝ => 16 * ((c_ n t - c t) ^ 2 / t ^ 4))
      (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun t ht => sq_mul_w_sq_le_near ht.1 ht.2.le)
      ((h1 n).const_mul 16)
    calc (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        ≤ ∫ t in Set.Ioo (0:ℝ) 1, 16 * ((c_ n t - c t) ^ 2 / t ^ 4) := h
      _ = 16 * ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4 := by
          rw [MeasureTheory.integral_const_mul]
  have hb2 : ∀ n, (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      ≤ 16 * ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 := by
    intro n
    have h := MeasureTheory.setIntegral_mono_of_nonneg
      (s := Set.Ioi (1:ℝ))
      (f := fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (g := fun t : ℝ => 16 * (c_ n t - c t) ^ 2)
      (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun t ht => sq_mul_w_sq_le_far ht.le)
      ((h2 n).const_mul 16)
    calc (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        ≤ ∫ t in Set.Ioi (1:ℝ), 16 * (c_ n t - c t) ^ 2 := h
      _ = 16 * ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
  -- ### The majorant sequence tends to `0`
  have hupper : Filter.Tendsto
      (fun n => 16 * (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
        + 16 * (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)) Filter.atTop (nhds 0) := by
    have h := (h1c.const_mul (16:ℝ)).add (h2c.const_mul (16:ℝ))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0:ℝ)) (f := Filter.atTop)) hupper ?_ ?_
  · intro n
    show (0:ℝ) ≤ ∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2
    rw [hsplit n]
    exact add_nonneg
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  · intro n
    show (∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        ≤ 16 * (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
          + 16 * (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)
    rw [hsplit n]
    linarith [hb1 n, hb2 n]

end Work.FTS.PhiStar.Honesty
