import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.radGreen_modeEnergy_interval

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem radGreen_source_facts_of_compactSupport {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hsupp : ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    (∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    ∧ (∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)
    ∧ MeasureTheory.IntegrableOn (fun z : ℝ => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  obtain ⟨a, b, ha, hsup⟩ := hsupp
  -- Enlarge the supporting interval so that its left endpoint is `≤` its right endpoint.  (If
  -- `b < a` then `Icc a b = ∅` and the source vanishes identically, so this loses nothing.)
  have hab : a ≤ max b a := le_max_right b a
  have hsup' : ∀ t : ℝ, t ∉ Set.Icc a (max b a) → c t = 0 := fun t ht =>
    hsup t fun h => ht ⟨h.1, le_trans h.2 (le_max_left b a)⟩
  -- The source is globally bounded: it vanishes off the compact set `Icc a (max b a)`.
  have hsub : Set.Icc a (max b a) ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub)
  have hMnn : (0 : ℝ) ≤ max C 0 := le_max_right C 0
  have hMb : ∀ t : ℝ, |c t| ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc a (max b a)
    · refine le_trans ?_ (le_max_left C 0)
      simpa only [Real.norm_eq_abs] using hC t ht
    · rw [hsup' t ht, abs_zero]
      exact hMnn
  -- The power factor `t ↦ t ^ e` is continuous on `(0,∞)` for every real exponent.
  have hrpow : ∀ e : ℝ, ContinuousOn (fun z : ℝ => z ^ e) (Set.Ioi 0) := fun e =>
    (Work.FTS.ClassC.contDiffOn_rpow_Ioi e 0).continuousOn
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
      (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
    exact pow_ne_zero 2 (ne_of_gt hz)
  refine ⟨Work.FTS.ClassCHon.decay_of_support hMnn hMb hsup',
    Work.FTS.ClassCHon.vanishing_of_support ha hMnn hMb hsup', ?_, ?_, ?_, ?_⟩
  · refine (Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      (hc.mul (hrpow _)) (fun z hz => by
        simp only [Pi.mul_apply]
        rw [hsup' z hz, zero_mul])).mono_set ?_
    intro z hz
    exact hz.1
  · refine (Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      (hc.mul (hrpow _)) (fun z hz => by
        simp only [Pi.mul_apply]
        rw [hsup' z hz, zero_mul])).mono_set ?_
    intro z hz
    exact hz.1
  · refine (Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      (hc.mul (hrpow _)) (fun z hz => by
        simp only [Pi.mul_apply]
        rw [hsup' z hz, zero_mul])).mono_set ?_
    exact Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)
  · refine Work.FTS.ClassCHon.integrableOn_Ioi_of_contOn_of_support ha hab
      ((hc.pow 2).mul hw) ?_
    intro z hz
    show (c z) ^ 2 * (Work.Spaces.w z) ^ 2 = 0
    rw [hsup' z hz]
    ring

end Work.FTS.PhiStar.Honesty
