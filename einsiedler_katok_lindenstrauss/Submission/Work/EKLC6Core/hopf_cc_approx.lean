import Mathlib
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLC6Core.hopf_cc_approx`

Continuity of the Hopf/`C_c` approximation step in component C6: for any Borel probability
measure `μ` on `X₃` and any measurable `C ⊆ X₃`, the indicator of `C` is approximated in `L¹(μ)`
by a continuous compactly supported `f` with `0 ≤ f ≤ 1`.

The proof uses the density of compactly supported continuous functions in `L¹(μ)`
(`MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le`, available because `X₃` is
a Polish, hence σ-compact locally compact space and every finite Borel measure on it is regular),
followed by clamping the approximant to `[0,1]` — which can only decrease the `L¹` distance to an
indicator function.
-/

namespace Work.EKLC6Core

open MeasureTheory

/-- Clamping a real number `t` to `[0,1]` does not increase its distance to any point `c` of
`[0,1]`. -/
lemma abs_clamp_sub_le {c t : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    |max 0 (min 1 t) - c| ≤ |t - c| := by
  obtain ⟨hc0, hc1⟩ := hc
  by_cases ht : t ≤ 0
  · have hclamp : max 0 (min 1 t) = 0 := by
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    rw [hclamp, zero_sub, abs_neg, abs_of_nonneg hc0, abs_of_nonpos (by linarith)]
    linarith
  · push_neg at ht
    by_cases ht1 : t ≤ 1
    · have hclamp : max 0 (min 1 t) = t := by
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      rw [hclamp]
    · push_neg at ht1
      have hclamp : max 0 (min 1 t) = 1 := by
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      rw [hclamp, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- Clamping a compactly supported continuous function to `[0,1]` keeps it compactly supported
(it only shrinks the support). -/
lemma hasCompactSupport_clamp {α : Type*} [TopologicalSpace α] {g : α → ℝ}
    (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => max 0 (min 1 (g x))) :=
  hg.mono (by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hgx
    exact hx (by rw [hgx]; simp))

theorem hopf_cc_approx (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] {C : Set Work.EKLContract.X3}
    (hC : MeasurableSet C) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Work.EKLContract.X3 → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∫ x, |f x - C.indicator (fun _ => (1 : ℝ)) x| ∂μ ≤ ε := by
  have hf0_int : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hC
  obtain ⟨g, hg_supp, hg_le, hg_cont, hg_mem⟩ :=
    hf0_int.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨fun x => max 0 (min 1 (g x)), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.max (continuous_const.min hg_cont)
  · exact hasCompactSupport_clamp hg_supp
  · intro x
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · have hpt : ∀ x, |max 0 (min 1 (g x)) - C.indicator (fun _ => (1 : ℝ)) x|
        ≤ |g x - C.indicator (fun _ => (1 : ℝ)) x| := by
      intro x
      refine abs_clamp_sub_le ?_
      by_cases hx : x ∈ C
      · rw [Set.indicator_of_mem hx]; exact ⟨zero_le_one, le_refl 1⟩
      · rw [Set.indicator_of_notMem hx]; exact ⟨le_refl 0, zero_le_one⟩
    have hIntg : Integrable (fun x => |g x - C.indicator (fun _ => (1 : ℝ)) x|) μ := by
      have := (hg_mem.sub hf0_int).abs
      simpa only [Pi.sub_apply] using this
    have hstep : ∫ x, |max 0 (min 1 (g x)) - C.indicator (fun _ => (1 : ℝ)) x| ∂μ
        ≤ ∫ x, |g x - C.indicator (fun _ => (1 : ℝ)) x| ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hIntg
        (Filter.Eventually.of_forall hpt)
    refine hstep.trans ?_
    rw [show (∫ x, |g x - C.indicator (fun _ => (1 : ℝ)) x| ∂μ)
        = ∫ x, ‖C.indicator (fun _ => (1 : ℝ)) x - g x‖ ∂μ from ?_]
    · exact hg_le
    · apply integral_congr_ae
      filter_upwards with x
      rw [abs_sub_comm, Real.norm_eq_abs]

end Work.EKLC6Core
