import Submission.Work.Stems.StepI.SqueezeDefs

/-!
# The evaluation properties of the squeeze homotopy `squeezeK`

`Work.Stems.StepI.squeezeK` deforms the path `δ : x₀ → d₀` into the nested concatenation
`(δ * sg_w) * rev sg_w`.  This file records the four properties that make it a homotopy over the
base of the product `↥W × p⁻¹(d₀)`:

* `t = 0`: the identity path (`squeezeK_zero`);
* `t = 1`: the nested concatenation, in the shape `compFunK` (`squeezeK_one`);
* the endpoints are fixed: `s = 0` gives `δ 0 = x₀` (`squeezeK_at_zero`) and `s = 1` gives `d₀`,
  the latter using the path-field axiom `sg (w, 0) = d₀` (`squeezeK_at_one`).
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.Stems.StepI

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}

theorem squeezeK_zero (sg : ContinuousMap (↥W × unitInterval) X) (w : ↥W)
    (δ : ContinuousMap unitInterval X) (s : unitInterval) :
    squeezeK sg w δ 0 (s : ℝ) = δ s := by
  unfold squeezeK
  rw [if_pos (by rw [hA_zero]; exact s.2.2), hA_zero, div_one, clampI_coe_I]

theorem squeezeK_one (sg : ContinuousMap (↥W × unitInterval) X) (w : ↥W)
    (δ : ContinuousMap unitInterval X) (s : unitInterval) :
    squeezeK sg w δ 1 (s : ℝ) = compFunK sg w δ s := by
  unfold squeezeK compFunK
  rw [hA_one, hB_one]
  by_cases h1 : (s : ℝ) ≤ 1 / 4
  · rw [if_pos h1, if_pos (by linarith : (2 : ℝ) * (s : ℝ) ≤ 1),
      if_pos (by linarith : (4 : ℝ) * (s : ℝ) ≤ 1)]
    rw [show (s : ℝ) / (1 / 4) = 4 * (s : ℝ) by ring]
  · rw [if_neg h1]
    by_cases h2 : (s : ℝ) ≤ 1 / 2
    · rw [if_pos h2, if_pos (by linarith : (2 : ℝ) * (s : ℝ) ≤ 1),
        if_neg (by linarith : ¬ ((4 : ℝ) * (s : ℝ) ≤ 1))]
      rw [show (1 : ℝ) * (((s : ℝ) - 1 / 4) / (1 / 2 - 1 / 4)) = 4 * (s : ℝ) - 1 by
        rw [show (1 : ℝ) / 2 - 1 / 4 = 1 / 4 by norm_num]; ring]
    · rw [if_neg h2, if_neg (by linarith : ¬ ((2 : ℝ) * (s : ℝ) ≤ 1))]
      rw [show (1 : ℝ) * (1 - (((s : ℝ) - 1 / 2) / (1 - 1 / 2))) = 2 - 2 * (s : ℝ) by
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; ring]

theorem squeezeK_at_zero (sg : ContinuousMap (↥W × unitInterval) X) (w : ↥W)
    (δ : ContinuousMap unitInterval X) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    squeezeK sg w δ t 0 = δ 0 := by
  unfold squeezeK
  rw [if_pos (le_of_lt (hA_pos ht.2))]
  rw [show (0 : ℝ) / hA t = 0 by simp, clampI_zero]

theorem squeezeK_at_one (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (w : ↥W)
    (δ : ContinuousMap unitInterval X) (hδ : δ 1 = d₀) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    squeezeK sg w δ t 1 = d₀ := by
  unfold squeezeK
  by_cases h : (1 : ℝ) ≤ hA t
  · rw [if_pos h]
    have ht1 : hA t = 1 := le_antisymm (hA_le_one ht.1) h
    rw [ht1, div_one, clampI_one, hδ]
  · rw [if_neg h]
    by_cases h2 : (1 : ℝ) ≤ hB t
    · have ht0 : hB t = 1 := le_antisymm (hB_le_one ht.1) h2
      have htz : t = 0 := by unfold hB at ht0; linarith
      exact absurd (by rw [htz, hA_zero] : (1 : ℝ) ≤ hA t) h
    · rw [if_neg h2]
      have harg : t * (1 - ((1 - hB t) / (1 - hB t))) = 0 := by
        rw [div_self (ne_of_gt (sub_pos.mpr (not_le.mp h2))), sub_self, mul_zero]
      rw [harg, clampI_zero]
      exact hsg0 w

theorem squeezeK_evals {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}
    (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) :
    (∀ (w : ↥W) (δ : ContinuousMap unitInterval X) (s : unitInterval),
        Work.Stems.StepI.squeezeK sg w δ 0 (s : ℝ) = δ s) ∧
    (∀ (w : ↥W) (δ : ContinuousMap unitInterval X) (s : unitInterval),
        Work.Stems.StepI.squeezeK sg w δ 1 (s : ℝ) = Work.Stems.StepI.compFunK sg w δ s) ∧
    (∀ (w : ↥W) (δ : ContinuousMap unitInterval X) (t : ℝ),
        t ∈ Set.Icc 0 1 → Work.Stems.StepI.squeezeK sg w δ t 0 = δ 0) ∧
    (∀ (w : ↥W) (δ : ContinuousMap unitInterval X), δ 1 = d₀ →
        ∀ (t : ℝ), t ∈ Set.Icc 0 1 → Work.Stems.StepI.squeezeK sg w δ t 1 = d₀) :=
  ⟨fun w δ s => squeezeK_zero sg w δ s,
   fun w δ s => squeezeK_one sg w δ s,
   fun w δ t ht => squeezeK_at_zero sg w δ ht,
   fun w δ hδ t ht => squeezeK_at_one sg hsg0 w δ hδ ht⟩

end

end Work.Stems.StepI
