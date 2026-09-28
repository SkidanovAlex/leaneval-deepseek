import Submission.Work.Stems.StepI.SqueezeDefs
import Submission.Work.Stems.StepI.continuous_squeezeHUnc

/-!
# The evaluation properties of the squeeze homotopy `squeezeH`

`Work.Stems.StepI.squeezeH` deforms the path `γ` into the nested concatenation
`(γ * rev sg_w) * sg_w`.  This file records the four properties that make it a *homotopy over the
base*:

* at `t = 0` it is the identity path (`squeezeH_zero`);
* at `t = 1` it is the nested concatenation, in the shape `compFun` (`squeezeH_one`);
* for every `t` its endpoints are fixed: `s = 0` gives `x₀` and `s = 1` gives the base point
  `w = q(1)` of the path (`squeezeH_at_zero`, `squeezeH_at_one`).

The endpoint `s = 1` needs the path-field axiom `sg (w, 1) = w`.
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.Stems.StepI

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X}

theorem squeezeH_zero (sg : ContinuousMap (↥W × unitInterval) X)
    (z : ↥((evalOne X x₀) ⁻¹' W)) (s : unitInterval) :
    squeezeH sg z 0 (s : ℝ) = cmOf z s := by
  unfold squeezeH
  rw [if_pos (by rw [hA_zero]; exact s.2.2), hA_zero, div_one, clampI_coe_I]

theorem squeezeH_one (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W)) (s : unitInterval) :
    squeezeH sg z 1 (s : ℝ) = compFun sg (wOf z) (cmOf z) s := by
  unfold squeezeH compFun
  rw [hA_one, hB_one]
  by_cases h1 : (s : ℝ) ≤ 1 / 4
  · rw [if_pos h1, if_pos (by linarith : (2 : ℝ) * (s : ℝ) ≤ 1),
      if_pos (by linarith : (4 : ℝ) * (s : ℝ) ≤ 1)]
    rw [show (s : ℝ) / (1 / 4) = 4 * (s : ℝ) by ring]
  · rw [if_neg h1]
    by_cases h2 : (s : ℝ) ≤ 1 / 2
    · rw [if_pos h2, if_pos (by linarith : (2 : ℝ) * (s : ℝ) ≤ 1),
        if_neg (by linarith : ¬ ((4 : ℝ) * (s : ℝ) ≤ 1))]
      rw [show (1 : ℝ) - 1 * (((s : ℝ) - 1 / 4) / (1 / 2 - 1 / 4)) = 2 - 4 * (s : ℝ) by
        rw [show (1 : ℝ) / 2 - 1 / 4 = 1 / 4 by norm_num]; ring]
    · rw [if_neg h2, if_neg (by linarith : ¬ ((2 : ℝ) * (s : ℝ) ≤ 1))]
      rw [show (1 : ℝ) - 1 * (1 - (((s : ℝ) - 1 / 2) / (1 - 1 / 2))) = 2 * (s : ℝ) - 1 by
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; ring]

theorem squeezeH_at_zero (sg : ContinuousMap (↥W × unitInterval) X)
    (z : ↥((evalOne X x₀) ⁻¹' W)) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    squeezeH sg z t 0 = x₀ := by
  unfold squeezeH
  rw [if_pos (le_of_lt (hA_pos ht.2))]
  rw [show (0 : ℝ) / hA t = 0 by simp, clampI_zero, cmOf_zero]

theorem squeezeH_at_one (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W)) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    squeezeH sg z t 1 = (wOf z : X) := by
  unfold squeezeH
  by_cases h : (1 : ℝ) ≤ hA t
  · rw [if_pos h]
    have ht1 : hA t = 1 := le_antisymm (hA_le_one ht.1) h
    rw [ht1, div_one, clampI_one, cmOf_one]
  · rw [if_neg h]
    by_cases h2 : (1 : ℝ) ≤ hB t
    · have ht0 : hB t = 1 := le_antisymm (hB_le_one ht.1) h2
      have htz : t = 0 := by unfold hB at ht0; linarith
      exact absurd (by rw [htz, hA_zero] : (1 : ℝ) ≤ hA t) h
    · rw [if_neg h2]
      rw [div_self (ne_of_gt (sub_pos.mpr (not_le.mp h2))), sub_self, mul_zero, sub_zero,
        clampI_one]
      exact hsg1 (wOf z)

theorem squeezeH_evals {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X}
    (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    (∀ (z : ↥((Work.StemsB.evalOne X x₀) ⁻¹' W)) (s : unitInterval),
        Work.Stems.StepI.squeezeH sg z 0 (s : ℝ) = Work.Stems.StepI.cmOf z s) ∧
    (∀ (z : ↥((Work.StemsB.evalOne X x₀) ⁻¹' W)) (s : unitInterval),
        Work.Stems.StepI.squeezeH sg z 1 (s : ℝ) =
          Work.Stems.StepI.compFun sg (Work.Stems.StepI.wOf z) (Work.Stems.StepI.cmOf z) s) ∧
    (∀ (z : ↥((Work.StemsB.evalOne X x₀) ⁻¹' W)) (t : ℝ),
        t ∈ Set.Icc 0 1 → Work.Stems.StepI.squeezeH sg z t 0 = x₀) ∧
    (∀ (z : ↥((Work.StemsB.evalOne X x₀) ⁻¹' W)) (t : ℝ),
        t ∈ Set.Icc 0 1 → Work.Stems.StepI.squeezeH sg z t 1 = (Work.Stems.StepI.wOf z : X)) :=
  ⟨fun z s => squeezeH_zero sg z s,
   fun z s => squeezeH_one sg hsg1 z s,
   fun z t ht => squeezeH_at_zero sg z ht,
   fun z t ht => squeezeH_at_one sg hsg1 z ht⟩

end

end Work.Stems.StepI
