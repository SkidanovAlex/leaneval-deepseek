/-
Copyright: work module for the Elgindi finite-time singularity project.

# Tonelli exchange for the Hardy operator with the radial weight `w(z)² z^{-β}`

This file proves `HarOp_lintegral_swap`: the double `lintegral` over the region
`{(z,s) | 0 < s ≤ z}` may be evaluated by Tonelli in either order, with the
radial weight `w(z)² z^{-β}` attached to the `z`-variable and the Hardy weight
`s^{β-1} f(s)²` attached to the `s`-variable.  The inner `z`-integral is left
unevaluated (unlike `Work.Elliptic.hardy_tonelli_swap`, which computes it).
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.hardy_op_L2_tonelli

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.FTS.EllipticEst

/-! ## The two weights, `Ioi 0`-truncated, and the region of integration -/

/-- The `Ioi 0`-truncated radial weight `z ↦ w(z)² z^{-β}`, as an `ℝ≥0∞`-valued function. -/
noncomputable def harSwapW (β : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))

/-- The `Ioi 0`-truncated Hardy weight `s ↦ s^{β-1} f(s)²`, as an `ℝ≥0∞`-valued function. -/
noncomputable def harSwapXi (β : ℝ) (f : ℝ → ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun s => ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))

/-- The region `{(z,s) | 0 < s ≤ z}` of the double integral. -/
def harSwapR : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}

theorem measurableSet_harSwapR : MeasurableSet harSwapR := by
  have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  exact h1.inter h2

theorem harSwapW_ne_top (β : ℝ) (z : ℝ) : harSwapW β z ≠ ⊤ := by
  unfold harSwapW
  by_cases h : z ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

theorem harSwapXi_ne_top (β : ℝ) (f : ℝ → ℝ) (s : ℝ) : harSwapXi β f s ≠ ⊤ := by
  unfold harSwapXi
  by_cases h : s ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-! ## Measurability -/

/-- The weight `z ↦ w(z)² z^{-β}` is continuous on `(0,∞)`. -/
theorem continuousOn_harSwapWeight (β : ℝ) :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z ^ (-β)) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun z hz => by
        simp only [Set.mem_Ioi] at hz
        positivity)
  exact (hw.pow 2).mul (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))

theorem aemeasurable_harSwapW (β : ℝ) : AEMeasurable (harSwapW β) volume := by
  unfold harSwapW
  refine Work.Elliptic.aemeasurable_indicator_restrict measurableSet_Ioi ?_
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (continuousOn_harSwapWeight β)).aemeasurable measurableSet_Ioi

theorem aemeasurable_harSwapXi {β : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    AEMeasurable (harSwapXi β f) volume := by
  unfold harSwapXi
  refine Work.Elliptic.aemeasurable_indicator_restrict measurableSet_Ioi ?_
  have h1 : AEMeasurable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioi 0)) :=
    hf.aestronglyMeasurable.aemeasurable
  have h2 : AEMeasurable (fun s : ℝ => s ^ (β - 1)) (volume.restrict (Set.Ioi 0)) :=
    (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx))).aemeasurable
      measurableSet_Ioi
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.mul h1)

/-! ## The Tonelli exchange -/

theorem HarOp_lintegral_swap (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))
      = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := by
  have _hβpos : (0 : ℝ) < β - 1 := by linarith
  have huncurry : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.w p.1) ^ 2 * p.1 ^ (-β)) *
        (Set.Ioc 0 p.1).indicator (harSwapXi β f) p.2) (volume.prod volume) := by
    have hpt : (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.w p.1) ^ 2 * p.1 ^ (-β)) *
          (Set.Ioc 0 p.1).indicator (harSwapXi β f) p.2)
        = fun p : ℝ × ℝ =>
            harSwapW β p.1 * harSwapXi β f p.2 * harSwapR.indicator (fun _ => 1) p := by
      funext p
      obtain ⟨z, s⟩ := p
      dsimp only
      by_cases h : s ∈ Set.Ioc 0 z
      · have hz : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le h.1 h.2
        have hmem : (z, s) ∈ harSwapR := h
        unfold harSwapW harSwapXi
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem h,
          Set.indicator_of_mem hmem, mul_one]
      · have hmem : (z, s) ∉ harSwapR := h
        unfold harSwapW harSwapXi
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hmem]
        simp
    rw [hpt]
    exact ((aemeasurable_harSwapW β).comp_fst.mul
        (aemeasurable_harSwapXi hf).comp_snd).mul
      (measurable_const.indicator measurableSet_harSwapR).aemeasurable
  have hinner : ∀ z : ℝ, (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))
      = ∫⁻ s in Set.Ioc 0 z, harSwapXi β f s := by
    intro z
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    unfold harSwapXi
    exact (Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs.1)
      (fun s => ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))).symm
  have h1 : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)))
      = ∫⁻ z, ∫⁻ s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (Set.Ioc 0 z).indicator (harSwapXi β f) s := by
    have h1a : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)))
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, harSwapXi β f s) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      rw [hinner z]
    have h1b : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, harSwapXi β f s))
        = ∫⁻ z, ∫⁻ s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            (Set.Ioc 0 z).indicator (harSwapXi β f) s := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hz, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator measurableSet_Ioc]
      · rw [Set.indicator_of_notMem hz]
        have hz0 : Set.Ioc 0 z = ∅ := Set.Ioc_eq_empty hz
        rw [hz0]
        simp
    exact h1a.trans h1b
  have h2 : (∫⁻ z, ∫⁻ s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (Set.Ioc 0 z).indicator (harSwapXi β f) s)
      = ∫⁻ s, ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (Set.Ioc 0 z).indicator (harSwapXi β f) s :=
    lintegral_lintegral_swap huncurry
  have h3 : (∫⁻ s, ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (Set.Ioc 0 z).indicator (harSwapXi β f) s)
      = ∫⁻ s in Set.Ioi 0, harSwapXi β f s *
          ∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hs]
      have hFeq : (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            (Set.Ioc 0 z).indicator (harSwapXi β f) s)
          = (Set.Ici s).indicator (fun z =>
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) * harSwapXi β f s) := by
        funext z
        by_cases hzs : s ≤ z
        · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 z from ⟨hs, hzs⟩),
              Set.indicator_of_mem (show z ∈ Set.Ici s from hzs)]
        · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hzs h.2),
              Set.indicator_of_notMem (show z ∉ Set.Ici s from hzs)]
          simp
      rw [hFeq, lintegral_indicator measurableSet_Ici]
      rw [show (∫⁻ z in Set.Ici s,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) * harSwapXi β f s)
            = ∫⁻ z in Set.Ici s,
              harSwapXi β f s * ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) from
          setLIntegral_congr_fun measurableSet_Ici (fun z _ => mul_comm _ _)]
      rw [lintegral_const_mul' (harSwapXi β f s)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
        (harSwapXi_ne_top β f s)]
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            (Set.Ioc 0 z).indicator (harSwapXi β f) s) = fun _ => (0 : ℝ≥0∞) := by
        funext z
        rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hs h.1)]
        simp
      rw [hzero]
      simp
  have h4 : (∫⁻ s in Set.Ioi 0, harSwapXi β f s *
        ∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
      = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    unfold harSwapXi
    rw [Set.indicator_of_mem hs]
  exact h1.trans (h2.trans (h3.trans h4))

end Work.FTS.EllipticEst
