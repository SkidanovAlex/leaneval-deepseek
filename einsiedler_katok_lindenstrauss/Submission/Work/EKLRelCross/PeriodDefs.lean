import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLC7.PerSub

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Work.EKLContract

/-- `PerSet ν i j hij x` is the set of parameters `τ : ℝ` for which the measure `ν x` on
`SL₃(ℝ)` is invariant under right translation by the root element `u_ij(τ)`.

Mathematically (for `x` in the conull domain of a leafwise system, where `ν x` is Radon and
carried by `U_ij`) this set is the *period set* (stabiliser) of `ν x` inside the one-parameter
root group `U_ij ≅ ℝ`; it is a closed additive subgroup of `ℝ`. -/
def PerSet (ν : X3 → Measure SL3) (i j : Fin 3) (hij : i ≠ j) (x : X3) : Set ℝ :=
  {τ : ℝ | (ν x).map (fun g : SL3 => g * uij hij τ) = ν x}

variable {ν : X3 → Measure SL3} {i j : Fin 3} {hij : i ≠ j} {x : X3}

/-- `0` is always a period: `u_ij(0) = 1`. -/
theorem zero_mem_PerSet (ν : X3 → Measure SL3) (i j : Fin 3) (hij : i ≠ j) (x : X3) :
    (0 : ℝ) ∈ PerSet ν i j hij x := by
  simp only [PerSet, Set.mem_ofPred_eq]
  have h1 : (fun g : SL3 => g * uij hij 0) = id := by
    funext g; simp [Work.EKLC7.uij_zero hij]
  rw [h1, Measure.map_id]

/-- The period set is closed under addition. -/
theorem add_mem_PerSet {τ σ : ℝ} (hτ : τ ∈ PerSet ν i j hij x)
    (hσ : σ ∈ PerSet ν i j hij x) : τ + σ ∈ PerSet ν i j hij x := by
  simp only [PerSet, Set.mem_setOf_eq] at hτ hσ ⊢
  have key : (fun g : SL3 => g * uij hij (τ + σ))
      = (fun g : SL3 => g * uij hij σ) ∘ (fun g : SL3 => g * uij hij τ) := by
    funext g
    simp only [Function.comp_apply]
    rw [Work.EKLC7.uij_add, mul_assoc]
  rw [key, ← Measure.map_map (Work.EKLC7.measurable_mulRight_uij hij σ) (Work.EKLC7.measurable_mulRight_uij hij τ),
    hτ, hσ]

/-- The period set is closed under negation. -/
theorem neg_mem_PerSet {τ : ℝ} (hτ : τ ∈ PerSet ν i j hij x) :
    -τ ∈ PerSet ν i j hij x := by
  simp only [PerSet, Set.mem_setOf_eq] at hτ ⊢
  have hcomp : (fun g : SL3 => g * uij hij (-τ)) ∘ (fun g : SL3 => g * uij hij τ) = id := by
    funext g
    simp only [Function.comp_apply, id_eq]
    rw [mul_assoc, ← Work.EKLC7.uij_add hij τ (-τ), add_neg_cancel, Work.EKLC7.uij_zero hij, mul_one]
  have h := Measure.map_map (μ := ν x)
    (g := fun g : SL3 => g * uij hij (-τ)) (f := fun g : SL3 => g * uij hij τ)
    (Work.EKLC7.measurable_mulRight_uij hij (-τ)) (Work.EKLC7.measurable_mulRight_uij hij τ)
  rw [hτ, hcomp, Measure.map_id] at h
  exact h

/-- **Continuity of the translate-integral.**  For a Radon measure `ν` on `SL₃(ℝ)` and a
compactly supported continuous `f`, the function `τ ↦ ∫ g, f (g * u_ij(τ)) ∂ν` is continuous.
This is the analytic input behind the closedness of `PerSet` and behind the measurability of the
condition "`ν x` has a period in `[a,b]`". -/
theorem continuous_integral_translate_uij (ν : Measure SL3) [IsFiniteMeasureOnCompacts ν]
    (f : CompactlySupportedContinuousMap SL3 ℝ) {i j : Fin 3} (hij : i ≠ j) :
    Continuous (fun τ : ℝ => ∫ g, f (g * uij hij τ) ∂ν) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g : SL3, ‖f g‖ ≤ C := by
    have hb := (f.hasCompactSupport.isCompact_range f.continuous).isBounded
    rw [isBounded_iff_forall_norm_le] at hb
    obtain ⟨D, hD⟩ := hb
    exact ⟨D, fun g => hD (f g) ⟨g, rfl⟩⟩
  set R : ℝ := |s₀| + 1 with hRdef
  set K₀ : Set SL3 := (fun p : SL3 × SL3 => p.1 * p.2) ''
    (tsupport (f : SL3 → ℝ) ×ˢ (uij hij '' Set.Icc (-R) R)) with hK₀def
  have hK₀c : IsCompact K₀ := by
    rw [hK₀def]
    exact ((f.hasCompactSupport.isCompact.prod
      (isCompact_Icc.image (Work.EKLC7.continuous_uij hij))).image continuous_mul)
  have hfin : ν K₀ ≠ ⊤ := (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK₀c).ne
  have hbound_int : Integrable (K₀.indicator (fun _ : SL3 => C)) ν :=
    (integrable_indicator_iff hK₀c.measurableSet).mpr
      (integrableOn_const (μ := ν) (s := K₀) (C := C) hfin)
  refine continuousAt_of_dominated (μ := ν) (x₀ := s₀)
    (F := fun s (g : SL3) => f (g * uij hij s))
    (bound := K₀.indicator (fun _ : SL3 => C)) ?_ ?_ hbound_int ?_
  · filter_upwards with s
    exact (f.continuous.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds s₀ zero_lt_one] with s hs
    have hsub : |s - s₀| < 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact hs
    have habs : |s| < R := by
      rw [hRdef]
      have h2 : |s| ≤ |s - s₀| + |s₀| := by
        calc |s| = |(s - s₀) + s₀| := by rw [sub_add_cancel]
          _ ≤ |s - s₀| + |s₀| := abs_add_le _ _
      linarith
    have hle := le_of_lt habs
    have hnegmem : -s ∈ Set.Icc (-R) R :=
      ⟨by linarith [(abs_le.mp hle).2], by linarith [(abs_le.mp hle).1]⟩
    filter_upwards with g
    by_cases hg : g ∈ K₀
    · rw [Set.indicator_of_mem hg]
      exact hC (g * uij hij s)
    · have hzero : f (g * uij hij s) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hg (by
          rw [hK₀def]
          exact ⟨(g * uij hij s, uij hij (-s)), ⟨hmem, ⟨-s, hnegmem, rfl⟩⟩, by
            show (g * uij hij s) * uij hij (-s) = g
            rw [mul_assoc, ← Work.EKLC7.uij_add hij s (-s), add_neg_cancel, Work.EKLC7.uij_zero hij, mul_one]⟩)
      rw [hzero, Set.indicator_of_notMem hg]
      simp
  · filter_upwards with g
    exact (f.continuous.comp (continuous_const.mul (Work.EKLC7.continuous_uij hij))).continuousAt

end

end Work.EKLRelCross
