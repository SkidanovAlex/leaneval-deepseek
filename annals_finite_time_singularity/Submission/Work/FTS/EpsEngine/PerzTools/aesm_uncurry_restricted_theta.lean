import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted
import Submission.Work.FTS.EpsEngine.PerzTools.aesm_uncurry_of_continuousOn_of_zero_1d

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.PerzTools

open MeasureTheory Set

/-- **Carathéodory measurability of a `(s,θ)`-function continuous in `θ` on `(0,π/2)` and
vanishing off it**, relative to the horizon `A`.  The `s`-slices need only be a.e. strongly
measurable for `volume.restrict A`, and only for `θ` in the open interval.  The proof truncates
to `A` (making the `s`-slices a.e. strongly measurable w.r.t. the unrestricted `volume`),
applies the unrestricted one-dimensional Carathéodory lemma, and transfers back along the
dominated measure `(volume.restrict A).prod volume ≤ volume.prod volume` together with the a.e.
fact that `p.1 ∈ A`. -/
theorem aesm_uncurry_restricted_theta {A : Set ℝ} (hA : MeasurableSet A) {g : ℝ → ℝ → ℝ}
    (hcont : ∀ s ∈ A, ContinuousOn (fun θ : ℝ => g s θ) (Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s ∈ A, ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → g s θ = 0)
    (hmeas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => g s θ) (MeasureTheory.volume.restrict A)) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume) := by
  classical
  -- Truncate `g` to the horizon `A`.
  set g₁ : ℝ → ℝ → ℝ := fun s θ => if s ∈ A then g s θ else 0 with hg₁
  -- Measurability of the `s`-slices, extended to *all* `θ` (for `θ ∉ Ioo` the slice vanishes
  -- on `A`, hence is a.e. equal to `0` for `volume.restrict A`).
  have hmeas_all : ∀ θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s θ)
      (MeasureTheory.volume.restrict A) := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · exact hmeas θ hθ
    · refine (MeasureTheory.aestronglyMeasurable_const (b := (0 : ℝ))).congr ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict hA] with x hx
      exact (hzero x hx θ hθ).symm
  -- Continuity of the truncated `θ`-slices.
  have hcont₁ : ∀ s : ℝ, ContinuousOn (fun θ : ℝ => g₁ s θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro s
    by_cases hs : s ∈ A
    · refine (hcont s hs).congr ?_
      intro θ _
      simp only [hg₁]
      rw [if_pos hs]
    · have hfun : (fun θ : ℝ => g₁ s θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp only [hg₁]
        rw [if_neg hs]
      rw [hfun]
      exact continuousOn_const
  -- Vanishing of the truncated function off the interval.
  have hzero₁ : ∀ s : ℝ, ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → g₁ s θ = 0 := by
    intro s θ hθ
    by_cases hs : s ∈ A
    · simp only [hg₁]
      rw [if_pos hs]
      exact hzero s hs θ hθ
    · simp only [hg₁]
      rw [if_neg hs]
  -- Strong measurability of the truncated `s`-slices for the unrestricted measure: the
  -- truncated slice is the indicator of `A` applied to the original slice.
  have hmeas₁ : ∀ θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g₁ s θ)
      (MeasureTheory.volume : Measure ℝ) := by
    intro θ
    have hfun : (fun s : ℝ => g₁ s θ) = A.indicator (fun s : ℝ => g s θ) := by
      funext s
      simp only [hg₁, Set.indicator_apply]
    rw [hfun]
    exact (aestronglyMeasurable_indicator_iff hA).2 (hmeas_all θ)
  have hbig : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g₁ p.1 p.2)
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ)) :=
    aesm_uncurry_of_continuousOn_of_zero_1d (g := g₁) hcont₁ hzero₁ hmeas₁
  -- The restricted product measure is dominated by the unrestricted one.
  have hle : (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume : Measure ℝ)
      ≤ (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ) :=
    MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self le_rfl
  -- ... and is carried by `A ×ˢ univ`.
  have haeA : ∀ᵐ p ∂((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume : Measure ℝ)),
      p.1 ∈ A := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ∈ A} = Aᶜ ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply' hA,
      Set.compl_inter_self, measure_empty, zero_mul]
  refine (hbig.mono_measure hle).congr ?_
  filter_upwards [haeA] with p hp
  simp only [hg₁]
  rw [if_pos hp]

end Work.FTS.EpsEngine.PerzTools
