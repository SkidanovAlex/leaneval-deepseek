import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.STE.Lead

/-- Fundamental theorem of calculus (right endpoint), stated on the half-open interval `Ico 0 τ`.

If `K : ℝ → ℂ` is continuous on `Ico 0 τ` and `t ∈ Ico 0 τ`, then the function
`s ↦ ∫ σ in 0..s, K σ` has derivative `K t` at `t` within `Ico 0 τ`.

The point is that, for the filter at `t`, the half-open interval `Ico 0 τ` is indistinguishable
from the closed interval `Icc 0 τ` (because `t < τ`), so the standard fundamental theorem of
calculus for closed intervals applies. -/
theorem hasDerivWithinAt_integral_Ico {τ : ℝ} (hτ : 0 < τ) {K : ℝ → ℂ}
    (hK : ContinuousOn K (Set.Ico (0 : ℝ) τ)) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) τ) :
    HasDerivWithinAt (fun s : ℝ => ∫ σ in (0 : ℝ)..s, K σ) (K t) (Set.Ico (0 : ℝ) τ) t := by
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htt : t < τ := ht.2
  have hmem : t ∈ Set.Icc (0 : ℝ) τ := ⟨ht0, le_of_lt htt⟩
  -- Near `t` the sets `Ico 0 τ` and `Icc 0 τ` agree: `Ico 0 τ = Icc 0 τ ∩ Iio τ` and
  -- `Iio τ` is a neighbourhood of `t` (as `t < τ`).
  have hIio : Set.Iio τ ∈ 𝓝[Set.Icc (0 : ℝ) τ] t := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio τ, isOpen_Iio, htt, fun x hx => hx.1⟩
  have hnhds : 𝓝[Set.Ico (0 : ℝ) τ] t = 𝓝[Set.Icc (0 : ℝ) τ] t := by
    rw [show Set.Ico (0 : ℝ) τ = Set.Icc (0 : ℝ) τ ∩ Set.Iio τ from by
      ext x; constructor
      · intro hx; exact ⟨⟨hx.1, le_of_lt hx.2⟩, hx.2⟩
      · intro hx; exact ⟨hx.1.1, hx.2⟩]
    exact nhdsWithin_inter_of_mem' hIio
  haveI : Fact (t ∈ Set.Icc (0 : ℝ) τ) := ⟨hmem⟩
  -- Continuity and strong measurability at `t` for the equivalent filter `𝓝[Icc 0 τ] t`.
  have hcw : ContinuousWithinAt K (Set.Icc (0 : ℝ) τ) t := by
    simpa only [ContinuousWithinAt, hnhds] using hK.continuousWithinAt ht
  have hmeas : StronglyMeasurableAtFilter K (𝓝[Set.Icc (0 : ℝ) τ] t) := by
    simpa only [StronglyMeasurableAtFilter, hnhds] using
      hK.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ico t
  -- Interval integrability on `0..t` (the interval is contained in `Ico 0 τ`).
  have hint : IntervalIntegrable K MeasureTheory.volume (0 : ℝ) t :=
    ContinuousOn.intervalIntegrable_of_Icc ht0
      (hK.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 htt⟩))
  -- Fundamental theorem of calculus on the closed interval `Icc 0 τ`.
  have hderiv : HasDerivWithinAt (fun s : ℝ => ∫ σ in (0 : ℝ)..s, K σ) (K t)
      (Set.Icc (0 : ℝ) τ) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc (0 : ℝ) τ)
      (t := Set.Icc (0 : ℝ) τ) hint hmeas hcw
  exact hderiv.mono Set.Ico_subset_Icc_self

end Work.Diff.STE.Lead
