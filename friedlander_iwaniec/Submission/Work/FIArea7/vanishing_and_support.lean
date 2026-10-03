import Mathlib

namespace Work.FIArea7

/-- If `w : ℝ → ℂ` is supported in `[0, 2πθ]` (in the sense that every nonzero value
is attained at an argument in that interval), then `w`, `deriv w` and `iteratedDeriv 2 w`
all vanish off `[0, 2πθ]`, and `w` and `deriv w` have compact support.

The vanishing of the derivatives uses only that `w` is *eventually* zero near any point
outside `[0, 2πθ]`: off that interval the whole function is zero, so both `deriv w` and
`iteratedDeriv 2 w = deriv (deriv w)` vanish there as well. -/
theorem vanishing_and_support (w : ℝ → ℂ) (θ : ℝ)
    (hsupp : ∀ α, w α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :
    (∀ α, α < 0 → w α = 0) ∧ (∀ α, 2 * Real.pi * θ < α → w α = 0) ∧
    (∀ α, α < 0 → deriv w α = 0) ∧ (∀ α, 2 * Real.pi * θ < α → deriv w α = 0) ∧
    (∀ α, α < 0 → iteratedDeriv 2 w α = 0) ∧ (∀ α, 2 * Real.pi * θ < α → iteratedDeriv 2 w α = 0) ∧
    HasCompactSupport w ∧ HasCompactSupport (deriv w) := by
  -- `[0, 2πθ]` is closed, so its complement (where `w` vanishes) is open.
  have hopen : IsOpen {β : ℝ | ¬ (0 ≤ β ∧ β ≤ 2 * Real.pi * θ)} := isClosed_Icc.isOpen_compl
  -- `w` vanishes off the interval `[0, 2πθ]`.
  have hw_out : ∀ β : ℝ, ¬ (0 ≤ β ∧ β ≤ 2 * Real.pi * θ) → w β = 0 := by
    intro β hβ; by_contra h; exact hβ (hsupp β h)
  -- hence it is *eventually* zero at any point outside the interval.
  have hwEv : ∀ α : ℝ, ¬ (0 ≤ α ∧ α ≤ 2 * Real.pi * θ) → w =ᶠ[nhds α] (0 : ℝ → ℂ) :=
    fun α hα => Filter.eventually_of_mem (hopen.mem_nhds hα) (fun β hβ => hw_out β hβ)
  -- so `deriv w` vanishes there too (a function eventually equal to a constant has the
  -- derivative of that constant).
  have hdw_out : ∀ β : ℝ, ¬ (0 ≤ β ∧ β ≤ 2 * Real.pi * θ) → deriv w β = 0 := by
    intro β hβ
    have := (hwEv β hβ).deriv_eq
    simpa using this
  have hdwEv : ∀ α : ℝ, ¬ (0 ≤ α ∧ α ≤ 2 * Real.pi * θ) → deriv w =ᶠ[nhds α] (0 : ℝ → ℂ) :=
    fun α hα => Filter.eventually_of_mem (hopen.mem_nhds hα) (fun β hβ => hdw_out β hβ)
  -- and therefore so does the second derivative `iteratedDeriv 2 w = deriv (deriv w)`.
  have hddw_out : ∀ β : ℝ, ¬ (0 ≤ β ∧ β ≤ 2 * Real.pi * θ) → iteratedDeriv 2 w β = 0 := by
    intro β hβ
    have h2 : iteratedDeriv 2 w = deriv (deriv w) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2]
    have := (hdwEv β hβ).deriv_eq
    simpa using this
  -- points below `0` and above `2πθ` both lie outside the interval.
  have hlt : ∀ α : ℝ, α < 0 → ¬ (0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :=
    fun α hα h => absurd h.1 (not_le.mpr hα)
  have hgt : ∀ α : ℝ, 2 * Real.pi * θ < α → ¬ (0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :=
    fun α hα h => absurd h.2 (not_le.mpr hα)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα; exact hw_out α (hlt α hα)
  · intro α hα; exact hw_out α (hgt α hα)
  · intro α hα; exact hdw_out α (hlt α hα)
  · intro α hα; exact hdw_out α (hgt α hα)
  · intro α hα; exact hddw_out α (hlt α hα)
  · intro α hα; exact hddw_out α (hgt α hα)
  -- compact support: the (topological) support is contained in the compact interval.
  · refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc 0 (2 * Real.pi * θ)) isCompact_Icc ?_
    intro x hx
    by_contra hx'
    exact hx (hw_out x hx')
  · refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc 0 (2 * Real.pi * θ)) isCompact_Icc ?_
    intro x hx
    by_contra hx'
    exact hx (hdw_out x hx')

end Work.FIArea7
