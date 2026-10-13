/-
# `L₁₂(hLoc)` at `z = 0`: the normalisation of the bump

This module computes the value at `z = 0` of the operator `L₁₂` of the paper on the concrete
bump `hLoc α z θ = bumpZ z · Γ(θ)` of the localised data (`Work.FTS.LocData.Defs`):

  `L₁₂(hLoc α)(0) = c(α) · ∫_{0}^{∞} bumpZ(s)/s ds`,

and proves that this number is **strictly positive**.  The two facts are what make the bump
usable in the localisation node N9 of the route: `β = O(1/L)` is chosen so that
`L₁₂(g(0))(0) = 0` for `g(0) = -zfar L F_* + β h`, which requires `L₁₂(h)(0) ≠ 0`.

## The computation

`L₁₂(f)(z) = ∫_z^∞ L₁₂dens(f)(s) ds` with `L₁₂dens(f)(s) = ∫_0^{π/2} K(θ) f(s,θ)/s dθ`
(`Work.FM.L12`).  For `f = hLoc α` the integrand of the *angular* integral is a product of a
function of `s` and a function of `θ`,

  `K(θ)·bumpZ(s)·Γ(θ)/s = (bumpZ(s)/s) · (K(θ)·Γ(θ))`,

so the angular density is the radial factor `bumpZ(s)/s` times the normalisation constant
`c(α) = ∫_0^{π/2} Γ(θ)K(θ) dθ` (`L12dens_hLoc`), and pulling the constant out of the outer
integral gives the stated identity.

## Positivity

`c(α) ≥ 1/10 > 0` for `0 < α ≤ 1` (`Work.Spaces.c_bounds`).  For the radial factor:
`bumpZ = χ(4·-5)` vanishes off `(3/4, 7/4)` (`bumpZ_eq_zero_of_notMem`) and equals `1` on
`[1, 3/2]` (`bumpZ_eq_one_of_mem`), so the integrand `bumpZ(s)/s` is a nonnegative compactly
supported function which equals `1/s ≥ 2/3` on an interval of length `1/2`; hence
`∫_0^∞ bumpZ(s)/s ds ≥ 1/3 > 0` (`bumpInt_pos`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The two support facts for `bumpZ = χ(4·-5)` -/

/-- `bumpZ` vanishes off the interval `(3/4, 7/4)`, i.e. outside the set where `|4s - 5| < 2`. -/
theorem bumpZ_eq_zero_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (3/4) (7/4)) : bumpZ s = 0 := by
  rw [bumpZ_apply]
  apply Work.Stability.chi_eq_zero
  have hs' : ¬(3/4 ≤ s ∧ s ≤ 7/4) := hs
  rcases not_and_or.mp hs' with h | h
  · rw [not_le] at h
    have h2 : 4 * s - 5 < -2 := by linarith
    rw [abs_of_neg (by linarith)]
    linarith
  · rw [not_le] at h
    have h2 : 2 < 4 * s - 5 := by linarith
    rw [abs_of_pos (by linarith)]
    linarith

/-- `bumpZ = 1` on `[1, 3/2]`, the flat top of the bump. -/
theorem bumpZ_eq_one_of_mem {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (3/2)) : bumpZ s = 1 := by
  rw [bumpZ_apply]
  apply Work.Stability.chi_eq_one
  rw [abs_le]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- `bumpZ` is continuous. -/
theorem continuous_bumpZ : Continuous bumpZ :=
  Work.Stability.chi_continuous.comp (by fun_prop)

/-! ## Positivity of the radial integral -/

/-- **The radial normalisation integral is positive**: `∫_0^∞ bumpZ(s)/s ds > 0`.

The integrand is nonnegative, compactly supported (in `(3/4, 7/4)`) and equals `1/s ≥ 2/3` on
the interval `[1, 3/2]`, so the integral is at least `(2/3)·(1/2) = 1/3 > 0`. -/
theorem bumpInt_pos : 0 < ∫ s in Set.Ioi (0 : ℝ), bumpZ s / s := by
  set f : ℝ → ℝ := fun s => bumpZ s / s with hf
  -- the integrand is integrable on `(3/4, 7/4)`, where it is continuous
  have hf_int_Icc : IntegrableOn f (Set.Icc (3/4) (7/4)) := by
    refine ContinuousOn.integrableOn_Icc ?_
    rw [hf]
    exact continuous_bumpZ.continuousOn.div continuousOn_id
      (fun s hs => ne_of_gt (by linarith [hs.1]))
  -- ... and vanishes off that interval, hence is integrable on `ℝ`
  have hf_ind : f = (Set.Icc (3/4) (7/4)).indicator f := by
    funext s
    by_cases hs : s ∈ Set.Icc (3/4) (7/4)
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      show f s = 0
      simp only [hf]
      rw [bumpZ_eq_zero_of_notMem hs, zero_div]
  have hf_int : Integrable f volume := by
    rw [hf_ind]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hf_int_Icc
  have hf_int_on : IntegrableOn f (Set.Ioi (0 : ℝ)) := hf_int.integrableOn
  have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun s hs => by
      simp only [hf, bumpZ_apply, Pi.zero_apply]
      exact div_nonneg (Work.Stability.chi_nonneg _) (le_of_lt hs))
  rw [setIntegral_pos_iff_support_of_nonneg_ae hf_nn hf_int_on]
  -- the support of `f` meets `(0,∞)` in the set of positive measure `[1, 3/2]`
  have hsub : Set.Icc (1 : ℝ) (3/2) ⊆ Function.support f ∩ Set.Ioi 0 := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rw [Function.mem_support]
      simp only [hf]
      rw [bumpZ_eq_one_of_mem hs, one_div]
      exact inv_ne_zero (ne_of_gt (by linarith [hs.1]))
    · simp only [Set.mem_Ioi]; linarith [hs.1]
  have hvol : 0 < volume (Set.Icc (1 : ℝ) (3/2)) := by
    rw [Real.volume_Icc]
    rw [show (3 : ℝ)/2 - 1 = 1/2 by norm_num]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  exact lt_of_lt_of_le hvol (measure_mono hsub)

/-! ## The angular density of `hLoc` -/

/-- **The angular density of the bump is the radial factor times `c(α)`**:
`L₁₂dens(hLoc α)(s) = (bumpZ(s)/s)·c(α)`.  This is separability of the integrand
`K(θ)·bumpZ(s)Γ(θ)/s` plus the definition of `c(α)`. -/
theorem L12dens_hLoc (α s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (hLoc α) s = (bumpZ s / s) * Work.Spaces.c α := by
  simp only [Work.FM.L12dens, Work.Spaces.c, Work.Spaces.Iθ]
  rw [show (∫ θ in Set.Icc (0 : ℝ) (π/2), Work.Spaces.K θ * hLoc α s θ / s)
      = ∫ θ in Set.Icc (0 : ℝ) (π/2),
          (bumpZ s / s) * (Work.Spaces.K θ * Work.Spaces.Gam α θ) from
    setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => by rw [hLoc_apply, div_eq_mul_inv]; ring)]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The target -/

theorem L12_hLoc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.L12 (hLoc α) 0
        = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), bumpZ s / s) ∧
      0 < Work.Construction.L12 (hLoc α) 0 := by
  have hI : 0 < ∫ s in Set.Ioi (0 : ℝ), bumpZ s / s := bumpInt_pos
  have hc : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hEq : Work.Construction.L12 (hLoc α) 0
      = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), bumpZ s / s) := by
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [show (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K (hLoc α) s)
        = ∫ s in Set.Ioi (0 : ℝ), (bumpZ s / s) * Work.Spaces.c α from
      setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_hLoc α s)]
    rw [MeasureTheory.integral_mul_const]
    exact mul_comm _ _
  exact ⟨hEq, by rw [hEq]; exact mul_pos hc hI⟩

end Work.FTS.LocData
