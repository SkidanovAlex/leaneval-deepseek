/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise vanishing bounds on the box `[0,R] × [0,π/2]`

Two consequences of the fundamental theorem of calculus on the box:

* `BoxMinBound`: if `G` vanishes on the two angular boundary segments of the box,
  then `|G z θ| ≤ boxSup R (∂_θ G) · min θ (π/2 - θ)`;
* `BoxSqBound`: if in addition `G` and `∂_z G` vanish identically at `z = 0`, then
  `|G z θ| ≤ boxSup R (∂_θ ∂_z² G) · z² · min θ (π/2 - θ)`.

These are the two elementary estimates which make a smooth compactly supported
function lie in `ℋ^k` despite the radial weight `w(z) = (1+z)²/z²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Auxiliary calculus lemmas in the angular direction -/

/-- `|H u θ - H u θ₀| ≤ C θ` when `θ₀ = 0` and `|∂_θ H| ≤ C` on the box. -/
theorem theta_slice_diff_zero (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {u θ C : ℝ}
    (hu : 0 ≤ u) (hθ : θ ∈ Iθ) (hC : ∀ s ∈ Iθ, |pth H u s| ≤ C) :
    |H u θ - H u 0| ≤ C * θ := by
  have hInt := (pth_integral H u hsm hu θ hθ).1
  have hIT : IntervalIntegrable (fun s => pth H u s) volume (0:ℝ) θ :=
    ContinuousOn.intervalIntegrable_of_Icc hθ.1 (pth_integral H u hsm hu θ hθ).2
  have h1 : |∫ s in (0:ℝ)..θ, pth H u s| ≤ C * θ := by
    have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun s => pth H u s) (a := (0:ℝ)) (b := θ) hθ.1
    rw [Real.norm_eq_abs] at h2
    have h3 : (∫ s in (0:ℝ)..θ, ‖pth H u s‖) ≤ ∫ s in (0:ℝ)..θ, C := by
      refine intervalIntegral.integral_mono_on hθ.1 hIT.norm intervalIntegrable_const ?_
      intro s hs
      rw [Real.norm_eq_abs]
      exact hC s ⟨hs.1, le_trans hs.2 hθ.2⟩
    have h4 : (∫ s in (0:ℝ)..θ, C) = C * θ := by
      rw [intervalIntegral.integral_const]; ring
    linarith [h2, h3, h4]
  rwa [← hInt]

/-- `|H u θ - H u (π/2)| ≤ C (π/2 - θ)` when `|∂_θ H| ≤ C` on the box. -/
theorem theta_slice_diff_half (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {u θ C : ℝ}
    (hu : 0 ≤ u) (hθ : θ ∈ Iθ) (hC : ∀ s ∈ Iθ, |pth H u s| ≤ C) :
    |H u θ - H u (π/2)| ≤ C * (π/2 - θ) := by
  have hInt1 := (pth_integral H u hsm hu θ hθ).1
  have hInt2 := (pth_integral H u hsm hu (π/2) pi_half_mem_Iθ).1
  have hIT1 : IntervalIntegrable (fun s => pth H u s) volume (0:ℝ) θ :=
    ContinuousOn.intervalIntegrable_of_Icc hθ.1 (pth_integral H u hsm hu θ hθ).2
  have hIT2 : IntervalIntegrable (fun s => pth H u s) volume (0:ℝ) (π/2) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
      (pth_integral H u hsm hu (π/2) pi_half_mem_Iθ).2
  have hsub : (∫ s in (0:ℝ)..(π/2), pth H u s) - (∫ s in (0:ℝ)..θ, pth H u s)
      = ∫ s in θ..(π/2), pth H u s := intervalIntegral.integral_interval_sub_left hIT2 hIT1
  have hkey : H u θ - H u (π/2) = -(∫ s in θ..(π/2), pth H u s) := by
    rw [← hsub, hInt2, hInt1]; ring
  have hIT3 : IntervalIntegrable (fun s => pth H u s) volume θ (π/2) :=
    ContinuousOn.intervalIntegrable_of_Icc hθ.2
      ((pth_integral H u hsm hu (π/2) pi_half_mem_Iθ).2.mono (by
        intro s hs; exact ⟨le_trans hθ.1 hs.1, hs.2⟩))
  have h1 : |∫ s in θ..(π/2), pth H u s| ≤ C * (π/2 - θ) := by
    have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun s => pth H u s) (a := θ) (b := π/2) hθ.2
    rw [Real.norm_eq_abs] at h2
    have h3 : (∫ s in θ..(π/2), ‖pth H u s‖) ≤ ∫ s in θ..(π/2), C := by
      refine intervalIntegral.integral_mono_on hθ.2 hIT3.norm intervalIntegrable_const ?_
      intro s hs
      rw [Real.norm_eq_abs]
      exact hC s ⟨le_trans hθ.1 hs.1, hs.2⟩
    have h4 : (∫ s in θ..(π/2), C) = C * (π/2 - θ) := by
      rw [intervalIntegral.integral_const]; ring
    linarith [h2, h3, h4]
  rw [hkey, abs_neg]
  exact h1

/-! ## Auxiliary calculus lemmas in the radial direction -/

/-- Continuity of `z ↦ ∂_z H z θ - ∂_z H z θ₀` on `[0,z]`. -/
theorem pz_slice_diff_continuousOn (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {θ θ₀ z : ℝ}
    (hθ : θ ∈ Iθ) (hθ₀ : θ₀ ∈ Iθ) (hz : 0 ≤ z) :
    ContinuousOn (fun s => pz H s θ - pz H s θ₀) (Set.Icc 0 z) := by
  refine ((hardyZ_continuousOn_pz_slice H hsm hθ).mono ?_).sub
    ((hardyZ_continuousOn_pz_slice H hsm hθ₀).mono ?_)
  · intro x hx; exact hardyZ_mem_Ioi 0 x (le_refl 0) hx.1
  · intro x hx; exact hardyZ_mem_Ioi 0 x (le_refl 0) hx.1

/-- Continuity of `z ↦ H z θ - H z θ₀` on `[0,z]`. -/
theorem slice_diff_continuousOn (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {θ θ₀ z : ℝ}
    (hθ : θ ∈ Iθ) (hθ₀ : θ₀ ∈ Iθ) (hz : 0 ≤ z) :
    ContinuousOn (fun s => H s θ - H s θ₀) (Set.Icc 0 z) := by
  refine ((hardyZ_contDiffOn_slice H hsm hθ).continuousOn.mono ?_).sub
    ((hardyZ_contDiffOn_slice H hsm hθ₀).continuousOn.mono ?_)
  · intro x hx; exact hardyZ_mem_Ioi 0 x (le_refl 0) hx.1
  · intro x hx; exact hardyZ_mem_Ioi 0 x (le_refl 0) hx.1

/-- The fundamental theorem of calculus for the difference of the two radial slices
`u ↦ H u θ` and `u ↦ H u θ₀`. -/
theorem slice_diff_ftc (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {θ θ₀ z : ℝ}
    (hθ : θ ∈ Iθ) (hθ₀ : θ₀ ∈ Iθ) (hz : 0 ≤ z) :
    H z θ - H z θ₀ - (H 0 θ - H 0 θ₀) = ∫ s in (0:ℝ)..z, (pz H s θ - pz H s θ₀) := by
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) z,
      HasDerivAt (fun u => H u θ - H u θ₀) (pz H x θ - pz H x θ₀) x := by
    intro x hx
    have hx' : x ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith [hx.1]
    exact (hardyZ_hasDerivAt_slice H hsm hθ hx').sub (hardyZ_hasDerivAt_slice H hsm hθ₀ hx')
  have hcont : ContinuousOn (fun u => H u θ - H u θ₀) (Set.Icc 0 z) :=
    slice_diff_continuousOn H hsm hθ hθ₀ hz
  have hint : IntervalIntegrable (fun s => pz H s θ - pz H s θ₀) volume (0:ℝ) z :=
    ContinuousOn.intervalIntegrable_of_Icc hz (pz_slice_diff_continuousOn H hsm hθ hθ₀ hz)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz hcont hderiv hint).symm

/-- Bound for the difference of two radial slices: if the `z`-derivative difference is
bounded by `K` on `[0,z]`, the slice difference is bounded by `K * z`. -/
theorem slice_diff_bound (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {θ θ₀ z K : ℝ}
    (hθ : θ ∈ Iθ) (hθ₀ : θ₀ ∈ Iθ) (hz : 0 ≤ z) (h0 : H 0 θ - H 0 θ₀ = 0)
    (hK : ∀ u ∈ Set.Icc 0 z, |pz H u θ - pz H u θ₀| ≤ K) :
    |H z θ - H z θ₀| ≤ K * z := by
  have hid := slice_diff_ftc H hsm hθ hθ₀ hz
  have hkey : H z θ - H z θ₀ = ∫ s in (0:ℝ)..z, (pz H s θ - pz H s θ₀) := by
    rw [← hid, h0, sub_zero]
  rw [hkey]
  have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun s => pz H s θ - pz H s θ₀) (a := (0:ℝ)) (b := z) hz
  rw [Real.norm_eq_abs] at h1
  have hint : IntervalIntegrable (fun s => ‖pz H s θ - pz H s θ₀‖) volume (0:ℝ) z :=
    ContinuousOn.intervalIntegrable_of_Icc hz (pz_slice_diff_continuousOn H hsm hθ hθ₀ hz).norm
  have h3 : (∫ s in (0:ℝ)..z, ‖pz H s θ - pz H s θ₀‖) ≤ ∫ s in (0:ℝ)..z, K := by
    refine intervalIntegral.integral_mono_on hz hint intervalIntegrable_const ?_
    intro s hs
    rw [Real.norm_eq_abs]
    exact hK s hs
  have h4 : (∫ s in (0:ℝ)..z, K) = K * z := by
    rw [intervalIntegral.integral_const]; ring
  linarith [h1, h3, h4]

/-- Bound for the difference of two radial slices with a linear majorant. -/
theorem slice_diff_bound_lin (H : ℝ → ℝ → ℝ) (hsm : SmoothNbhd H) {θ θ₀ z K : ℝ}
    (hθ : θ ∈ Iθ) (hθ₀ : θ₀ ∈ Iθ) (hz : 0 ≤ z) (h0 : H 0 θ - H 0 θ₀ = 0)
    (hK : ∀ u ∈ Set.Icc 0 z, |pz H u θ - pz H u θ₀| ≤ K * u) :
    |H z θ - H z θ₀| ≤ K * z ^ 2 / 2 := by
  have hid := slice_diff_ftc H hsm hθ hθ₀ hz
  have hkey : H z θ - H z θ₀ = ∫ s in (0:ℝ)..z, (pz H s θ - pz H s θ₀) := by
    rw [← hid, h0, sub_zero]
  rw [hkey]
  have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun s => pz H s θ - pz H s θ₀) (a := (0:ℝ)) (b := z) hz
  rw [Real.norm_eq_abs] at h1
  have hint : IntervalIntegrable (fun s => ‖pz H s θ - pz H s θ₀‖) volume (0:ℝ) z :=
    ContinuousOn.intervalIntegrable_of_Icc hz (pz_slice_diff_continuousOn H hsm hθ hθ₀ hz).norm
  have h3 : (∫ s in (0:ℝ)..z, ‖pz H s θ - pz H s θ₀‖) ≤ ∫ s in (0:ℝ)..z, K * s := by
    refine intervalIntegral.integral_mono_on hz hint
      (ContinuousOn.intervalIntegrable_of_Icc hz (continuousOn_const.mul continuousOn_id)) ?_
    intro s hs
    rw [Real.norm_eq_abs]
    exact hK s hs
  have h4 : (∫ s in (0:ℝ)..z, K * s) = K * z ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  linarith [h1, h3, h4]

/-! ## The two box bounds -/

/-- If `G` vanishes on the two angular boundary segments of the box then
`|G| ≤ boxSup R (∂_θ G) · min θ (π/2 - θ)` on the box. -/
theorem BoxMinBound (G : ℝ → ℝ → ℝ) (R : ℝ)
    (hsm : ContDiffOn ℝ ⊤ (Function.uncurry G) U)
    (h1 : ∀ z ∈ Set.Icc 0 R, G z 0 = 0) (h2 : ∀ z ∈ Set.Icc 0 R, G z (π/2) = 0) :
    ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Iθ,
      |G z θ| ≤ boxSup R (pth G) * min θ (π/2 - θ) := by
  have hb : BddAbove (boxSet R (pth G)) := bddAbove_boxSup_of_continuousOn
    (continuousOn_box_of_contDiffOn (contDiffOn_uncurry_pth isOpen_U hsm))
  intro z hz θ hθ
  have hbd : ∀ s ∈ Iθ, |pth G z s| ≤ boxSup R (pth G) := fun s hs => le_boxSup hb hz hs
  have hle1 : |G z θ| ≤ boxSup R (pth G) * θ := by
    have := theta_slice_diff_zero G hsm hz.1 hθ hbd
    rwa [h1 z hz, sub_zero] at this
  have hle2 : |G z θ| ≤ boxSup R (pth G) * (π/2 - θ) := by
    have := theta_slice_diff_half G hsm hz.1 hθ hbd
    rwa [h2 z hz, sub_zero] at this
  rcases le_total θ (π/2 - θ) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- If `G` and `∂_z G` vanish identically at `z = 0` and `G` vanishes on the two
angular boundary segments of the box, then
`|G| ≤ boxSup R (∂_θ ∂_z² G) · z² · min θ (π/2 - θ)` on the box. -/
theorem BoxSqBound (G : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hsm : ContDiffOn ℝ ⊤ (Function.uncurry G) U)
    (h0 : ∀ θ ∈ Iθ, G 0 θ = 0) (hpz : ∀ θ ∈ Iθ, pz G 0 θ = 0)
    (h1 : ∀ z ∈ Set.Icc 0 R, G z 0 = 0) (h2 : ∀ z ∈ Set.Icc 0 R, G z (π/2) = 0) :
    ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Iθ,
      |G z θ| ≤ boxSup R (pth (pz (pz G))) * z ^ 2 * min θ (π/2 - θ) := by
  have hsm1 : SmoothNbhd (pz G) := contDiffOn_uncurry_pz isOpen_U hsm
  have hsm2 : SmoothNbhd (pz (pz G)) := contDiffOn_uncurry_pz isOpen_U hsm1
  have hb : BddAbove (boxSet R (pth (pz (pz G)))) := bddAbove_boxSup_of_continuousOn
    (continuousOn_box_of_contDiffOn (contDiffOn_uncurry_pth isOpen_U hsm2))
  have hCnn : 0 ≤ boxSup R (pth (pz (pz G))) := boxSup_nonneg hR hb
  intro z hz θ hθ
  have hbdC : ∀ u ∈ Set.Icc 0 R, ∀ s ∈ Iθ,
      |pth (pz (pz G)) u s| ≤ boxSup R (pth (pz (pz G))) := fun u hu s hs => le_boxSup hb hu hs
  -- Step A : the `θ`-difference of `∂_z² G`
  have hA0 : ∀ u ∈ Set.Icc 0 R,
      |pz (pz G) u θ - pz (pz G) u 0| ≤ boxSup R (pth (pz (pz G))) * θ :=
    fun u hu => theta_slice_diff_zero (pz (pz G)) hsm2 hu.1 hθ (hbdC u hu)
  have hA2 : ∀ u ∈ Set.Icc 0 R,
      |pz (pz G) u θ - pz (pz G) u (π/2)| ≤ boxSup R (pth (pz (pz G))) * (π/2 - θ) :=
    fun u hu => theta_slice_diff_half (pz (pz G)) hsm2 hu.1 hθ (hbdC u hu)
  -- Step B : the `θ`-difference of `∂_z G`
  have hB0 : ∀ t ∈ Set.Icc 0 R,
      |pz G t θ - pz G t 0| ≤ (boxSup R (pth (pz (pz G))) * θ) * t := by
    intro t ht
    refine slice_diff_bound (pz G) hsm1 hθ zero_mem_Iθ ht.1 ?_ ?_
    · rw [hpz θ hθ, hpz 0 zero_mem_Iθ, sub_zero]
    · intro u hu
      exact hA0 u ⟨hu.1, le_trans hu.2 ht.2⟩
  have hB2 : ∀ t ∈ Set.Icc 0 R,
      |pz G t θ - pz G t (π/2)| ≤ (boxSup R (pth (pz (pz G))) * (π/2 - θ)) * t := by
    intro t ht
    refine slice_diff_bound (pz G) hsm1 hθ pi_half_mem_Iθ ht.1 ?_ ?_
    · rw [hpz θ hθ, hpz (π/2) pi_half_mem_Iθ, sub_zero]
    · intro u hu
      exact hA2 u ⟨hu.1, le_trans hu.2 ht.2⟩
  -- Step C : `G` itself
  have hC0 : |G z θ| ≤ (boxSup R (pth (pz (pz G))) * θ) * z ^ 2 / 2 := by
    have h := slice_diff_bound_lin G hsm hθ zero_mem_Iθ hz.1
      (by rw [h0 θ hθ, h0 0 zero_mem_Iθ, sub_zero])
      (fun u hu => hB0 u ⟨hu.1, le_trans hu.2 hz.2⟩)
    rwa [h1 z hz, sub_zero] at h
  have hC2 : |G z θ| ≤ (boxSup R (pth (pz (pz G))) * (π/2 - θ)) * z ^ 2 / 2 := by
    have h := slice_diff_bound_lin G hsm hθ pi_half_mem_Iθ hz.1
      (by rw [h0 θ hθ, h0 (π/2) pi_half_mem_Iθ, sub_zero])
      (fun u hu => hB2 u ⟨hu.1, le_trans hu.2 hz.2⟩)
    rwa [h2 z hz, sub_zero] at h
  have hfin1 : |G z θ| ≤ boxSup R (pth (pz (pz G))) * z ^ 2 * θ := by
    have hstep : (boxSup R (pth (pz (pz G))) * θ) * z ^ 2 / 2
        ≤ boxSup R (pth (pz (pz G))) * z ^ 2 * θ := by
      have hnn : 0 ≤ boxSup R (pth (pz (pz G))) * θ * z ^ 2 :=
        mul_nonneg (mul_nonneg hCnn hθ.1) (sq_nonneg z)
      nlinarith [hnn]
    linarith [hC0, hstep]
  have hfin2 : |G z θ| ≤ boxSup R (pth (pz (pz G))) * z ^ 2 * (π/2 - θ) := by
    have hstep : (boxSup R (pth (pz (pz G))) * (π/2 - θ)) * z ^ 2 / 2
        ≤ boxSup R (pth (pz (pz G))) * z ^ 2 * (π/2 - θ) := by
      have hnn : 0 ≤ boxSup R (pth (pz (pz G))) * (π/2 - θ) * z ^ 2 :=
        mul_nonneg (mul_nonneg hCnn (by linarith [hθ.2])) (sq_nonneg z)
      nlinarith [hnn]
    linarith [hC2, hstep]
  rcases le_total θ (π/2 - θ) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

end Work.Spaces
