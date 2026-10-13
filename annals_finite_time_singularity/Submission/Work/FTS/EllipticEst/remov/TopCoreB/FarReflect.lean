import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The reflection `θ ↦ π/2 - θ` of the far window `[3π/8, π/2]`

For the far-window bound on `v = u/cos θ` one substitutes `x = π/2 - θ ∈ [0, π/8]`, so that
`v(π/2 - x) = u(π/2 - x)/sin x`.  This file collects the definitions (`xEnd`, `shiftU`,
`shiftV`, `secH`), the elementary reflection calculus for `iteratedDeriv`, the change of
variables for the far-window integral, and the smoothness/vanishing/integrability transfers
from the `θ`-side to the `x`-side.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The right endpoint `π/8` of the reflected far window. -/
abbrev xEnd : ℝ := Real.pi / 8

theorem xEnd_pos : 0 < xEnd := by rw [xEnd]; positivity

theorem xEnd_le_one : xEnd ≤ 1 := by
  rw [xEnd]; linarith [Real.pi_pos, Real.pi_lt_four]

theorem xEnd_lt_pi_half : xEnd < Real.pi / 2 := by
  rw [xEnd]; linarith [Real.pi_pos]

theorem xEnd_lt_pi_four : xEnd < Real.pi / 4 := by
  rw [xEnd]; linarith [Real.pi_pos]

theorem two_xEnd_eq : 2 * xEnd = Real.pi / 4 := by rw [xEnd]; ring

/-- The reflected slice `x ↦ u (π/2 - x)`. -/
abbrev shiftU (u : ℝ → ℝ) : ℝ → ℝ := fun x => u (Real.pi / 2 - x)

/-- The bounded quotient `x / sin x` on the far window. -/
abbrev secH : ℝ → ℝ := fun x => x / Real.sin x

/-- `v = u / cos θ` in the reflected variable: `x ↦ u (π/2 - x) / sin x`. -/
abbrev shiftV (u : ℝ → ℝ) : ℝ → ℝ := fun x => shiftU u x / Real.sin x

/-- The reflection `x ↦ π/2 - x`. -/
abbrev reflectC : ℝ → ℝ := fun x => Real.pi / 2 - x

theorem reflectC_eq (x : ℝ) : reflectC x = -(x - Real.pi / 2) := by rw [reflectC]; ring

/-- **Chain rule for the reflection** `θ ↦ c - θ`. -/
theorem iteratedDeriv_comp_const_sub (n : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    iteratedDeriv n (fun x => f (c - x)) = fun x => (-1) ^ n * iteratedDeriv n f (c - x) := by
  have h := iteratedDerivWithin_comp_const_sub (𝕜 := ℝ) (f := f) (s := Set.univ) (n := n) c
  simpa using h

/-- `sin (2 (π/2 - x)) = sin (2x)`. -/
theorem sin_two_pi_half_sub (x : ℝ) : Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-- **Substitution `θ = π/2 - x` on the far window.** -/
theorem integral_farSet_eq (F : ℝ → ℝ) :
    (∫ θ in farSet, F θ) = ∫ x in (0 : ℝ)..xEnd, F (Real.pi / 2 - x) := by
  have hIcc : farSet = Set.Icc (3 * Real.pi / 8) (Real.pi / 2) := rfl
  have hle : (3 : ℝ) * Real.pi / 8 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [hIcc, setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := 3 * Real.pi / 8)
      (b := Real.pi / 2)).symm, ← intervalIntegral.integral_of_le hle]
  have h := intervalIntegral.integral_comp_sub_left (fun y : ℝ => F (Real.pi / 2 - y))
    (Real.pi / 2) (a := 3 * Real.pi / 8) (b := Real.pi / 2)
  simp only [sub_sub_cancel] at h
  rw [show Real.pi / 2 - 3 * Real.pi / 8 = xEnd by rw [xEnd]; ring,
    show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring] at h
  exact h

/-- `vF u` is the reflected `v`. -/
theorem vF_eq_shiftV (u : ℝ → ℝ) :
    vF u = fun θ => shiftV u (Real.pi / 2 - θ) := by
  funext θ
  rw [vF, shiftV, shiftU, Real.sin_pi_div_two_sub]
  rw [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring]

/-- The far-window integrand in the reflected variable. -/
theorem farSet_integrand_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) (x : ℝ) :
    (iteratedDeriv m (vF u) (Real.pi / 2 - x)) ^ 2 * qW k γ (Real.pi / 2 - x)
      = (iteratedDeriv m (shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
  rw [vF_eq_shiftV, iteratedDeriv_comp_const_sub]
  have hx : Real.pi / 2 - (Real.pi / 2 - x) = x := by ring
  have hp : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, show m * 2 = 2 * m by ring, pow_mul]
    norm_num
  simp only [qW, hx, sin_two_pi_half_sub]
  rw [mul_pow, hp, one_mul]

/-- **The far-window left-hand side in the reflected variable.** -/
theorem farSet_LHS_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) :
    (∫ θ in farSet, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
      = ∫ x in (0 : ℝ)..xEnd, (iteratedDeriv m (shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
  rw [integral_farSet_eq]
  refine intervalIntegral.integral_congr fun x _ => ?_
  exact farSet_integrand_eq k γ m u x

/-- The reflected slot integrand. -/
theorem slot_integrand_reflect (j : ℕ) (p : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    (iteratedDeriv j u (Real.pi / 2 - x)) ^ 2
        * Real.rpow (Real.sin (2 * (Real.pi / 2 - x))) p
      = (iteratedDeriv j (shiftU u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) p := by
  have h := congrFun (iteratedDeriv_comp_const_sub j u (Real.pi / 2)) x
  have h' : iteratedDeriv j (shiftU u) x = (-1) ^ j * iteratedDeriv j u (Real.pi / 2 - x) := h
  have hsq : (iteratedDeriv j u (Real.pi / 2 - x)) ^ 2 = (iteratedDeriv j (shiftU u) x) ^ 2 := by
    have hp : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, show j * 2 = 2 * j by ring, pow_mul]
      norm_num
    rw [h', mul_pow, hp, one_mul]
  rw [sin_two_pi_half_sub, hsq]

/-- **A far-window `u`-slot integral in the reflected variable.** -/
theorem integral_farSet_slot_eq (j : ℕ) (p : ℝ) (u : ℝ → ℝ) :
    (∫ θ in farSet, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) p)
      = ∫ x in (0 : ℝ)..xEnd, (iteratedDeriv j (shiftU u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) p := by
  rw [integral_farSet_eq]
  refine intervalIntegral.integral_congr fun x _ => ?_
  exact slot_integrand_reflect j p u x

section Basic

variable {x θ : ℝ}

theorem sin_two_nonneg_Ioc (hx : x ∈ Set.Ioc 0 xEnd) : 0 ≤ Real.sin (2 * x) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by
    have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos]⟩

theorem sin_two_pos_Ioc (hx : x ∈ Set.Ioc 0 xEnd) : 0 < Real.sin (2 * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by
    have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos])

theorem sin_two_nonneg_Ioo (hx : x ∈ Set.Ioo 0 xEnd) : 0 ≤ Real.sin (2 * x) :=
  sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩

/-- On the reflected window, `x ≤ sin (2x)`. -/
theorem self_le_sin_two (hx : x ∈ Set.Ioc 0 xEnd) : x ≤ Real.sin (2 * x) := by
  have h0 : 0 ≤ 2 * x := by linarith [hx.1]
  have h1 : 2 * x ≤ Real.pi / 2 := by
    have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos]
  have h2 := Real.mul_le_sin h0 h1
  have h3 : (4 / Real.pi) * x ≤ Real.sin (2 * x) := by
    calc (4 / Real.pi) * x = 2 / Real.pi * (2 * x) := by ring
      _ ≤ Real.sin (2 * x) := h2
  have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
    rw [le_div_iff₀ (by linarith [Real.pi_pos])]; linarith [Real.pi_lt_four]
  calc x = 1 * x := (one_mul x).symm
    _ ≤ (4 / Real.pi) * x := mul_le_mul_of_nonneg_right h4 (by linarith [hx.1])
    _ ≤ Real.sin (2 * x) := h3

end Basic

/-- Reflected smoothness. -/
theorem contDiffOn_shiftU {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (shiftU u) (Set.Ioo 0 xEnd) := by
  have hmap : ContDiffOn ℝ n (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 xEnd) := by fun_prop
  have hmt : MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 xEnd)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    exact ⟨by linarith [hx.2, xEnd_lt_pi_half], by linarith [hx.1]⟩
  exact hu.comp hmap hmt

/-- `shiftU u` is `C^N` on the half-open interval `(0, xEnd]`. -/
theorem contDiffOn_shiftU_Ioc {N : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ N u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ N (shiftU u) (Set.Ioc 0 xEnd) := by
  have hmap : ContDiffOn ℝ N (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4)) := by
    fun_prop
  have hmt : MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
  have h1 : ContDiffOn ℝ N (shiftU u) (Set.Ioo 0 (Real.pi / 4)) := hu.comp hmap hmt
  refine h1.mono fun x hx => ?_
  exact ⟨hx.1, by linarith [hx.2, xEnd_lt_pi_four]⟩

/-- The reflected slice tends to `u (π/2) = 0` at `0⁺`. -/
theorem tendsto_shiftU {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu1 : u (Real.pi / 2) = 0) :
    Tendsto (shiftU u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hcont : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)))
      (nhds (u (Real.pi / 2))) := hu.continuousWithinAt hmem
  rw [hu1] at hcont
  refine hcont.comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun x : ℝ => Real.pi / 2 - x) 0 := by fun_prop
    have h1 : Tendsto (fun x : ℝ => Real.pi / 2 - x) (nhds (0 : ℝ))
        (nhds (Real.pi / 2 - 0)) := hc.tendsto
    simpa using h1.mono_left nhdsWithin_le_nhds
  · have hlt : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))
    filter_upwards [self_mem_nhdsWithin, hlt] with x hxpos hxlt
    have h1 : (0 : ℝ) < x := hxpos
    have h2 : x < Real.pi / 2 := hxlt
    exact ⟨by linarith, by linarith⟩

theorem measurableEmbedding_reflectC : MeasurableEmbedding reflectC := by
  have h : MeasurableEmbedding (fun x : ℝ => -(x - Real.pi / 2)) :=
    measurableEmbedding_neg.comp (measurableEmbedding_subRight (Real.pi / 2))
  have hfun : reflectC = fun x : ℝ => -(x - Real.pi / 2) := by
    funext x; rw [reflectC_eq]
  rwa [hfun]

theorem measurePreserving_reflectC : MeasurePreserving reflectC volume volume := by
  have h : MeasurePreserving (fun x : ℝ => -(x - Real.pi / 2)) volume volume :=
    (Measure.measurePreserving_neg volume).comp
      (measurePreserving_sub_right volume (Real.pi / 2))
  have hfun : reflectC = fun x : ℝ => -(x - Real.pi / 2) := by
    funext x; rw [reflectC_eq]
  rwa [hfun]

theorem preimage_reflectC_farSet : reflectC ⁻¹' farSet = Set.Icc 0 xEnd := by
  ext x
  simp only [mem_preimage, reflectC, farSet, mem_Icc, xEnd]
  constructor
  · intro h
    exact ⟨by linarith [h.2, Real.pi_pos], by linarith [h.1]⟩
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Integrability of a reflected slot, transferred from the angular interval. -/
theorem integrableOn_shift_slot (j : ℕ) (p : ℝ) (u : ℝ → ℝ)
    (h : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) p)
      Work.Spaces.Iθ) :
    IntegrableOn (fun x : ℝ => (iteratedDeriv j (shiftU u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) p) (Set.Icc 0 xEnd) := by
  have h1 : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) p)
      farSet := h.mono_set farSet_subset_Iθ
  have h2 := (MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_reflectC) measurableEmbedding_reflectC (s := farSet)).mpr h1
  rw [preimage_reflectC_farSet] at h2
  refine h2.congr_fun (fun x _ => ?_) measurableSet_Icc
  exact slot_integrand_reflect j p u x

/-- The same, on the half-open interval `(0, xEnd]`. -/
theorem integrableOn_shift_slot_Ioc (j : ℕ) (p : ℝ) (u : ℝ → ℝ)
    (h : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) p)
      Work.Spaces.Iθ) :
    IntegrableOn (fun x : ℝ => (iteratedDeriv j (shiftU u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) p) (Set.Ioc 0 xEnd) :=
  (integrableOn_shift_slot j p u h).mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)

end Work.FTS.EllipticEst.remov.TopCoreB
