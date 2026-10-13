import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarDefs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Reflected-variable toolkit for the `g`-slot finiteness on the far window

The far window `farSet = [3π/8, π/2]` of the angular estimate is mapped to `[0, π/8]` by
`x ↦ π/2 - x`.  In the reflected variable `x`

* `gsqU u x = u (π/2 - x)` (the reflected solution slice),
* `gsqG g x = g (π/2 - x)` (the reflected source slice),
* `gsqSec x = x / sin x`, `gsqKap x = gsqSec x * cos x = x * cot x` (smooth bounded quotient),
* `gsqW u x = gsqU u x / x` (the *divided* reflected slice),

so that in the reflected variable the pointwise angular identity `g = -u'' + (tan θ·u)' - 6u`
reads

`gsqG g = -(gsqU u)'' - (gsqKap · gsqW u)' - 6 · gsqU u`,

and the derivative of the product `gsqKap · gsqW u` is controlled by the divided derivatives
`gsqW u^{(j)}` with the *bounded* coefficients `gsqKap^{(i)}`.

This file contains only the definitions and the elementary reflected-variable facts
(substitution, integrability transfer by the measure-preserving reflection, the pointwise
integrand identity, the weight comparisons and the two smoothness/limit inputs for the
division lemmas).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The reflected window -/

/-- The right endpoint `π/8` of the reflected far window `[0, π/8]`. -/
def gsqXEnd : ℝ := Real.pi / 8

theorem gsqXEnd_pos : 0 < gsqXEnd := by rw [gsqXEnd]; positivity

theorem gsqXEnd_lt_pi_half : gsqXEnd < Real.pi / 2 := by
  rw [gsqXEnd]; linarith [Real.pi_pos]

theorem gsqXEnd_le_one : gsqXEnd ≤ 1 := by
  rw [gsqXEnd]; linarith [Real.pi_pos, Real.pi_lt_four]

theorem gsqXEnd_le_pi_four : gsqXEnd ≤ Real.pi / 4 := by
  rw [gsqXEnd]; linarith [Real.pi_pos]

theorem gsqXEnd_lt_pi_four : gsqXEnd < Real.pi / 4 := by
  rw [gsqXEnd]; linarith [Real.pi_pos]

theorem gsq_three_eight_eq : 3 * Real.pi / 8 = Real.pi / 2 - gsqXEnd := by
  rw [gsqXEnd]; ring

/-! ## The reflected functions -/

/-- The reflected slice `x ↦ u (π/2 - x)`. -/
def gsqU (u : ℝ → ℝ) : ℝ → ℝ := fun x => u (Real.pi / 2 - x)

/-- The reflected source `x ↦ g (π/2 - x)`. -/
def gsqG (g : ℝ → ℝ) : ℝ → ℝ := fun x => g (Real.pi / 2 - x)

/-- The bounded quotient `x / sin x`. -/
def gsqSec (x : ℝ) : ℝ := x / Real.sin x

/-- `x * cot x = (x / sin x) * cos x`, the bounded coefficient of the reflected
`(tan θ · u)` term. -/
def gsqKap (x : ℝ) : ℝ := gsqSec x * Real.cos x

/-- The divided reflected slice `u (π/2 - x) / x`. -/
def gsqW (u : ℝ → ℝ) : ℝ → ℝ := fun x => gsqU u x / x

/-- The reflection `x ↦ π/2 - x`. -/
def gsqRefl (x : ℝ) : ℝ := Real.pi / 2 - x

theorem gsqRefl_eq (x : ℝ) : gsqRefl x = -(x - Real.pi / 2) := by
  rw [gsqRefl]; ring

/-! ## The reflection and the iterated derivative -/

/-- **Chain rule for the reflection** `θ ↦ c - θ`. -/
theorem gsq_iteratedDeriv_comp_const_sub (n : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    iteratedDeriv n (fun x => f (c - x)) = fun x => (-1) ^ n * iteratedDeriv n f (c - x) := by
  have h := iteratedDerivWithin_comp_const_sub (𝕜 := ℝ) (f := f) (s := Set.univ) (n := n) c
  simpa using h

theorem gsq_sin_two_pi_half_sub (x : ℝ) : Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

theorem gsq_cos_pi_half_sub (x : ℝ) : Real.cos (Real.pi / 2 - x) = Real.sin x :=
  Real.cos_pi_div_two_sub x

theorem gsq_sin_pi_half_sub (x : ℝ) : Real.sin (Real.pi / 2 - x) = Real.cos x :=
  Real.sin_pi_div_two_sub x

/-- `qW k γ` is invariant under the reflection. -/
theorem gsq_qW_refl (k : ℕ) (γ x : ℝ) : qW k γ (Real.pi / 2 - x) = qW k γ x := by
  simp only [qW, gsq_sin_two_pi_half_sub]

/-! ## Substitution and integrability transfer -/

/-- **Substitution `θ = π/2 - x` on the far window.** -/
theorem gsq_integral_farSet_eq (F : ℝ → ℝ) :
    (∫ θ in farSet, F θ) = ∫ x in (0 : ℝ)..gsqXEnd, F (Real.pi / 2 - x) := by
  have hIcc : farSet = Set.Icc (3 * Real.pi / 8) (Real.pi / 2) := rfl
  have hle : (3 : ℝ) * Real.pi / 8 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [hIcc, setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := 3 * Real.pi / 8)
      (b := Real.pi / 2)).symm, ← intervalIntegral.integral_of_le hle]
  have h := intervalIntegral.integral_comp_sub_left (fun y : ℝ => F (Real.pi / 2 - y))
    (Real.pi / 2) (a := 3 * Real.pi / 8) (b := Real.pi / 2)
  simp only [sub_sub_cancel] at h
  rw [show Real.pi / 2 - 3 * Real.pi / 8 = gsqXEnd by rw [gsqXEnd]; ring,
    show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring] at h
  exact h

theorem gsq_measurePreserving_refl : MeasurePreserving gsqRefl volume volume := by
  have h : MeasurePreserving (fun x : ℝ => -(x - Real.pi / 2)) volume volume :=
    (Measure.measurePreserving_neg volume).comp
      (measurePreserving_sub_right volume (Real.pi / 2))
  have hfun : gsqRefl = fun x : ℝ => -(x - Real.pi / 2) := by
    funext x; rw [gsqRefl_eq]
  rwa [hfun]

theorem gsq_measurableEmbedding_refl : MeasurableEmbedding gsqRefl := by
  have h : MeasurableEmbedding (fun x : ℝ => -(x - Real.pi / 2)) :=
    measurableEmbedding_neg.comp (measurableEmbedding_subRight (Real.pi / 2))
  have hfun : gsqRefl = fun x : ℝ => -(x - Real.pi / 2) := by
    funext x; rw [gsqRefl_eq]
  rwa [hfun]

theorem gsq_preimage_refl_farSet : gsqRefl ⁻¹' farSet = Set.Icc 0 gsqXEnd := by
  have hfun : gsqRefl = fun x : ℝ => Real.pi / 2 - x := rfl
  ext x
  rw [hfun]
  simp only [mem_preimage, farSet, mem_Icc, gsqXEnd]
  constructor
  · intro h; exact ⟨by linarith [h.2, Real.pi_pos], by linarith [h.1]⟩
  · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **Integrability transfer.**  A function is integrable on the far window iff its reflection
is integrable on `[0, π/8]`. -/
theorem gsq_integrableOn_iff (F : ℝ → ℝ) :
    IntegrableOn F farSet ↔
      IntegrableOn (fun x => F (Real.pi / 2 - x)) (Set.Icc 0 gsqXEnd) := by
  have h := (MeasurePreserving.integrableOn_comp_preimage gsq_measurePreserving_refl
    gsq_measurableEmbedding_refl (s := farSet) (f := F)).symm
  rw [gsq_preimage_refl_farSet] at h
  simpa [gsqRefl, Function.comp_def] using h

/-- The reflected integrand identity for a general function `f` and exponent `p`. -/
theorem gsq_integrand_reflect (l : ℕ) (p : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (iteratedDeriv l f (Real.pi / 2 - x)) ^ 2
        * Real.rpow (Real.sin (2 * (Real.pi / 2 - x))) p
      = (iteratedDeriv l (fun y => f (Real.pi / 2 - y)) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) p := by
  have h := congrFun (gsq_iteratedDeriv_comp_const_sub l f (Real.pi / 2)) x
  have h' : iteratedDeriv l (fun y => f (Real.pi / 2 - y)) x
      = (-1) ^ l * iteratedDeriv l f (Real.pi / 2 - x) := h
  have hsq : (iteratedDeriv l f (Real.pi / 2 - x)) ^ 2
      = (iteratedDeriv l (fun y => f (Real.pi / 2 - y)) x) ^ 2 := by
    have hp : ((-1 : ℝ) ^ l) ^ 2 = 1 := by
      rw [← pow_mul, show l * 2 = 2 * l by ring, pow_mul]; norm_num
    rw [h', mul_pow, hp, one_mul]
  rw [gsq_sin_two_pi_half_sub, hsq]

/-- The reflected `l`-th derivative, up to sign (squared, so signless). -/
theorem gsq_g_iteratedDeriv_refl (l : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    (iteratedDeriv l g (Real.pi / 2 - x)) ^ 2 = (iteratedDeriv l (gsqG g) x) ^ 2 := by
  have h := congrFun (gsq_iteratedDeriv_comp_const_sub l g (Real.pi / 2)) x
  have h' : iteratedDeriv l (gsqG g) x
      = (-1) ^ l * iteratedDeriv l g (Real.pi / 2 - x) := h
  have hp : ((-1 : ℝ) ^ l) ^ 2 = 1 := by
    rw [← pow_mul, show l * 2 = 2 * l by ring, pow_mul]; norm_num
  rw [h', mul_pow, hp, one_mul]

/-- The reflected `qW`-weighted `g`-integrand identity. -/
theorem gsq_g_integrand_reflect (k : ℕ) (γ : ℝ) (l : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    qW k γ (Real.pi / 2 - x) * (iteratedDeriv l g (Real.pi / 2 - x)) ^ 2
      = qW k γ x * (iteratedDeriv l (gsqG g) x) ^ 2 := by
  rw [gsq_qW_refl, gsq_g_iteratedDeriv_refl]

/-- Integrability of a reflected slot, transferred from the angular interval `Iθ`. -/
theorem gsq_slot_integrable_transfer (j : ℕ) (p : ℝ) (u : ℝ → ℝ)
    (h : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) p) Work.Spaces.Iθ) :
    IntegrableOn (fun x : ℝ => (iteratedDeriv j (gsqU u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) p) (Set.Icc 0 gsqXEnd) := by
  have h1 : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) p) farSet := h.mono_set farSet_subset_Iθ
  have h2 := (MeasurePreserving.integrableOn_comp_preimage gsq_measurePreserving_refl
    gsq_measurableEmbedding_refl (s := farSet)).mpr h1
  rw [gsq_preimage_refl_farSet] at h2
  refine h2.congr_fun (fun x _ => ?_) measurableSet_Icc
  exact gsq_integrand_reflect j p u x

/-! ## Weight comparisons on the reflected window -/

/-- On `[0, π/8]` one has `x ≤ sin (2x)`. -/
theorem gsq_x_le_sin_two {x : ℝ} (hx : x ∈ Set.Icc 0 gsqXEnd) : x ≤ Real.sin (2 * x) := by
  have hx8 : x ≤ Real.pi / 8 := by rw [gsqXEnd] at hx; exact hx.2
  have h2x : 2 * x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hm : 2 / Real.pi * (2 * x) ≤ Real.sin (2 * x) :=
    Real.mul_le_sin (by linarith [hx.1]) h2x
  have hrew : (Real.pi / 4) * (2 / Real.pi * (2 * x)) = x := by field_simp; ring
  calc x = (Real.pi / 4) * (2 / Real.pi * (2 * x)) := hrew.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * x) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ 1 * Real.sin (2 * x) := by
        refine mul_le_mul_of_nonneg_right ?_
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [Real.pi_pos]⟩)
        linarith [Real.pi_lt_four]
    _ = Real.sin (2 * x) := one_mul _

/-- On `(0, π/8]` the double-angle sine is positive. -/
theorem gsq_sin_two_pos {x : ℝ} (hx : x ∈ Set.Ioc 0 gsqXEnd) : 0 < Real.sin (2 * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by
    have h := hx.2; rw [gsqXEnd] at h; linarith [Real.pi_pos])

/-- **Weight comparison, nonnegative exponent.**  For `p ≥ 0` and `x ∈ [0, π/8]`,
`x^p ≤ sin(2x)^p`. -/
theorem gsq_rpow_x_le_sin_two {p : ℝ} (hp : 0 ≤ p) {x : ℝ} (hx : x ∈ Set.Icc 0 gsqXEnd) :
    x ^ p ≤ Real.rpow (Real.sin (2 * x)) p :=
  Real.rpow_le_rpow hx.1 (gsq_x_le_sin_two hx) hp

/-- `sin(2x) ≤ 2x` on `[0, π/8]`. -/
theorem gsq_sin_two_le_two_mul {x : ℝ} (hx : 0 ≤ x) : Real.sin (2 * x) ≤ 2 * x :=
  Real.sin_le (by linarith)

/-- **Weight comparison, upper bound.**  For `0 ≤ p ≤ 2k` and `x ∈ (0, π/8]`,
`sin(2x)^p ≤ 2^{2k} x^p`. -/
theorem gsq_sin_two_rpow_le {p : ℝ} (hp : 0 ≤ p) {k : ℕ} (hpk : p ≤ 2 * (k : ℝ)) {x : ℝ}
    (hx : x ∈ Set.Ioc 0 gsqXEnd) :
    Real.rpow (Real.sin (2 * x)) p ≤ (2 : ℝ) ^ (2 * k) * x ^ p := by
  have hsin0 : 0 ≤ Real.sin (2 * x) := le_of_lt (gsq_sin_two_pos hx)
  have h1 : Real.rpow (Real.sin (2 * x)) p ≤ (2 * x) ^ p :=
    Real.rpow_le_rpow hsin0 (gsq_sin_two_le_two_mul hx.1.le) hp
  have h2 : (2 * x) ^ p = 2 ^ p * x ^ p := Real.mul_rpow (by norm_num) hx.1.le
  have h3 : 2 ^ p ≤ (2 : ℝ) ^ (2 * k) := by
    have hpc : p ≤ ((2 * k : ℕ) : ℝ) := by
      push_cast
      linarith [hpk]
    calc 2 ^ p ≤ (2 : ℝ) ^ ((2 * k : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hpc
      _ = (2 : ℝ) ^ (2 * k) := Real.rpow_natCast 2 (2 * k)
  rw [h2] at h1
  calc Real.rpow (Real.sin (2 * x)) p ≤ 2 ^ p * x ^ p := h1
    _ ≤ (2 : ℝ) ^ (2 * k) * x ^ p :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hx.1.le p)

/-! ## Smoothness and the limit at `0⁺` of the reflected slice -/

/-- Reflected smoothness, on the full open interval `(0, π/2)`. -/
theorem gsq_contDiffOn_gsqU {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (gsqU u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : ContDiffOn ℝ n (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hmt : MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  exact hu.comp hmap hmt

/-- The reflected slice on the half-open interval `(0, π/8]`. -/
theorem gsq_contDiffOn_gsqU_Ioc {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (gsqU u) (Set.Ioc 0 gsqXEnd) :=
  (gsq_contDiffOn_gsqU hu).mono fun _ hx => ⟨hx.1, lt_of_le_of_lt hx.2 gsqXEnd_lt_pi_half⟩

/-- The reflected slice tends to `u (π/2) = 0` at `0⁺`. -/
theorem gsq_tendsto_gsqU {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu1 : u (Real.pi / 2) = 0) :
    Tendsto (gsqU u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hcont : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)))
      (nhds (u (Real.pi / 2))) := hu.continuousWithinAt hmem
  have hshift : Tendsto (fun x : ℝ => Real.pi / 2 - x) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun x : ℝ => Real.pi / 2 - x) 0 := by fun_prop
      have h1 : Tendsto (fun x : ℝ => Real.pi / 2 - x) (nhds (0 : ℝ))
          (nhds (Real.pi / 2 - 0)) := hc.tendsto
      simpa using h1.mono_left nhdsWithin_le_nhds
    · have hmemIio : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
      filter_upwards [self_mem_nhdsWithin, hmemIio] with x hxpos hxlt
      have hx0 : (0 : ℝ) < x := hxpos
      have hx1 : x < Real.pi / 2 := hxlt
      exact ⟨by linarith, le_of_lt (by linarith : Real.pi / 2 - x < Real.pi / 2)⟩
  have h := hcont.comp hshift
  change Tendsto (fun x : ℝ => u (Real.pi / 2 - x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  simpa [Function.comp_def, hu1] using h

end Work.FTS.EllipticEst.remov.TopCoreB
