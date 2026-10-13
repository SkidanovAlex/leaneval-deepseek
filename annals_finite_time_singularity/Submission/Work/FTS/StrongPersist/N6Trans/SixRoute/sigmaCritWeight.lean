import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Transport3Aux.sin_weight_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

/-!
# Integrability of the critical angular weight `sin(2θ)^{-(1-α/10)}` with a `C/α` bound

We prove `sigmaCritWeight`: for `α ∈ (0,1]` the function `θ ↦ sin(2θ)^{-(1-α/10)}` is integrable
on `(0,π/2)` and its integral is at most `C/α` with a universal constant.

The exponent `c := -(1 - α/10) = α/10 - 1` satisfies `-1 < c ≤ 0`, i.e. it is the borderline
integrable case.  The proof is a two-sided Jordan comparison, valid for *every* `c ∈ (-1, 0]`:

* on `(0,π/4)`, `sin(2θ) ≥ (4/π) θ`, hence (the exponent being negative)
  `sin(2θ)^c ≤ (4/π)^c θ^c`; integrating `θ^c` over `(0,π/4)` with `integral_rpow` and using
  `(4/π)^c (π/4)^{c+1} = π/4` gives `∫_0^{π/4} sin(2θ)^c ≤ (π/4)/(1+c)`;
* the mirror `θ ↦ π/2 - θ` (under which `sin 2θ` is invariant) gives the same bound on
  `(π/4,π/2)`;
* adding the halves: `∫_{(0,π/2)} sin(2θ)^c ≤ (π/2)/(1+c)`.

With `c = α/10 - 1` this is `(π/2)/(α/10) = 5π/α ≤ 20/α`.
-/

/-- **Jordan's inequality with a negative exponent.**  On `(0,π/4)`, for `c ≤ 0`,
`sin(2θ)^c ≤ (4/π)^c θ^c` (taking a negative power reverses `(4/π)θ ≤ sin 2θ`). -/
theorem sin_two_rpow_le_theta_rpow {c : ℝ} (hc : c ≤ 0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ c ≤ (4 / Real.pi) ^ c * θ ^ c := by
  have h := Work.FTS.H2.Transport3Aux.sin_rpow_sub_le_theta (β := 1 + c) (by linarith) hθ
  rwa [show (1 : ℝ) + c - 1 = c by ring] at h

/-- **The left half.**  `∫_0^{π/4} sin(2θ)^c ≤ (π/4)/(1+c)` for `-1 < c ≤ 0`. -/
theorem sin_two_rpow_half_left_le {c : ℝ} (hc : -1 < c) (hc0 : c ≤ 0) :
    (∫ θ in (0 : ℝ)..(Real.pi / 4), (Real.sin (2 * θ)) ^ c) ≤ (Real.pi / 4) / (1 + c) := by
  have hb0 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hbq : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hIL : IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) volume 0 (Real.pi / 4) :=
    Work.FTS.H2.Transport3Aux.II_sin_rpow_interval hc hb0 le_rfl hbq
  have hIg : IntervalIntegrable (fun θ : ℝ => (4 / Real.pi) ^ c * θ ^ c) volume 0
      (Real.pi / 4) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := Real.pi / 4) (r := c) hc)
      |>.const_mul _
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (Real.sin (2 * θ)) ^ c ≤ (4 / Real.pi) ^ c * θ ^ c :=
    fun θ hθ => sin_two_rpow_le_theta_rpow hc0 hθ
  have h1 := intervalIntegral.integral_mono_on_of_le_Ioo hb0 hIL hIg hpt
  have h2 : (∫ θ in (0 : ℝ)..(Real.pi / 4), (4 / Real.pi) ^ c * θ ^ c)
      = (4 / Real.pi) ^ c * ((Real.pi / 4) ^ (c + 1) / (c + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hc),
      Real.zero_rpow (by linarith : c + 1 ≠ 0)]
    ring
  calc (∫ θ in (0 : ℝ)..(Real.pi / 4), (Real.sin (2 * θ)) ^ c)
      ≤ ∫ θ in (0 : ℝ)..(Real.pi / 4), (4 / Real.pi) ^ c * θ ^ c := h1
    _ = (4 / Real.pi) ^ c * ((Real.pi / 4) ^ (c + 1) / (c + 1)) := h2
    _ = (Real.pi / 4) / (1 + c) := by
        have hq : (4 / Real.pi) ^ c * (Real.pi / 4) ^ (c + 1) = Real.pi / 4 := by
          have h := Work.FTS.H2.Transport3Aux.rpow_quarter_mul' (c + 1)
          rwa [show c + 1 - 1 = c by ring] at h
        rw [show (4 / Real.pi) ^ c * ((Real.pi / 4) ^ (c + 1) / (c + 1))
              = ((4 / Real.pi) ^ c * (Real.pi / 4) ^ (c + 1)) / (c + 1) from by ring, hq]
        ring

/-- **The mirror identity.**  `sin(2θ)` is invariant under `θ ↦ π/2 - θ`, so the two halves of
`(0,π/2)` carry the same integral. -/
theorem sin_two_rpow_mirror (c : ℝ) :
    (∫ θ in (Real.pi / 4)..(Real.pi / 2), (Real.sin (2 * θ)) ^ c)
      = ∫ θ in (0 : ℝ)..(Real.pi / 4), (Real.sin (2 * θ)) ^ c := by
  have h := (Work.FTS.H2.Transport3Aux.integral_mirror_sub
    (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)).symm
  rw [h]
  apply intervalIntegral.integral_congr
  intro u _
  show (Real.sin (2 * (Real.pi / 2 - u))) ^ c = (Real.sin (2 * u)) ^ c
  rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub]

/-- **The bound on the whole interval** `(0,π/2)`, in `IntervalIntegral` form. -/
theorem sin_two_rpow_interval_le {c : ℝ} (hc : -1 < c) (hc0 : c ≤ 0) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.sin (2 * θ)) ^ c) ≤ (Real.pi / 2) / (1 + c) := by
  have hL := sin_two_rpow_half_left_le hc hc0
  have hR : (∫ θ in (Real.pi / 4)..(Real.pi / 2), (Real.sin (2 * θ)) ^ c)
      ≤ (Real.pi / 4) / (1 + c) := by
    rw [sin_two_rpow_mirror c]; exact hL
  have hIL : IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) volume 0 (Real.pi / 4) :=
    Work.FTS.H2.Transport3Aux.II_sin_rpow_interval hc (by positivity) le_rfl
      (by linarith [Real.pi_pos])
  have hIR : IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) volume (Real.pi / 4)
      (Real.pi / 2) :=
    Work.FTS.H2.Transport3Aux.II_sin_rpow_interval hc (by linarith [Real.pi_pos])
      (by positivity) le_rfl
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals hIL hIR).symm
  rw [hsplit]
  have hsum : (Real.pi / 4) / (1 + c) + (Real.pi / 4) / (1 + c) = (Real.pi / 2) / (1 + c) := by
    ring
  linarith [hL, hR, hsum]

/-- **The bound on the set integral over `(0,π/2)`.** -/
theorem sin_two_rpow_setIntegral_le {c : ℝ} (hc : -1 < c) (hc0 : c ≤ 0) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ c) ≤ (Real.pi / 2) / (1 + c) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi]
  exact sin_two_rpow_interval_le hc hc0

/-- **Integrability.**  `θ ↦ sin(2θ)^c` is integrable on `(0,π/2)` for every `c > -1`. -/
theorem integrableOn_sin_two_rpow {c : ℝ} (hc : -1 < c) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) (Set.Ioo 0 (Real.pi / 2)) :=
  (Work.FTS.H2.intervalIntegrable_sin_rpow c hc).1.mono_set Set.Ioo_subset_Ioc_self

/-- **The critical angular weight is integrable with a bound `C/α`.**  For `α ∈ (0,1]`, the
function `θ ↦ sin(2θ)^{-(1-α/10)}` is integrable on the open interval `(0,π/2)` and its integral
is `≤ C/α` with a universal `C`.

(The exponent `-(1-α/10)` is the borderline case: `∫_0 sin(2θ)^{-(1-α/10)}` converges because
`1 - α/10 < 1`, and the exact scaling in `α` is `≈ 10/α`.)  Route: on `(0,π/4)` one has
`sin(2θ) ≥ (4/π)θ` (`Work.FTS.H2.Transport3Aux.four_div_pi_mul_le_sin_two`), so
`sin(2θ)^{-(1-α/10)} ≤ (π/4)^{1-α/10} θ^{-(1-α/10)}` with `θ^{-(1-α/10)}` integrable
(`integral_rpow`); the other half is the mirror `θ ↦ π/2 - θ`. -/
theorem sigmaCritWeight : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      (Set.Ioo 0 (Real.pi / 2)) ∧
    (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-(1 - α / 10))) ≤ C / α := by
  refine ⟨20, by norm_num, ?_⟩
  intro α hα
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hc : -1 < -(1 - α / 10) := by linarith
  have hc0 : -(1 - α / 10) ≤ 0 := by linarith
  constructor
  · exact integrableOn_sin_two_rpow hc
  · have h1 := sin_two_rpow_setIntegral_le (c := -(1 - α / 10)) hc hc0
    have h1c : 1 + -(1 - α / 10) = α / 10 := by ring
    have h2 : (Real.pi / 2) / (1 + -(1 - α / 10)) = 5 * Real.pi / α := by
      rw [h1c]
      field_simp
      ring
    have h3 : 5 * Real.pi / α ≤ 20 / α := by
      apply div_le_div_of_nonneg_right _ hα0.le
      linarith [Real.pi_le_four]
    calc (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
        ≤ (Real.pi / 2) / (1 + -(1 - α / 10)) := h1
      _ = 5 * Real.pi / α := h2
      _ ≤ 20 / α := h3

end Work.FTS.StrongPersist.N6Trans.SixRoute
