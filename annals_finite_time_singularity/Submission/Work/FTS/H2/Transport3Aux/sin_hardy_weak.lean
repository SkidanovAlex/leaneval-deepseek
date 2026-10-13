import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.Transport3Aux.num_int_1d_aux
import Submission.Work.FTS.H2.Transport3Aux.HW.hardy_half_a_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sin(2θ)`-weighted Hardy inequality (weak hypotheses) on `Iθ = [0,π/2]`

`Work.FTS.H2.Transport3Aux.sin_hardy_weak`: for `0 < β ≤ 1` and `f` continuous on `[0,π/2]`,
differentiable with continuous derivative on the open interval,

`∫_Iθ f² sin(2θ)^{β-1} ≤ (4/β²) ∫_Iθ (f')² sin(2θ)^{1-β} + (4/β) f(π/4)²`.

The two weights are reciprocal; the boundary term at the *interior* point `π/4` is essential
(the inequality is false without it, e.g. for constant `f` as `β → 0`).

Proof: split `Iθ` at `π/4`.  On each half, the sharp power-weighted Hardy inequality with its
boundary term (`Work.FTS.H2.Transport3Aux.hardy_power_weak`, applied with exponent `a = β-1`)
together with Jordan's inequality `(4/π)θ ≤ sin(2θ) ≤ 1` on `[0,π/4]` gives

`∫_0^{π/4} f² sin(2θ)^{β-1} ≤ (4/β²)(π/4)² ∫_0^{π/4}(f')² sin(2θ)^{1-β} + (π/2β) f(π/4)²`,

and the mirror image `θ ↦ π/2 - θ` (under which `sin 2θ` is invariant) gives the same on
`[π/4,π/2]`.  Adding the two halves and using `(π/4)² ≤ 1`, `π ≤ 4` yields the claim.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option maxHeartbeats 1000000

/-- The derivative of the mirror `u ↦ f (π/2 - u)` at an interior point, under the weak
hypotheses of `sin_hardy_weak` (no `C¹`-on-the-closed-interval hypothesis). -/
theorem deriv_mirror_weak {f : ℝ → ℝ}
    (hder : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt f (deriv f θ) θ) :
    ∀ u ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      deriv (fun u : ℝ => f (Real.pi/2 - u)) u = - deriv f (Real.pi/2 - u) := by
  intro u hu
  have hu' : Real.pi/2 - u ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
    ⟨by linarith [hu.2, Real.pi_pos], by linarith [hu.1]⟩
  have h1 : HasDerivAt (fun u : ℝ => Real.pi/2 - u) (-1) u := by
    have h := (hasDerivAt_id u).const_sub (Real.pi/2)
    simpa using h
  have h2 : HasDerivAt (fun u : ℝ => f (Real.pi/2 - u)) (deriv f (Real.pi/2 - u) * (-1)) u := by
    have h := (hder (Real.pi/2 - u) hu').comp u h1
    simpa only [Function.comp_def] using h
  rw [h2.deriv]
  ring

/-- The mirror identity for the `(f')²`-integral, under the weak hypotheses of `sin_hardy_weak`
(`sin 2θ` is invariant under `θ ↦ π/2 - θ`). -/
theorem mirror_deriv_sq_integral_weak {β : ℝ} {f : ℝ → ℝ}
    (hder : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt f (deriv f θ) θ) :
    (∫ u in (0:ℝ)..(Real.pi/4),
        (deriv (fun u : ℝ => f (Real.pi/2 - u)) u)^2 * (Real.sin (2*u))^(1-β))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ)^2 * (Real.sin (2*θ))^(1-β) := by
  rw [← integral_mirror_sub (fun θ : ℝ => (deriv f θ)^2 * (Real.sin (2*θ))^(1-β))]
  refine integral_congr_Ioo (by positivity : (0:ℝ) ≤ Real.pi/4) (fun u hu => ?_)
  rw [deriv_mirror_weak hder u ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩]
  have hsin : Real.sin (2 * (Real.pi/2 - u)) = Real.sin (2*u) := by
    rw [show 2 * (Real.pi/2 - u) = Real.pi - 2*u by ring, Real.sin_pi_sub]
  rw [hsin]
  ring

/-- A set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
theorem Iθ_setIntegral_eq_interval (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0:ℝ)..(Real.pi/2), g θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]

theorem sin_hardy_weak {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hcont : ContinuousOn f Work.Spaces.Iθ)
    (hder : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt f (deriv f θ) θ)
    (hdcont : ContinuousOn (deriv f) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (f θ)^2 * (Real.sin (2*θ))^(β-1))
      ≤ 4/β^2 * (∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 * (Real.sin (2*θ))^(1-β))
        + (4/β) * (f (Real.pi/4))^2 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hp2 : (0:ℝ) ≤ Real.pi/2 := by linarith
  have hb0 : (0:ℝ) ≤ Real.pi/4 := by linarith
  have hb2 : Real.pi/4 ≤ Real.pi/2 := by linarith
  have hz : (0:ℝ) ≤ (f (Real.pi/4))^2 := sq_nonneg _
  -- boundedness of `deriv f` on the interval
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hdcont
  have hbdd : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), |deriv f θ| ≤ Cf := by
    intro θ hθ
    have h := hCf θ ⟨hθ.1.le, hθ.2.le⟩
    simpa only [Real.norm_eq_abs] using h
  -- the mirrored function and its data
  have hcontm : ContinuousOn (fun u : ℝ => f (Real.pi/2 - u)) (Set.Icc 0 (Real.pi/2)) := by
    refine hcont.comp (continuousOn_const.sub continuousOn_id) ?_
    intro x hx
    exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
  have hderm : ∀ u ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => f (Real.pi/2 - u))
        (deriv (fun u : ℝ => f (Real.pi/2 - u)) u) u := by
    intro u hu
    have hu' : Real.pi/2 - u ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
      ⟨by linarith [hu.2, Real.pi_pos], by linarith [hu.1]⟩
    have h1 : HasDerivAt (fun u : ℝ => Real.pi/2 - u) (-1) u := by
      have h := (hasDerivAt_id u).const_sub (Real.pi/2)
      simpa using h
    have h2 : HasDerivAt (fun u : ℝ => f (Real.pi/2 - u)) (deriv f (Real.pi/2 - u) * (-1)) u := by
      have h := (hder (Real.pi/2 - u) hu').comp u h1
      simpa only [Function.comp_def] using h
    rw [h2.deriv]
    exact h2
  have hbddm : ∀ u ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      |deriv (fun u : ℝ => f (Real.pi/2 - u)) u| ≤ Cf := by
    intro u hu
    rw [deriv_mirror_weak hder u hu]
    simpa using hbdd (Real.pi/2 - u) ⟨by linarith [hu.2, Real.pi_pos], by linarith [hu.1]⟩
  -- the two half-interval Hardy bounds
  have hA1 := HW.hardy_half_a_weak (f := f) hβ hβ1 hcont hder hbdd
  have hA2raw := HW.hardy_half_a_weak (f := fun u : ℝ => f (Real.pi/2 - u))
    hβ hβ1 hcontm hderm hbddm
  have hfm : f (Real.pi/2 - Real.pi/4) = f (Real.pi/4) := by
    congr 1
    ring
  rw [mirror_sq_sin_rpow (β-1) f, mirror_deriv_sq_integral_weak (β := β) hder, hfm] at hA2raw
  -- integrability, in order to split the interval integrals at `π/4`
  have hcontf : ContinuousOn (fun θ : ℝ => (f θ)^2) (Set.uIcc 0 (Real.pi/2)) := by
    rw [Set.uIcc_of_le hp2]
    exact hcont.pow 2
  have hcontdf : ContinuousOn (fun θ : ℝ => (deriv f θ)^2) (Set.uIcc 0 (Real.pi/2)) := by
    rw [Set.uIcc_of_le hp2]
    exact hdcont.pow 2
  have hsub01 : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hb0, Set.uIcc_of_le hp2]
    exact fun x hx => ⟨hx.1, le_trans hx.2 hb2⟩
  have hsub12 : Set.uIcc (Real.pi/4) (Real.pi/2) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hb2, Set.uIcc_of_le hp2]
    exact fun x hx => ⟨le_trans hb0 hx.1, hx.2⟩
  have hIntF : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * (Real.sin (2*θ))^(β-1))
      volume 0 (Real.pi/2) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β-1) hp2 le_rfl le_rfl) hcontf
  have hIntD : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * (Real.sin (2*θ))^(1-β))
      volume 0 (Real.pi/2) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < 1-β) hp2 le_rfl le_rfl) hcontdf
  have hIntF1 := hIntF.mono_set hsub01
  have hIntF2 := hIntF.mono_set hsub12
  have hIntD1 := hIntD.mono_set hsub01
  have hIntD2 := hIntD.mono_set hsub12
  -- convert the set integrals and split both of them
  rw [Iθ_setIntegral_eq_interval (fun θ => (f θ)^2 * (Real.sin (2*θ))^(β-1)),
    Iθ_setIntegral_eq_interval (fun θ => (deriv f θ)^2 * (Real.sin (2*θ))^(1-β))]
  rw [← intervalIntegral.integral_add_adjacent_intervals hIntF1 hIntF2,
    ← intervalIntegral.integral_add_adjacent_intervals hIntD1 hIntD2]
  set D1 : ℝ := ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ)^2 * (Real.sin (2*θ))^(1-β) with hD1
  set D2 : ℝ := ∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ)^2 * (Real.sin (2*θ))^(1-β) with hD2
  have hstep : (∫ θ in (0:ℝ)..(Real.pi/4), (f θ)^2 * (Real.sin (2*θ))^(β-1))
        + (∫ θ in (Real.pi/4)..(Real.pi/2), (f θ)^2 * (Real.sin (2*θ))^(β-1))
      ≤ (4/β^2 * (Real.pi/4)^2 * D1 + Real.pi/(2*β) * (f (Real.pi/4))^2)
        + (4/β^2 * (Real.pi/4)^2 * D2 + Real.pi/(2*β) * (f (Real.pi/4))^2) :=
    add_le_add hA1 hA2raw
  have hDsum : (0:ℝ) ≤ D1 + D2 := by
    have h1 : (0:ℝ) ≤ D1 := by
      rw [hD1]
      exact intervalIntegral.integral_nonneg hb0 (fun u hu => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Icc ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩) _))
    have h2 : (0:ℝ) ≤ D2 := by
      rw [hD2]
      exact intervalIntegral.integral_nonneg hb2 (fun u hu => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Icc ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩) _))
    linarith
  have hpi4 : (Real.pi/4)^2 ≤ 1 := by
    have h1 : Real.pi/4 ≤ 1 := by linarith [Real.pi_le_four]
    nlinarith [h1, Real.pi_pos]
  have hcoef1 : 4/β^2 * (Real.pi/4)^2 ≤ 4/β^2 := by
    have h0 : (0:ℝ) < 4/β^2 := by positivity
    nlinarith [hpi4, h0]
  have hcoef2 : Real.pi/(2*β) + Real.pi/(2*β) ≤ 4/β := by
    have h1 : Real.pi/(2*β) + Real.pi/(2*β) = Real.pi/β := by
      field_simp
      ring
    rw [h1, div_le_div_iff_of_pos_right hβ]
    linarith [Real.pi_le_four]
  have hb1 : 4/β^2 * (Real.pi/4)^2 * (D1 + D2) ≤ 4/β^2 * (D1 + D2) :=
    mul_le_mul_of_nonneg_right hcoef1 hDsum
  have hb2' : (Real.pi/(2*β) + Real.pi/(2*β)) * (f (Real.pi/4))^2 ≤ 4/β * (f (Real.pi/4))^2 :=
    mul_le_mul_of_nonneg_right hcoef2 hz
  have hmid : (4/β^2 * (Real.pi/4)^2 * D1 + Real.pi/(2*β) * (f (Real.pi/4))^2)
        + (4/β^2 * (Real.pi/4)^2 * D2 + Real.pi/(2*β) * (f (Real.pi/4))^2)
      = 4/β^2 * (Real.pi/4)^2 * (D1 + D2)
        + (Real.pi/(2*β) + Real.pi/(2*β)) * (f (Real.pi/4))^2 := by
    ring
  calc (∫ θ in (0:ℝ)..(Real.pi/4), (f θ)^2 * (Real.sin (2*θ))^(β-1))
        + (∫ θ in (Real.pi/4)..(Real.pi/2), (f θ)^2 * (Real.sin (2*θ))^(β-1))
      ≤ (4/β^2 * (Real.pi/4)^2 * D1 + Real.pi/(2*β) * (f (Real.pi/4))^2)
        + (4/β^2 * (Real.pi/4)^2 * D2 + Real.pi/(2*β) * (f (Real.pi/4))^2) := hstep
    _ = 4/β^2 * (Real.pi/4)^2 * (D1 + D2)
        + (Real.pi/(2*β) + Real.pi/(2*β)) * (f (Real.pi/4))^2 := hmid
    _ ≤ 4/β^2 * (D1 + D2) + 4/β * (f (Real.pi/4))^2 := add_le_add hb1 hb2'

end Work.FTS.H2.Transport3Aux
