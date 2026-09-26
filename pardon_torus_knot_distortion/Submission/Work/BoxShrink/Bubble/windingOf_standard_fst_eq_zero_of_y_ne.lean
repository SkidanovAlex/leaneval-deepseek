import Mathlib
import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq

/-!
# A curve of the standard torus avoiding the plane `y = 0` has zero longitude winding

On the standard torus of revolution the second coordinate of a point of the surface is
`(2 + cos φ) · sin θ`, where `θ` is the *longitude* parameter and `φ` the *meridian* parameter
(`Work.Core.torusMap_apply_one`).  Since `2 + cos φ ≥ 1 > 0`, a closed curve `γ` of the surface
satisfying `(γ t) 1 ≠ 0` for every `t` has `sin (Θ t) ≠ 0` along a lift, where `Θ` is the
longitude component of the lift (`Work.CoreTopology.LiftOf`).

As `ℝ` is connected and `Θ` is continuous, `Θ` then stays inside a single connected component of
`ℝ ∖ πℤ`: more precisely no interval `[Θ s, Θ t]` can contain a multiple of `π`, so
`|Θ t - Θ s| < π` for all `s, t`.  Applying this with `s = 0`, `t = 2π` and using that the
longitude component advances by `(winding).1 · 2π` over one period (`LiftOf.winding_spec`) gives
`|(winding).1 · 2π| < π`, hence `(winding).1 = 0`.

This is the elementary geometric input of the box-shrink chapter: a loop contained in the open
half of the standard torus cut by the plane `y = 0` cannot wind around the axis.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- Any real interval of length at least `π` contains an integer multiple of `π` in its
interior-to-the-right: if `x + π ≤ y` there is `m : ℤ` with `x < m · π ≤ y`. -/
lemma exists_int_mul_pi_between {x y : ℝ} (h : x + Real.pi ≤ y) :
    ∃ m : ℤ, x < (m : ℝ) * Real.pi ∧ (m : ℝ) * Real.pi ≤ y := by
  refine ⟨⌊x / Real.pi⌋ + 1, ?_, ?_⟩
  · have hlt : x / Real.pi < ((⌊x / Real.pi⌋ + 1 : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one (x / Real.pi)
      push_cast
      linarith
    exact (div_lt_iff₀ Real.pi_pos).mp hlt
  · have hle : ((⌊x / Real.pi⌋ : ℤ) : ℝ) ≤ x / Real.pi := Int.floor_le _
    have h1 : ((⌊x / Real.pi⌋ : ℤ) : ℝ) * Real.pi ≤ x := (le_div_iff₀ Real.pi_pos).mp hle
    have : ((⌊x / Real.pi⌋ + 1 : ℤ) : ℝ) * Real.pi ≤ x + Real.pi := by
      push_cast
      nlinarith [Real.pi_pos]
    linarith

/-- A continuous real function avoiding the zeros of `sin` is *not* monotone across a multiple of
`π`: any two of its values differ by less than `π`.  (Equivalently, its image lies in one
connected component of `ℝ ∖ πℤ`.) -/
lemma abs_sub_lt_pi_of_sin_ne_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, Real.sin (f t) ≠ 0) (s t : ℝ) : |f t - f s| < Real.pi := by
  -- if `f b - f a ≥ π` then `[f a, f b]` contains a multiple of `π`, at which `sin` vanishes
  have hstep : ∀ {a b : ℝ}, Real.pi ≤ f b - f a → False := by
    intro a b hab
    obtain ⟨m, hlt, hle⟩ := exists_int_mul_pi_between (x := f a) (y := f b) (by linarith)
    have hmem : (m : ℝ) * Real.pi ∈ Set.Icc (f a) (f b) := ⟨le_of_lt hlt, hle⟩
    obtain ⟨c, hc⟩ := intermediate_value_univ a b hf hmem
    exact h c (by rw [hc, Real.sin_int_mul_pi])
  by_contra hcon
  have hge : Real.pi ≤ |f t - f s| := le_of_not_gt hcon
  rcases le_total 0 (f t - f s) with hpos | hneg
  · have habs : |f t - f s| = f t - f s := abs_of_nonneg hpos
    exact hstep (a := s) (b := t) (by linarith)
  · have habs : |f t - f s| = -(f t - f s) := abs_of_nonpos hneg
    exact hstep (a := t) (b := s) (by linarith)

theorem windingOf_standard_fst_eq_zero_of_y_ne
    {γ : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard}
    (h : ∀ t : ℝ, (γ.γ t) 1 ≠ 0) :
    (Work.SurgeryInvariance.windingOf Work.CoreTopology.standard γ).1 = 0 := by
  -- a lift of `γ` to the parameter plane, and the winding vector read off from it
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf Work.CoreTopology.standard γ
  rw [Work.SurgeryInvariance.windingOf_eq Work.CoreTopology.standard γ L]
  -- the second coordinate of a point of the standard torus is `(2 + cos φ) · sin θ`, so the
  -- longitude component `L.Θ` of the lift avoids the zeros of `sin`
  have hsin : ∀ t : ℝ, Real.sin (L.Θ t) ≠ 0 := by
    intro t
    have hcoord : (2 + Real.cos (L.Φ t)) * Real.sin (L.Θ t) = (γ.γ t) 1 := by
      have hl := congrArg (fun u : R3 => u 1) (L.lifts t)
      simpa only [Work.CoreTopology.standard_psi, Work.CoreTopology.torusMap_apply_one] using hl
    exact (mul_ne_zero_iff.mp (by rw [hcoord]; exact h t)).2
  -- hence the longitude component cannot advance by a full `π` over one period
  have hbdd : |L.Θ (2 * Real.pi) - L.Θ 0| < Real.pi :=
    abs_sub_lt_pi_of_sin_ne_zero L.contΘ hsin 0 (2 * Real.pi)
  have hsub : L.Θ (2 * Real.pi) - L.Θ 0 = ((L.winding).1 : ℝ) * (2 * Real.pi) := by
    rw [L.winding_spec.1]; ring
  rw [hsub] at hbdd
  have h2 : |((L.winding).1 : ℝ)| * (2 * Real.pi) < Real.pi := by
    rwa [abs_mul, abs_of_pos (show (0:ℝ) < 2 * Real.pi by positivity)] at hbdd
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  have h3 : |((L.winding).1 : ℝ)| < 1 / 2 := by
    have h2' := (div_lt_div_iff_of_pos_right hp).mpr h2
    have hsimp : (|((L.winding).1 : ℝ)| * (2 * Real.pi)) / (2 * Real.pi) =
        |((L.winding).1 : ℝ)| := mul_div_cancel_right₀ _ (ne_of_gt hp)
    rw [hsimp] at h2'
    have hπ : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp
    rwa [hπ] at h2'
  -- an integer whose absolute value is `< 1/2` is `0`
  have hlt := abs_lt.mp h3
  have hz1 : (-1 : ℤ) < (L.winding).1 := by
    have : ((-1 : ℤ) : ℝ) < ((L.winding).1 : ℝ) := by push_cast; linarith [hlt.1]
    exact_mod_cast this
  have hz2 : (L.winding).1 < 1 := by
    have : ((L.winding).1 : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith [hlt.2]
    exact_mod_cast this
  omega

end

end Work.BoxShrink.Bubble
