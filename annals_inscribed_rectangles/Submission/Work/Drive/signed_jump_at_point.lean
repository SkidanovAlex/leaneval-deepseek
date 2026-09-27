import Mathlib
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.SeparationBase
import Submission.Work.Drive.rot90
import Submission.Work.Drive.curve_normal_segment
import Submission.Work.Drive.winding_pair_ne
import Submission.Work.Drive.smooth_jordan_separation
import Submission.Work.Drive.winding_preconnected
import Submission.Work.Drive.winding_zero_far
import Submission.Work.Drive.ratio_loop
import Submission.Work.Drive.curve_ratio_local

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

/-!
# The signed local jump of the winding number at a point of the curve

At a point `curve γ t₀` of a smooth embedded closed plane curve, the two points
`curve γ t₀ ± ε • rot90 (deriv (curve γ) t₀)` (small `ε > 0`) lie on opposite sides of the curve and
off it, and the winding number about the point on the *left* of the traversal (the direction
`rot90` of the tangent) exceeds the winding number about the point on the right by exactly `2` (the
`dirC`-normalisation of this workspace, where a full turn of the position direction counts `2`).

The mathematical content is the `t₀ = 0` case (the proof of `Work.Drive.windE_two_sided` and of
`Work.Drive.smooth_jordan_separation`), transported to a general base point `t₀` by re-parametrising
the curve, `s ↦ curve γ (t₀ + s)`.  The one genuinely new ingredient is that the loop whose degree
computes the difference of the winding numbers is the ratio loop of the parametrisation `gammaU γ`,
which is the ratio loop of the re-parametrised curve *rotated* by `t₀/(2π)`; the invariance of the
degree under that rotation (`Work.Drive.degree_comp_add_right`) closes the gap.
-/

/-! ## Re-parametrising a closed plane curve -/

/-- Re-parametrisation of `curve γ` sending `0` to the parameter `t₀`. -/
lemma continuous_curve_add (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (t₀ : ℝ) :
    Continuous (fun s : ℝ => curve γ (t₀ + s)) :=
  (contDiff_curve γ hγ).continuous.comp (continuous_const.add continuous_id)

/-- The derivative of the re-parametrised curve at `0` is the derivative of `curve γ` at `t₀`. -/
lemma hasDerivAt_curve_add {γ : Circle → ℝ × ℝ} {V : ℝ × ℝ} {t₀ : ℝ}
    (hV : HasDerivAt (curve γ) V t₀) :
    HasDerivAt (fun s : ℝ => curve γ (t₀ + s)) V 0 := by
  have h1 : HasDerivAt (curve γ) V (t₀ + 0) := by simpa using hV
  exact h1.comp_const_add t₀ 0

lemma periodic_curve_add (γ : Circle → ℝ × ℝ) (t₀ s : ℝ) :
    curve γ (t₀ + (s + 2 * Real.pi)) = curve γ (t₀ + s) := by
  rw [show t₀ + (s + 2 * Real.pi) = (t₀ + s) + 2 * Real.pi by ring,
    curve_periodic γ (t₀ + s)]

lemma periodic_curve_add' (γ : Circle → ℝ × ℝ) (t₀ s : ℝ) :
    curve γ (t₀ + (s - 2 * Real.pi)) = curve γ (t₀ + s) := by
  rw [show t₀ + (s - 2 * Real.pi) = t₀ + s - 2 * Real.pi by ring]
  have h := curve_periodic γ (t₀ + s - 2 * Real.pi)
  rw [show t₀ + s - 2 * Real.pi + 2 * Real.pi = t₀ + s by ring] at h
  exact h.symm

lemma eq_of_curve_add_eq (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (t₀ : ℝ) {s t : ℝ}
    (h : curve γ (t₀ + s) = curve γ (t₀ + t)) : ∃ k : ℤ, s = t + 2 * Real.pi * k := by
  obtain ⟨k, hk⟩ := (curve_eq_iff γ hγ (t₀ + s) (t₀ + t)).mp h
  exact ⟨k, by linarith⟩

/-! ## The signed jump at a fixed small `ε` -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The signed jump of the winding number at a point of a smooth embedded closed plane curve,
with a fixed `ε`.**  Let `γ` be a smooth embedded closed plane curve, `t₀` a parameter, `V` its
derivative at `t₀` (hypothesis `hV`), and `ε > 0` small enough that the curve meets the normal line
`curve γ t₀ + span (rot90 V)` only at the base point, within the segment of half-length `ε`
(hypothesis `hseg`, which is what `Work.Drive.curve_normal_segment` supplies after re-parametrising
`γ` so that `t₀` becomes `0`).  Then the two points `curve γ t₀ ± ε • rot90 V` are off the curve, and
the winding number about the point on the `rot90` (left) side exceeds the one about the point on the
other (right) side by exactly `2`. -/
theorem windE_jump_of_normal_aux (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {t₀ : ℝ} {V : ℝ × ℝ}
    (hV : HasDerivAt (curve γ) V t₀) {ε : ℝ} (hε : 0 < ε)
    (hseg : ∀ x τ : ℝ, |τ| ≤ ε → curve γ x = curve γ t₀ + τ • rot90 V →
      τ = 0 ∧ ∃ k : ℤ, x = t₀ + 2 * Real.pi * k) :
    (∀ t : ℝ, curve γ t ≠ curve γ t₀ + ε • rot90 V) ∧
    (∀ t : ℝ, curve γ t ≠ curve γ t₀ - ε • rot90 V) ∧
    (∀ (hp : curve γ t₀ + ε • rot90 V ∉ Set.range γ)
      (hp' : curve γ t₀ - ε • rot90 V ∉ Set.range γ),
      windE γ hγ hp - windE γ hγ hp' = 2) := by
  have hcont : Continuous γ := hγ.isEmbedding.continuous
  have hVne : V ≠ 0 := by
    rw [← hV.deriv]; exact curve_deriv_ne_zero γ hγ t₀
  -- the re-parametrised curve, whose base point is `curve γ t₀`
  set G : ℝ → ℝ × ℝ := fun s => curve γ (t₀ + s) with hGdef
  have hG0 : G 0 = curve γ t₀ := by
    show curve γ (t₀ + 0) = curve γ t₀
    rw [add_zero]
  have hGcont : Continuous G := continuous_curve_add γ hγ t₀
  have hGder : HasDerivAt G V 0 := hasDerivAt_curve_add hV
  -- the segment property, in the shape of `Work.Drive.seg_rel_false_of_curve`
  have hsegG : ∀ y τ : ℝ, |τ| ≤ ε → G y = G 0 + τ • rot90 V →
      τ = 0 ∧ ∃ k : ℤ, y = 2 * Real.pi * k := by
    intro y τ hτ hy
    have h2 : curve γ (t₀ + y) = curve γ t₀ + τ • rot90 V := by
      rw [hG0] at hy
      exact hy
    obtain ⟨hτ0, k, hk⟩ := hseg (t₀ + y) τ hτ h2
    exact ⟨hτ0, k, by linarith⟩
  -- the two points
  set p : ℝ × ℝ := curve γ t₀ + ε • rot90 V with hpdef
  set p' : ℝ × ℝ := curve γ t₀ - ε • rot90 V with hp'def
  have hp_eq : p = G 0 + ε • rot90 V := by rw [hpdef, ← hG0]
  have hp'_eq : p' = G 0 - ε • rot90 V := by rw [hp'def, ← hG0]
  -- the curve avoids both points
  have hcurve_ne : ∀ x : ℝ, curve γ x ≠ curve γ t₀ + ε • rot90 V ∧
      curve γ x ≠ curve γ t₀ - ε • rot90 V := by
    intro x
    constructor
    · intro hx
      have h2 : curve γ x = curve γ t₀ + ε • rot90 V := hx
      obtain ⟨hτ, -⟩ := hseg x ε (by simp [abs_of_pos hε]) h2
      exact hε.ne' hτ
    · intro hx
      have h2 : curve γ x = curve γ t₀ + (-ε) • rot90 V := by
        rw [hx, sub_eq_add_neg, neg_smul]
      obtain ⟨hτ, -⟩ := hseg x (-ε) (by simp [abs_of_pos hε]) h2
      exact (neg_ne_zero.mpr hε.ne') hτ
  have hp : curve γ t₀ + ε • rot90 V ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨x, hx⟩
    exact (hcurve_ne x).1 hx
  have hp' : curve γ t₀ - ε • rot90 V ∉ Set.range γ := by
    rw [← range_curve γ]
    rintro ⟨x, hx⟩
    exact (hcurve_ne x).2 hx
  -- the ratio loop of the parametrisation `gammaU γ`
  set F : UnitAddCircle → UnitAddCircle := ratioLoop (gammaU γ) p p' with hFdef
  have hFcont : Continuous F := continuous_ratioLoop (gammaU γ) (continuous_gammaU hcont)
    (notMem_range_gammaU hp) (notMem_range_gammaU hp')
  -- the ratio of the two chords, for the re-parametrised curve
  set R : ℝ → ℂ := fun x => ratioMap G p p' (2 * Real.pi * x) with hRdef
  have hRne : ∀ x : ℝ, R x ≠ 0 := by
    intro x
    rw [hRdef]
    refine div_ne_zero ?_ ?_
    · rw [cpx_ne_zero_iff, sub_ne_zero]
      exact fun h => (hcurve_ne (t₀ + 2 * Real.pi * x)).1 h
    · rw [cpx_ne_zero_iff, sub_ne_zero]
      exact fun h => (hcurve_ne (t₀ + 2 * Real.pi * x)).2 h
  -- the ratio never crosses the negative real axis on `(0,1)`
  have hRslit : ∀ x ∈ Set.Ioo (0:ℝ) 1, R x ∈ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, hRne x⟩
    intro harg
    have hre : (R x).re < 0 := (Complex.arg_eq_pi_iff.mp harg).1
    have him : (R x).im = 0 := (Complex.arg_eq_pi_iff.mp harg).2
    have hz : R x = ((R x).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hrel : cpx (G (2 * Real.pi * x) - (G 0 + ε • rot90 V))
        = ((R x).re : ℂ) * cpx (G (2 * Real.pi * x) - (G 0 - ε • rot90 V)) := by
      have hden : cpx (G (2 * Real.pi * x) - p') ≠ 0 := by
        rw [cpx_ne_zero_iff, sub_ne_zero]
        exact fun h => (hcurve_ne (t₀ + 2 * Real.pi * x)).2 h
      have h1 : cpx (G (2 * Real.pi * x) - p) = R x * cpx (G (2 * Real.pi * x) - p') := by
        rw [hRdef]
        simp only [ratioMap]
        rw [div_mul_cancel₀ _ hden]
      rw [hz, hp_eq, hp'_eq] at h1
      exact h1
    exact seg_rel_false_of_curve hε hsegG hre hx.1 hx.2 hrel
  set A : ℝ → ℝ := fun x => (R x).arg / Real.pi with hAdef
  have hRcont : Continuous R := by
    rw [hRdef]
    refine Continuous.div ?_ ?_ ?_
    · exact continuous_cpx.comp ((hGcont.comp (continuous_const.mul continuous_id)).sub
        continuous_const)
    · exact continuous_cpx.comp ((hGcont.comp (continuous_const.mul continuous_id)).sub
        continuous_const)
    · intro x
      rw [cpx_ne_zero_iff, sub_ne_zero]
      exact fun h => (hcurve_ne (t₀ + 2 * Real.pi * x)).2 h
  have hAcont : ContinuousOn A (Set.Ioo (0:ℝ) 1) := by
    rw [hAdef]
    exact (Complex.continuousOn_arg.comp hRcont.continuousOn fun x hx => hRslit x hx).div_const
      Real.pi
  -- `gammaU γ` after the rotation `t₀/(2π)` is the re-parametrised curve
  set c : UnitAddCircle := ((t₀ / (2 * Real.pi) : ℝ) : UnitAddCircle) with hcdef
  have hgamma : ∀ x : ℝ, gammaU γ ((x : UnitAddCircle) + c) = G (2 * Real.pi * x) := by
    intro x
    have h1 : (x : UnitAddCircle) + c = ((x + t₀ / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
      rw [hcdef, ← AddCircle.coe_add]
    rw [h1, gammaU_apply_coe]
    have h2 : 2 * Real.pi * (x + t₀ / (2 * Real.pi)) = t₀ + 2 * Real.pi * x := by
      field_simp
      ring
    rw [h2]
  -- the loop of which the degree is computed is the rotated ratio loop
  set g : UnitAddCircle → UnitAddCircle := fun u => F (u + c) with hgdef
  have hgcont : Continuous g := hFcont.comp (continuous_id.add continuous_const)
  have hlift : ∀ x ∈ Set.Ioo (0:ℝ) 1, ((A x : ℝ) : UnitAddCircle) = g (x : UnitAddCircle) := by
    intro x hx
    have h1 : ((A x : ℝ) : UnitAddCircle) = dirZ (R x) := rfl
    have h2 : g (x : UnitAddCircle) = dirZ (R x) := by
      show F ((x : UnitAddCircle) + c) = dirZ (ratioMap G p p' (2 * Real.pi * x))
      rw [hFdef, ratioLoop_apply, ratioMap_apply, hgamma x]
    rw [h1, h2]
  -- the limits of the lift
  obtain ⟨δ, hδpos, himneg, himpos, hlimpos, hlimneg⟩ :=
    curve_ratio_local hVne hGder hε
  have ha : Tendsto A (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-1)) := by
    have hlimG : Tendsto (fun x : ℝ =>
        (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) (2 * Real.pi * x)).arg / Real.pi)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-1)) := by
      have harg : Tendsto (fun x : ℝ => 2 * Real.pi * x)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h1 : Tendsto (fun x : ℝ => 2 * Real.pi * x) (nhds (0:ℝ))
              (nhds (2 * Real.pi * 0)) := tendsto_const_nhds.mul tendsto_id
          simpa using h1.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with x hx
          show (0:ℝ) < 2 * Real.pi * x
          have : (0:ℝ) < x := hx
          positivity
      have hlim := (hlimpos.comp harg).div_const Real.pi
      have h3 : (-Real.pi) / Real.pi = -1 := by
        rw [neg_div, div_self Real.pi_ne_zero]
      rw [h3] at hlim
      exact hlim
    refine hlimG.congr' ?_
    filter_upwards with x
    rw [hAdef, hRdef, hp_eq, hp'_eq]
  have hb : Tendsto A (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds 1) := by
    have hper2 : ∀ x : ℝ, G (2 * Real.pi * x) = G (2 * Real.pi * x - 2 * Real.pi) :=
      fun x => (periodic_curve_add' γ t₀ (2 * Real.pi * x)).symm
    have hlimG : Tendsto (fun x : ℝ =>
        (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) (2 * Real.pi * x)).arg / Real.pi)
        (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds 1) := by
      have heq : (fun x : ℝ =>
            (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) (2 * Real.pi * x)).arg
              / Real.pi)
          =ᶠ[nhdsWithin (1:ℝ) (Set.Iio 1)]
          fun x : ℝ => (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V)
            (2 * Real.pi * x - 2 * Real.pi)).arg / Real.pi := by
        filter_upwards with x
        simp only [ratioMap]
        rw [hper2 x]
      have harg : Tendsto (fun x : ℝ => 2 * Real.pi * x - 2 * Real.pi)
          (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhdsWithin (0:ℝ) (Set.Iio 0)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h1 : Tendsto (fun x : ℝ => 2 * Real.pi * x - 2 * Real.pi) (nhds (1:ℝ))
              (nhds (2 * Real.pi * 1 - 2 * Real.pi)) :=
            (tendsto_const_nhds.mul tendsto_id).sub tendsto_const_nhds
          have h2 : 2 * Real.pi * 1 - 2 * Real.pi = 0 := by ring
          rw [h2] at h1
          exact h1.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with x hx
          show 2 * Real.pi * x - 2 * Real.pi < 0
          have hx1 : x < 1 := hx
          nlinarith [Real.pi_pos]
      have hlim := (hlimneg.comp harg).div_const Real.pi
      have h3 : Real.pi / Real.pi = 1 := div_self Real.pi_ne_zero
      rw [h3] at hlim
      exact hlim.congr' heq.symm
    refine hlimG.congr' ?_
    filter_upwards with x
    rw [hAdef, hRdef, hp_eq, hp'_eq]
  -- the degree is `2`
  obtain ⟨n, hn, hdeg⟩ := degree_eq_of_lift_on_Ioo hgcont hAcont hlift ha hb
  have hn2 : n = 2 := by
    have h : (n : ℝ) = 2 := by linarith
    exact_mod_cast h
  have hdegF : degree F hFcont = 2 := by
    rw [← degree_comp_add_right F hFcont c, hdeg, hn2]
  have hwind : windE γ hγ hp - windE γ hγ hp' = 2 := by
    have hsub : windE γ hγ hp - windE γ hγ hp' = degree F hFcont :=
      winding_sub_eq_degree_ratioLoop (gammaU γ) (continuous_gammaU hcont)
        (notMem_range_gammaU hp) (notMem_range_gammaU hp')
    rw [hsub, hdegF]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (hcurve_ne t).1 ht
  · intro t ht
    exact (hcurve_ne t).2 ht
  · intro hp₀ hp₀'
    exact hwind

open Manifold in
open scoped Manifold ContDiff in
/-- **The signed local jump of the winding number at a point of the curve.**  At a point `curve γ t₀`
of a smooth embedded closed plane curve `γ`, the two points
`curve γ t₀ ± ε • rot90 (deriv (curve γ) t₀)` (small `ε > 0`) lie on opposite sides of the curve and
off it, and the winding number of `γ` about the point on the *left* of the traversal (i.e. in the
direction `rot90` of the tangent) exceeds the winding number about the point on the right by exactly
`2` (the `dirC`-normalisation of this workspace, where a full turn of the position direction counts
`2`). -/
theorem signed_jump_at_point (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (t₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (∀ t : ℝ, curve γ t ≠ curve γ t₀ + ε • rot90 (deriv (curve γ) t₀)) ∧
      (∀ t : ℝ, curve γ t ≠ curve γ t₀ - ε • rot90 (deriv (curve γ) t₀)) ∧
      (∀ (hp : curve γ t₀ + ε • rot90 (deriv (curve γ) t₀) ∉ Set.range γ)
        (hp' : curve γ t₀ - ε • rot90 (deriv (curve γ) t₀) ∉ Set.range γ),
        windE γ hγ hp - windE γ hγ hp' = 2) := by
  have hVne : deriv (curve γ) t₀ ≠ 0 := curve_deriv_ne_zero γ hγ t₀
  have hV : HasDerivAt (curve γ) (deriv (curve γ) t₀) t₀ :=
    (((contDiff_curve γ hγ).differentiable (by norm_num)).differentiableAt).hasDerivAt
  obtain ⟨δ, hδpos, hseg₀⟩ := curve_normal_segment (fun s : ℝ => curve γ (t₀ + s)) hVne
    (continuous_curve_add γ hγ t₀) (hasDerivAt_curve_add hV) (periodic_curve_add γ t₀)
    (fun s t h => eq_of_curve_add_eq γ hγ t₀ h)
  refine ⟨δ, hδpos, fun ε hε hεδ => ?_⟩
  have hseg : ∀ x τ : ℝ, |τ| ≤ ε →
      curve γ x = curve γ t₀ + τ • rot90 (deriv (curve γ) t₀) →
      τ = 0 ∧ ∃ k : ℤ, x = t₀ + 2 * Real.pi * k := by
    intro x τ hτ hx
    have h1 : curve γ (t₀ + (x - t₀))
        = curve γ (t₀ + 0) + τ • rot90 (deriv (curve γ) t₀) := by
      rw [show t₀ + (x - t₀) = x by ring, add_zero]
      exact hx
    obtain ⟨hτ0, k, hk⟩ := hseg₀ (x - t₀) τ (le_trans hτ (le_of_lt hεδ)) h1
    exact ⟨hτ0, k, by linarith⟩
  exact windE_jump_of_normal_aux γ hγ hV hε hseg

end Work.Drive
