import ChallengeDeps
import Submission.RadialIntegral
import Submission.RadialRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local integrability of the rescaled radial profile on `(R, ∞)`

Goal theorem (assigned sub-lemma, same statement as in `Submission.ProfileEq1D`):

    profile_mul_locallyIntegrableOn {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
      (hrad : IsRadial w) (hwli : LocallyIntegrable w) :
      MeasureTheory.LocallyIntegrableOn (fun r : ℝ => r * radialProfile w r)
        (Set.Ioi R) volume

The 1D classification `SndClassify.affine_ae_of_snd_annihilates` needs the
rescaled profile `u(r) := r · radialProfile w r` to be locally integrable on
the half-line `(R, ∞)`, which is what this module proves from the local
integrability of `w` on `ℝ³` (radial functions integrate by shells).

## Proof route

`LocallyIntegrableOn f s μ` is `∀ x, x ∈ s → IntegrableAtFilter f (𝓝[s] x) μ`,
i.e. for each `x > R` you must exhibit a set `U` with `U ∈ 𝓝[Ioi R] x` on which
`u` is integrable.

1. Fix `x > R`. Choose a window `Icc a c` and a ball radius `d` with
   `R < a < x < c < d` (e.g. `a := (x + R) / 2`, `c := x + 1`, `d := x + 2`).
   Then `Icc a c ⊆ Ioo 0 d`, `Icc a c ∈ 𝓝[Ioi R] x` (`mem_nhdsWithin.mpr`:
   the open interval `(a, c)` is a neighbourhood of `x` inside `(R, ∞)`).

2. **Integrability of `r ↦ r ^ 2 · radialProfile w r` on the window**:
   - `hwli : LocallyIntegrable w` gives integrability on every compact set:
     `w` is integrable on `Metric.closedBall 0 d` (compact in `ℝ³`) by
     `LocallyIntegrable.integrableOn_isCompact` + `isCompact_closedBall`, hence
     on the open ball `Metric.ball 0 d` by restriction.
   - Since `w` is radial, `w y = radialProfile w ‖y‖` pointwise
     (`radial_eq_profile`), so the radial-integral equivalence
     `integrable_radial_ball_r3 (R := d) (f := radialProfile w)` turns this
     into `IntegrableOn (fun r => r ^ 2 * radialProfile w r) (Ioo 0 d) volume`.
   - Restrict to the window `Icc a c ⊆ Ioo 0 d` (`0 < a`, `c < d`).

3. **The factor `r`:** on the window `a ≤ r`, so `r ≠ 0` and
   `r⁻¹ · (r ^ 2 · f r) = r · f r` pointwise; multiplying the integrable
   function `r ↦ r ^ 2 · f r` by the continuous function `r ↦ r⁻¹` (which is
   `ContinuousOn` the window) via `IntegrableOn.continuousOn_mul` gives
   integrability of `u` on `Icc a c` (congruence by pointwise equality).

4. Unfold `LocallyIntegrableOn` at `x` and supply
   `⟨Icc a c, hmem, hint⟩` where `hmem : Icc a c ∈ 𝓝[Ioi R] x` and
   `hint : IntegrableOn (fun r => r * radialProfile w r) (Icc a c) volume`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The rescaled profile `u(r) := r · radialProfile w r` is locally
integrable on `(R, ∞)` when `w` is radial and locally integrable on `ℝ³`
and `R > 0`. -/
theorem profile_mul_locallyIntegrableOn {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) (hwli : LocallyIntegrable w) :
    MeasureTheory.LocallyIntegrableOn (fun r : ℝ => r * radialProfile w r)
      (Set.Ioi R) volume := by
  let f : ℝ → ℝ := radialProfile w
  change MeasureTheory.LocallyIntegrableOn (fun r : ℝ => r * f r) (Set.Ioi R) volume
  intro x hx
  let a : ℝ := (x + R) / 2
  let c : ℝ := x + 1
  let d : ℝ := x + 2
  have hR_x : R < x := hx
  have haR : R < a := by dsimp [a]; linarith
  have hax : a < x := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hxc : x < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  change ∃ s ∈ 𝓝[Set.Ioi R] x,
    IntegrableOn (fun r : ℝ => r * f r) s volume
  refine ⟨Set.Icc a c, ?_, ?_⟩
  · -- `Icc a c` is a neighbourhood of `x` within `(R, ∞)`
    rw [mem_nhdsWithin]
    refine ⟨Set.Ioo a c, isOpen_Ioo, ⟨hax, hxc⟩, ?_⟩
    intro y hy
    rcases hy with ⟨hyo, hyR⟩
    exact ⟨le_of_lt hyo.1, le_of_lt hyo.2⟩
  · -- integrability of `u` on the window `Icc a c`
    have hwcb : IntegrableOn w (Metric.closedBall (0 : ℝ³) d) volume := by
      exact hwli.integrableOn_isCompact (isCompact_closedBall (0 : ℝ³) d)
    have hwball : IntegrableOn (fun x : ℝ³ => w x) (Metric.ball (0 : ℝ³) d) volume := by
      exact hwcb.mono_set Metric.ball_subset_closedBall
    have hw_eq : (fun x : ℝ³ => w x) = (fun x : ℝ³ => f ‖x‖) := by
      funext x
      exact radial_eq_profile hrad x
    have hfball : IntegrableOn (fun x : ℝ³ => f ‖x‖) (Metric.ball (0 : ℝ³) d) volume := by
      rw [← hw_eq]
      exact hwball
    have h1d : IntegrableOn (fun r : ℝ => r ^ 2 * f r) (Set.Ioo 0 d) volume :=
      (integrable_radial_ball_r3 (f := f) d).mp hfball
    have hwin_sub : Set.Icc a c ⊆ Set.Ioo 0 d := by
      intro y hy
      exact ⟨lt_of_lt_of_le ha0 hy.1, lt_of_le_of_lt hy.2 hcd⟩
    have h1ac : IntegrableOn (fun r : ℝ => r ^ 2 * f r) (Set.Icc a c) volume :=
      h1d.mono_set hwin_sub
    have hinvcont : ContinuousOn (fun r : ℝ => r⁻¹) (Set.Icc a c) := by
      refine continuousOn_inv₀.mono ?_
      intro r hr
      exact ne_of_gt (lt_of_lt_of_le ha0 hr.1)
    have hprod : IntegrableOn (fun r : ℝ => r⁻¹ * (r ^ 2 * f r)) (Set.Icc a c) volume := by
      exact IntegrableOn.continuousOn_mul hinvcont h1ac isCompact_Icc
    have hcong : Set.EqOn (fun r : ℝ => r⁻¹ * (r ^ 2 * f r)) (fun r : ℝ => r * f r)
        (Set.Icc a c) := by
      intro r hr
      have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hr.1)
      field_simp [hrne]
    exact hprod.congr_fun hcong measurableSet_Icc

end Submission.BoseGases
