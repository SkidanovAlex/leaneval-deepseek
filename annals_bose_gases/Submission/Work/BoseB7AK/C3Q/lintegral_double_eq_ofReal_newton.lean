import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.C3Q.coulomb_W1fun_le
import Submission.Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7AK.C3Q

/-!
# `∫⁻`-form of the Newton double-integral identity

This file proves `Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton`, the `∫⁻`
(ENNReal) companion of `Submission.BoseGases.chosen_newton_double_eq`.

## Proof shape

Three steps, all pointwise-a.e. followed by `lintegral_congr_ae`:

1. `newton_slice_integrable_ae` — for a.e. `x`, the slice `y ↦ g y * ‖x−y‖⁻¹` is
   Bochner-integrable (`coulPot_abs_slice_integrable_ae` plus `|g| = g` a.e. from
   `hg0`).  Together with `ofReal_integral_eq_lintegral_ofReal` this identifies the
   inner `∫⁻` with an `ofReal` of a real integral.
2. `lintegral_slice_ofReal_newton` — at such an `x`, `ofReal (g x)` factors out of the
   inner `∫⁻` (`ENNReal.ofReal_mul` + `lintegral_const_mul''`) and the Newton
   representation turns the remaining slice integral into `ofReal (8π * ω x)`.
3. The outer `∫⁻` is then `∫⁻ x, ofReal (8π * (g x * ω x))`, evaluated by
   `ofReal_integral_eq_lintegral_ofReal` (using `hgω`, `hgω0`).

The case `R = 0` is degenerate (`hgsupp` forces `g ≡ 0`) and is handled separately,
since the corpus slice lemma `coulPot_abs_slice_integrable_ae` needs `0 < R`.
-/

open MeasureTheory

/-- **A.e. slice integrability of the Newton kernel against `g`.**  For `g ∈ L¹`,
`g ≥ 0` a.e. and `g = 0` outside `closedBall 0 R` with `R > 0`, the slice
`y ↦ g y * ‖x − y‖⁻¹` is Bochner-integrable for a.e. `x`.

(`Submission.BoseGases.coulPot_abs_slice_integrable_ae` gives the version with `|g y|`,
which agrees with `g y` for a.e. `y` by `hg0`.) -/
theorem newton_slice_integrable_ae {g : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hg : MeasureTheory.Integrable g) (hg0 : ∀ᵐ x, 0 ≤ g x)
    (hgsupp : ∀ x, R ≤ ‖x‖ → g x = 0) (hR : 0 < R) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 3), MeasureTheory.Integrable (fun y => g y * ‖x - y‖⁻¹) := by
  have h := Submission.BoseGases.coulPot_abs_slice_integrable_ae (p := g) (R := R) hg hgsupp hR
  filter_upwards [h, hg0] with x hx _
  refine Integrable.congr hx ?_
  filter_upwards [hg0] with y hy
  rw [abs_of_nonneg hy]

/-- **Pointwise reduction of the inner `∫⁻`.**  If `g ≥ 0` a.e., `g x ≥ 0`, the slice
`y ↦ g y * ‖x − y‖⁻¹` is integrable and its integral is `8π · ω x` (the Newton
representation at `x`), then the inner extended integral of `g x * g y / ‖x − y‖`
equals `ofReal (8π * (g x * ω x))`. -/
theorem lintegral_slice_ofReal_newton {g ω : EuclideanSpace ℝ (Fin 3) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hg0 : ∀ᵐ y, 0 ≤ g y) (hgx : 0 ≤ g x)
    (hslice : MeasureTheory.Integrable (fun y => g y * ‖x - y‖⁻¹))
    (hI : (∫ y, g y * ‖x - y‖⁻¹) = 8 * Real.pi * ω x) :
    (∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖))
      = ENNReal.ofReal (8 * Real.pi * (g x * ω x)) := by
  have hnonneg : 0 ≤ᵐ[volume] (fun y => g y * ‖x - y‖⁻¹) := by
    filter_upwards [hg0] with y hy
    exact mul_nonneg hy (inv_nonneg.mpr (norm_nonneg _))
  have hlin : (∫⁻ y, ENNReal.ofReal (g y * ‖x - y‖⁻¹)) =
      ENNReal.ofReal (∫ y, g y * ‖x - y‖⁻¹) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hslice hnonneg).symm
  have h1 : ∀ y, ENNReal.ofReal (g x * g y / ‖x - y‖) =
      ENNReal.ofReal (g x) * ENNReal.ofReal (g y * ‖x - y‖⁻¹) := by
    intro y
    rw [← ENNReal.ofReal_mul hgx]
    congr 1
    rw [div_eq_mul_inv]
    ring
  calc (∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖))
      = ∫⁻ y, ENNReal.ofReal (g x) * ENNReal.ofReal (g y * ‖x - y‖⁻¹) := by
        apply lintegral_congr
        intro y
        exact h1 y
    _ = ENNReal.ofReal (g x) * (∫⁻ y, ENNReal.ofReal (g y * ‖x - y‖⁻¹)) :=
        MeasureTheory.lintegral_const_mul'' _
          (ENNReal.measurable_ofReal.comp_aemeasurable
            hslice.aestronglyMeasurable.aemeasurable)
    _ = ENNReal.ofReal (g x) * ENNReal.ofReal (∫ y, g y * ‖x - y‖⁻¹) := by rw [hlin]
    _ = ENNReal.ofReal (g x) * ENNReal.ofReal (8 * Real.pi * ω x) := by rw [hI]
    _ = ENNReal.ofReal (8 * Real.pi * (g x * ω x)) := by
        rw [← ENNReal.ofReal_mul hgx]
        congr 1
        ring

/-- **The `∫⁻` (ENNReal) form of the Newton double-integral identity** (x-space, no
Fourier): for `g ∈ L¹`, `g ≥ 0` a.e., supported in `closedBall 0 R`, and `ω` satisfying
the Newton representation `ω x = (8π)⁻¹ ∫ y, g y ‖x−y‖⁻¹ dy` a.e. (with `g·ω ∈ L¹`,
`g·ω ≥ 0` a.e.), one has

`∫⁻ x, ∫⁻ y, ofReal (g x * g y / ‖x−y‖) = ofReal (8π * ∫ x, g x * ω x)`.

This is the `∫⁻`-companion of `Submission.BoseGases.chosen_newton_double_eq` (which states
that the Bochner **iterated** double integral equals `8π ∫ g ω`); the `∫⁻` form is what a
consumer needs to *evaluate* the double lintegral (in particular it also shows it is
finite).  It is not implied by the Bochner identity alone: the `∫⁻` and the iterated
Bochner integral differ when the `y`-slices are non-integrable, and it is exactly the
a.e.-slice integrability below that rules this out.

ROUTE (all ingredients already in the workspace):

* `Submission.BoseGases.kernel_abs_slice_integrable_ae` (`Submission/NewtonRep.lean`, with
  `kernel_abs_lintegral_prod_lt_top`, `kernel_abs_integrable_prod_ball`): for a.e. `x` in
  `ball 0 M` (`M := R + 1` suffices), `y ↦ |g y| * ‖x − y‖⁻¹` is Bochner-integrable, hence
  (via `|g y| = g y` for a.e. `y`) so is `y ↦ g y * ‖x − y‖⁻¹`, i.e.
  `∫⁻ y, ofReal (g y * ‖x − y‖⁻¹) < ⊤` for a.e. `x`.  (Outside `ball 0 (2R)` the far-field
  bound `coulPot_abs_slice_integrable_of_norm_ge` of `Submission/NewtonCoulomb.lean` gives
  slice integrability directly; a countable cover of `ℝ³` by such balls, or Tonelli for
  the marginal, then upgrades "a.e. on each ball" to "a.e. on `ℝ³`".)
* `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` on the slice plus `hrep` gives
  `∫⁻ y, ofReal (g y * ‖x − y‖⁻¹) = ofReal (8π * ω x)` for a.e. `x`.
* `ENNReal.ofReal_mul` (with `0 ≤ g x` a.e.) splits off `ofReal (g x)` from the inner
  lintegral and `lintegral_const_mul''` moves it out:
  `∫⁻ y, ofReal (g x * g y / ‖x − y‖) = ofReal (8π * (g x * ω x))` for a.e. `x`.
* The outer lintegral is `∫⁻ x, ofReal (8π * (g x * ω x))`, and
  `ofReal_integral_eq_lintegral_ofReal` (with `g·ω` integrable and `≥ 0` a.e.) evaluates it
  as `ofReal (8π * ∫ x, g x * ω x)`.

Instantiation in the consumer (`Work.BoseB7AK.C3Q.I2_integral_bound`):
`g := Submission.BoseGases.g0 v h`, `ω := Classical.choose h`, with
`scattering_newton_representation` (`hrep`), `g0_integrable`, `g0_nonneg_ae`,
`g0_zero_of_norm_ge`, `g0w0_integrable`, `W1omegaNum_nonneg_ae`. -/
theorem lintegral_double_eq_ofReal_newton {g ω : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hg : MeasureTheory.Integrable g) (hg0 : ∀ᵐ x, 0 ≤ g x)
    (hgsupp : ∀ x, R ≤ ‖x‖ → g x = 0) (hR : 0 ≤ R)
    (hgω : MeasureTheory.Integrable (fun x => g x * ω x))
    (hgω0 : ∀ᵐ x, 0 ≤ g x * ω x)
    (hrep : ∀ᵐ x, ω x = (1 / (8 * Real.pi)) * ∫ y, g y * ‖x - y‖⁻¹) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖))
      = ENNReal.ofReal (8 * Real.pi * ∫ x, g x * ω x) := by
  rcases eq_or_lt_of_le hR with hRz | hRp
  · -- degenerate case `R = 0`: `hgsupp` forces `g ≡ 0`
    have hgz : ∀ x : EuclideanSpace ℝ (Fin 3), g x = 0 :=
      fun x => hgsupp x (hRz ▸ norm_nonneg x)
    have hleft : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖)) = 0 := by
      simp [hgz]
    have hright : ENNReal.ofReal (8 * Real.pi * ∫ x, g x * ω x) = 0 := by
      rw [show (∫ x, g x * ω x) = 0 from by simp [hgz]]
      simp
    rw [hleft, hright]
  · have hslice := newton_slice_integrable_ae (g := g) (R := R) hg hg0 hgsupp hRp
    -- per-`x` reduction of the inner extended integral
    have hper : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
        (∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖))
          = ENNReal.ofReal (8 * Real.pi * (g x * ω x)) := by
      filter_upwards [hslice, hg0, hrep] with x hxs hgx hxrep
      have hI : (∫ y, g y * ‖x - y‖⁻¹) = 8 * Real.pi * ω x := by
        rw [hxrep, ← mul_assoc,
          mul_one_div_cancel (by positivity : (8 : ℝ) * Real.pi ≠ 0), one_mul]
      exact lintegral_slice_ofReal_newton hg0 hgx hxs hI
    rw [MeasureTheory.lintegral_congr_ae hper]
    -- the outer `∫⁻` of `ofReal (8π * (g·ω))` is `ofReal` of the Bochner integral
    have hint : MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin 3) => (8 : ℝ) * Real.pi * (g x * ω x)) :=
      hgω.const_mul _
    have hnn : 0 ≤ᵐ[volume]
        (fun x : EuclideanSpace ℝ (Fin 3) => (8 : ℝ) * Real.pi * (g x * ω x)) := by
      filter_upwards [hgω0] with x hx
      exact mul_nonneg (by positivity) hx
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [MeasureTheory.integral_const_mul]

end Work.BoseB7AK.C3Q
