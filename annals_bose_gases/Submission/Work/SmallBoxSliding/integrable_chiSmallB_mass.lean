import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the `χ_{B(u)}`-mass over the sliding parameter `u`

The sliding localisation of FS `thm:aprioriHLambda` integrates the per-box
cutoff mass

    Ψ(u) := ∫_x χ_{B(u)}(x)² dx ,    χ_{B(u)}(x) = χ_M(x/ℓ)·χ_M(x/(ℓd) − u),

over the parameter `u ∈ ℝ³`.  This module proves that `Ψ` is
`MeasureTheory.Integrable` (`Work.SmallBoxSliding.integrable_chiSmallB_mass`),
so that all the `u`-integrated mass-bookkeeping of the sliding sum
(`nBox_integral_u`, the Cauchy–Schwarz window, the discarded-set estimates)
has a legitimate Bochner integral to speak about.

The argument is short because `Ψ` is both **continuous** (`u ↦ χ_{B(u)}(x)²`
is jointly continuous with `x`-support in the fixed compact big-box cube,
`Submission.BoseGases.chiSmallB_partial_integral_continuous`) and
**compactly supported**: if `Ψ(u) ≠ 0` the integrand
`x ↦ χ_{B(u)}(x)²` cannot vanish identically, so some `x` has
`χ_{B(u)}(x) ≠ 0`; the support containments of the two factors
(`chiSmallB_support_big_box`: `|x_j| ≤ ℓ/2`, and
`chiSmallB_support_small_box_dist`: `|(x − (ℓd)•u)_j| ≤ (ℓd)/2`) then force
`‖(ℓd)•u‖_∞ ≤ ℓ/2 + (ℓd)/2`, i.e. `‖u‖ ≤ √3·(ℓ/2+(ℓd)/2)/(ℓd)` — a fixed
ball, because the small box can only meet the big box when the two are
`s`-close.  (This is the `u`-shadow of `farSet_chiSmallB_zero`.)

Continuous + compactly supported ⟹ integrable for the Lebesgue measure on
`ℝ³`.  Note that the hypotheses `0 < ℓ`, `0 < d` are essential: they make
`x ↦ (ℓd)⁻¹ • x − u` a genuine dilation and keep `(ℓd) ≠ 0` in the support
estimate.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **The mass detects the cutoff**: if `∫_x χ_{B(u)}(x)² ≠ 0` then the
integrand is not identically zero, i.e. some `x` has `χ_{B(u)}(x) ≠ 0`.
(Purely logical: if `χ_{B(u)} ≡ 0` the integral of the square is `∫ 0 = 0`.) -/
lemma exists_chiSmallB_ne_zero_of_integral_sq_ne_zero {M : ℕ} {ℓ d : ℝ} {u : ℝ³}
    (hu : (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) ≠ 0) : ∃ x : ℝ³, chiSmallB M ℓ d u x ≠ 0 := by
  by_contra h
  push Not at h
  exact hu (by simp [h])

/-- **Coordinate support estimate for the mass**: if `∫_x χ_{B(u)}(x)² ≠ 0`
then some coordinate of `w := (ℓd)•u` satisfies `|w_j| ≤ ℓ/2 + (ℓd)/2` —
the small box meets the big box only over such `u`. -/
lemma exists_coord_abs_le_of_integral_chiSmallB_sq_ne_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³}
    (hu : (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) ≠ 0) :
    ∃ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ ℓ / 2 + (ℓ * d) / 2 := by
  obtain ⟨x, hx⟩ := exists_chiSmallB_ne_zero_of_integral_sq_ne_zero hu
  refine ⟨0, ?_⟩
  have h1 : |x.ofLp (0 : Fin 3)| ≤ ℓ / 2 := chiSmallB_support_big_box hM hℓ hx 0
  have h2 : |((x - (ℓ * d) • u).ofLp (0 : Fin 3))| ≤ (ℓ * d) / 2 :=
    chiSmallB_support_small_box_dist hM hℓ hd hx 0
  have h3 : ((ℓ * d) • u).ofLp (0 : Fin 3) =
      x.ofLp (0 : Fin 3) - (x - (ℓ * d) • u).ofLp (0 : Fin 3) := by simp
  rw [h3]
  calc |x.ofLp (0 : Fin 3) - (x - (ℓ * d) • u).ofLp (0 : Fin 3)|
      ≤ |x.ofLp (0 : Fin 3)| + |(x - (ℓ * d) • u).ofLp (0 : Fin 3)| := abs_sub _ _
    _ ≤ ℓ / 2 + (ℓ * d) / 2 := add_le_add h1 h2

/-- **Full support estimate**: the mass `Ψ(u) = ∫_x χ_{B(u)}(x)² dx` can only
be nonzero for `u` in the fixed ball of radius
`√3·(ℓ/2 + (ℓd)/2)/(ℓd)`; indeed there `∀ j, |((ℓd)•u)_j| ≤ ℓ/2 + (ℓd)/2`
and the coordinate box maps into the Euclidean ball. -/
lemma norm_le_of_integral_chiSmallB_sq_ne_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u : ℝ³} (hu : (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) ≠ 0) :
    ‖u‖ ≤ Real.sqrt 3 * (ℓ / 2 + (ℓ * d) / 2) / (ℓ * d) := by
  obtain ⟨x, hx⟩ := exists_chiSmallB_ne_zero_of_integral_sq_ne_zero hu
  have hB0 : 0 ≤ ℓ / 2 + (ℓ * d) / 2 := by positivity
  have hcoord : ‖(ℓ * d) • u‖ ≤ Real.sqrt 3 * (ℓ / 2 + (ℓ * d) / 2) :=
    coord_box_subset_eucl_ball (A := ℓ / 2 + (ℓ * d) / 2) hB0 (by
      intro j
      have h1 : |x.ofLp j| ≤ ℓ / 2 := chiSmallB_support_big_box hM hℓ hx j
      have h2 : |((x - (ℓ * d) • u).ofLp j)| ≤ (ℓ * d) / 2 :=
        chiSmallB_support_small_box_dist hM hℓ hd hx j
      have h3 : ((ℓ * d) • u).ofLp j = x.ofLp j - (x - (ℓ * d) • u).ofLp j := by simp
      rw [h3]
      calc |x.ofLp j - (x - (ℓ * d) • u).ofLp j|
          ≤ |x.ofLp j| + |(x - (ℓ * d) • u).ofLp j| := abs_sub _ _
        _ ≤ ℓ / 2 + (ℓ * d) / 2 := add_le_add h1 h2)
  have hsmul : ‖(ℓ * d) • u‖ = (ℓ * d) * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hℓ hd)]
  rw [hsmul] at hcoord
  exact (le_div_iff₀ (mul_pos hℓ hd)).mpr (by rw [mul_comm]; exact hcoord)

/-- **`Ψ` has compact support**: its support lies in the fixed closed ball of
radius `√3·(ℓ/2 + (ℓd)/2)/(ℓd)`. -/
lemma hasCompactSupport_integral_chiSmallB_sq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) :
    HasCompactSupport (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) := by
  set F : ℝ³ → ℝ := fun u => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2 with hF
  set R : ℝ := Real.sqrt 3 * (ℓ / 2 + (ℓ * d) / 2) / (ℓ * d) with hR
  have hsub : Function.support F ⊆ closedBall (0 : ℝ³) R := by
    intro u hu
    have hu' : (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) ≠ 0 := by
      simpa [hF] using hu
    have hnorm : ‖u‖ ≤ R := by
      rw [hR]
      exact norm_le_of_integral_chiSmallB_sq_ne_zero hM hℓ hd hu'
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hnorm
  change IsCompact (tsupport F)
  change IsCompact (closure (Function.support F))
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) R) isClosed_closure
    (closure_minimal hsub isClosed_closedBall)

/-- **The per-`u` cutoff mass is integrable over `u`.**  `u ↦ ∫_x χ_{B(u)}(x)² dx`
is continuous (`Submission.BoseGases.chiSmallB_partial_integral_continuous`) and
compactly supported (`hasCompactSupport_integral_chiSmallB_sq`), hence
`MeasureTheory.Integrable` for the Lebesgue measure on `ℝ³`. -/
lemma integrable_chiSmallB_mass {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      ∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) := by
  have hcont : Continuous (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) :=
    chiSmallB_partial_integral_continuous hM hℓ hd
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_integral_chiSmallB_sq hM hℓ hd)

end Work.SmallBoxSliding

end
