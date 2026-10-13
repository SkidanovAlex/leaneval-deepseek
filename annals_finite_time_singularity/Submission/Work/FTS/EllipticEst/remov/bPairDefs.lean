/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`0` weight `ρ` and the `H⁰`-integrand, for the `-∂_θθΨ` pairing identity

This module fixes the weight

  `Wt z θ = w(z)² · sin(2θ)^{-η}`   (`Work.Spaces.w`, `Work.FTS.EllipticEst.sEta`),

which is *the* level-`0` `HkIntegrand` weight, and records the two rewritings that the
pairing identity `Work.FTS.EllipticEst.remov.bPairingIdentity` uses:

* `HkIntegrand α 0 g z θ = (g z θ)² · Wt z θ` on `Iθ` (`HkIntegrand_zero_eq_Wt`),
  the pointwise identity that converts `HkSq α 0 g` into a `Wt`-weighted square integral;
* the *slices* of `HkMem α 0 g` in `Wt`-form: an angular slice and the outer `z`-integral
  (`HkMem_zero_slice_Wt`, `HkMem_zero_outer_Wt`).

Also recorded: `sEta` is integrable on `Iθ` (the exponent `η = 99/100 < 1`), the measurability
of `Iz`/`Iθ`, and the fact that at level `0` the `HkIntegrand` does not depend on `α` at all
(`HkMem_zero_congr`), which lets the level-`0` memberships be transported between parameters.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- The level-`0` weight `ρ z θ = w(z)² · sin(2θ)^{-η}`: the angular weight `sEta` times the
*square* of the radial weight `w`. -/
def Wt (z θ : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem measurableSet_Iz : MeasurableSet Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]; exact measurableSet_Ici

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩) _

/-- The level-`0` weight is nonnegative on `Iθ`. -/
theorem Wt_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wt z θ :=
  mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)

/-- The level-`0` weight vanishes on the axis `z = 0` (totalised division). -/
theorem Wt_zero_left (θ : ℝ) : Wt 0 θ = 0 := by
  simp only [Wt, Work.Spaces.w]
  norm_num

/-- The angular weight is integrable on `Iθ` (`η = 99/100 < 1`). -/
theorem integrableOn_sEta :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- At level `0` the `HkIntegrand` is the single `Wt`-weighted square. -/
theorem HkIntegrand_zero_eq_Wt (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ = (g z θ) ^ 2 * Wt z θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey, Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ]
  simp only [Wt, Work.FTS.EllipticEst.sEta]
  ring

/-- The angular slices of `HkMem α 0 g`, in `Wt`-form. -/
theorem HkMem_zero_slice_Wt {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Wt z θ) Work.Spaces.Iθ :=
  (hmem.1 z hz).congr_fun
    (fun θ hθ => HkIntegrand_zero_eq_Wt α g z hθ) measurableSet_Iθ

/-- The outer `z`-integral of the `H⁰`-integrand of `HkMem α 0 g`, in `Wt`-form. -/
theorem HkMem_zero_outer_Wt {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Wt z θ) Work.Spaces.Iz :=
  hmem.2.congr_fun
    (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
      (fun θ hθ => HkIntegrand_zero_eq_Wt α g z hθ)) measurableSet_Iz

/-- `HkSq α 0 g` is the `Wt`-weighted square integral of `g`. -/
theorem HkSq_zero_eq_Wt (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Wt z θ := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Iz fun z _ => ?_
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
    (fun θ hθ => HkIntegrand_zero_eq_Wt α g z hθ)

/-- At level `0` the `HkIntegrand` does not depend on the parameter `α` (its mixed-derivative
sum is empty). -/
theorem HkIntegrand_zero_eq_indep (α α' : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ = Work.Spaces.HkIntegrand α' 0 g z θ := by
  simp [Work.Spaces.HkIntegrand]

/-- `HkMem _ 0 g` is independent of the parameter `α`. -/
theorem HkMem_zero_congr {α α' : ℝ} {g : ℝ → ℝ → ℝ} :
    Work.Spaces.HkMem α 0 g ↔ Work.Spaces.HkMem α' 0 g := by
  constructor
  · intro h
    refine ⟨fun z hz => (h.1 z hz).congr_fun
        (fun θ _ => HkIntegrand_zero_eq_indep α α' g z θ) measurableSet_Iθ, ?_⟩
    exact h.2.congr_fun (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
      (fun θ _ => HkIntegrand_zero_eq_indep α α' g z θ)) measurableSet_Iz
  · intro h
    refine ⟨fun z hz => (h.1 z hz).congr_fun
        (fun θ _ => HkIntegrand_zero_eq_indep α' α g z θ) measurableSet_Iθ, ?_⟩
    exact h.2.congr_fun (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
      (fun θ _ => HkIntegrand_zero_eq_indep α' α g z θ)) measurableSet_Iz

end Work.FTS.EllipticEst.remov
