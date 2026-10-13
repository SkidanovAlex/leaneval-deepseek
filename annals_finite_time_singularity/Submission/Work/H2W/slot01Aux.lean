/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared helpers for the slice form of the `(0,1)`-slot estimate (`slot01SliceBound`)

This module collects the elementary facts about the angular weight
`σ_γ(θ) = sin(2θ)^{2-γ}` (`γ = gam α`) and about the `(0,1)`-slot of the weighted ℋ²-integrand
that the slice estimate `Work.H2W.slot01SliceBound` (and the lemmas requested alongside it)
consume:

* `sq_mul_sq_rpow_neg` — the `rpow` algebra `s^2 · (s^{-γ/2})^2 = s^{2-γ}`;
* `wt_mixed_sq` — the weight identity
  `(D_θ f · Wt)² = w² · ((∂_θ f)² · sin(2θ)^{2-γ})` on `Iθ`;
* `aesm_mixed01_sq` — a.e. strong measurability of the `(0,1)`-summand;
* `integrableOn_pth_mixed01` — **the slot extractor**: from `HkMem α 2 f` (which demands the
  honesty of `HkIntegrand α 2 f` on *every* angular slice `z ∈ Iz`) one gets, for every `z > 0`,
  the integrability of the single `(0,1)`-summand
  `θ ↦ (∂_θ f(z,θ))² · sin(2θ)^{2-γ}`.

The last statement is what makes the four right-hand sides of `slot01SliceBound` honest at every
`z > 0`: applied to `f = F`, to `f = z² ∂_z²Ψ` and to `f = ∂_θ²Ψ` it gives the honesty of the
`F`-, `z²∂_z²Ψ`- and `∂_θ³Ψ`-slots.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- `sin(2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
theorem sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `σ_γ(θ) = sin(2θ)^{2-γ}` is nonnegative on `Iθ`. -/
theorem sig_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _

/-- The angular weight `σ_γ(θ) = sin(2θ)^{2-γ}` is at most `1` on `Iθ` (`0 ≤ 2 - γ`). -/
theorem sig_le_one {γ : ℝ} (hγ : γ ≤ 2) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - γ) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg_Iθ' hθ) (Real.sin_le_one _) (by linarith)

/-- `s^2 * (s^(-(γ/2)))^2 = s^(2-γ)` for `0 ≤ s` and `0 < γ < 2`. -/
theorem sq_mul_sq_rpow_neg {s γ : ℝ} (hs : 0 ≤ s) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    s ^ 2 * (s ^ (-(γ / 2))) ^ 2 = s ^ (2 - γ) := by
  rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_natCast s 2).symm,
    show (s ^ (-(γ / 2))) ^ 2 = (s ^ (-(γ / 2))) ^ (2 : ℝ) from
      (Real.rpow_natCast (s ^ (-(γ / 2))) 2).symm]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    rw [Real.zero_rpow (by linarith : (-(γ / 2)) ≠ 0),
      Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
      Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)]
    ring
  · rw [← Real.rpow_mul h.le (-(γ / 2)) 2, ← Real.rpow_add h]
    congr 1
    ring

/-- **The squared weight identity of the `(0,1)`-slot.**
On `Iθ`, `(D_θ f · Wt α)² = w(z)² · ((∂_θ f)² · sin(2θ)^{2-γ})`. -/
theorem wt_mixed_sq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) (z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ' hθ
  have hγ0 : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have key := sq_mul_sq_rpow_neg (s := Real.sin (2 * θ)) hs hγ0 hγ2
  show (Real.sin (2 * θ) * Work.Spaces.pth f z θ
      * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
  linear_combination (Work.Spaces.pth f z θ ^ 2 * (Work.Spaces.w z) ^ 2) * key

/-- `Wt α z ·` is measurable. -/
theorem measurable_Wt (α z : ℝ) : Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  rw [show (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ => Work.Spaces.w z * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
      from rfl]
  exact measurable_const.mul
    ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).pow_const _)

/-- A.e. strong measurability of the `(0,1)`-summand of `HkIntegrand`. -/
theorem aesm_mixed01_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)
  rw [show (fun θ : ℝ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = fun θ => (Real.sin (2 * θ) * Work.Spaces.pth f z θ * Work.Spaces.Wt α z θ) ^ 2
      from rfl]
  exact ((((hsin.mul (measurable_deriv _)).mul (measurable_Wt α z)).pow_const 2)).aestronglyMeasurable

/-- **The `(0,1)`-slot extractor.**  From the honesty of the full `ℋ²`-integrand of `f` on every
angular slice one gets, for every `z > 0`, the integrability of the single `(0,1)`-summand
`θ ↦ (∂_θ f(z,θ))² · sin(2θ)^{2-γ}` of the `ℋ²`-norm of `f`. -/
theorem integrableOn_pth_mixed01 {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 2 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Iθ := by
    refine Integrable.mono' (hmem.1 z hzI) (aesm_mixed01_sq α f z) ?_
    filter_upwards with θ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ 1 0 (by norm_num) (by norm_num)
  have hw : ((Work.Spaces.w z) ^ 2) ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  refine (hsum.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [wt_mixed_sq hα hα4 f z hθ, inv_mul_cancel_left₀ hw]

end

end Work.H2W
