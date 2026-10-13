/-
Copyright: work module for the Elgindi finite-time singularity project.

# `∂_θΨ` vanishes on the axis `z = 0` when it lies in the weighted `H^0`

For `Ψ` smooth on a neighbourhood of the closed quadrant `[0,∞) × [0,π/2]` and lying in
the weighted space `H^0` *after* differentiation in `θ` (`Work.Spaces.HkMem α 0 (pth Ψ)`,
i.e. the honesty of the integral of `(∂_θΨ · w/ sin(2θ)^{η/2})²`), the whole axis value
`∂_θΨ(0,θ)` vanishes for every `θ ∈ [0,π/2]`.

## The mathematics

The `k = 0` integrand is the single square

  `HkIntegrand α 0 g z θ = (g(z,θ) · w(z)/sin(2θ)^{η/2})² = g(z,θ)² w(z)² sin(2θ)^{-η}`,

with `w(z) = (1+z)²/z² ∼ 1/z²`.  `HkMem α 0 g` therefore says that both iterated integrals of
that square are honest:

* every angular slice `θ ↦ g(z,θ)² sin(2θ)^{-η}` (`z > 0`) is integrable
  (`L2Mem_DzIter_Hwt` for `k = 0`, rescaled by `w(z)²`), and
* the radial slice `z ↦ ∫_θ g(z,θ)² w(z)² sin(2θ)^{-η}` is integrable on `Iz = [0,∞)`.

If now `g 0 θ₀ ≠ 0`, continuity of `g` at `(0,θ₀)` (here: `SmoothNbhd.pth`) gives a whole
rectangle on which `g² ≥ m² > 0`, so the angular integral `∫_θ g² sin(2θ)^{-η}` is bounded
below by a positive constant `c` for all small `z`.  Since `w(z)² ≥ 1/z⁴`, the radial slice
then dominates `c/z⁴` near `0`, which is not integrable there: contradiction.

The two analytic ingredients are the lemmas `theta_integral_lower` (continuity turns into a
uniform lower bound for the angular integral) and `slice_not_integrable_of_lower_bound` (such
a lower bound is incompatible with radial integrability, because `w² ∼ z^{-4}`); both live in
this directory.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.EllipticEst.remov.theta_integral_lower
import Submission.Work.FTS.EllipticEst.remov.slice_not_integrable_of_lower_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The `k = 0` integrand -/

/-- At `k = 0` the `H^k`-integrand is the single square of `g · w/ sin(2θ)^{η/2}`, i.e. the
unweighted expression `g² w² sin(2θ)^{-η}`.  (The mixed sum of `HkIntegrand` is empty, because
its condition `1 ≤ i ∧ i + j ≤ 0` is unsatisfiable.) -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  rw [show Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 by
        simp [Work.Spaces.HkIntegrand]]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-! ## Extraction of the two honesty properties of the `k = 0` integrand -/

/-- **The two integrability properties hidden in `HkMem α 0 g`.**

`HkMem α 0 g` is the honesty of the iterated integral of the single square
`(g · w/ sin(2θ)^{η/2})²`; this lemma extracts the two consequences in the *unweighted*
angular form `g² sin(2θ)^{-η}` that the divergence argument consumes: every angular slice with
`z > 0` is integrable on `Iθ`, and the radial slice `z ↦ ∫_θ g² w² sin(2θ)^{-η}` is integrable
on `Iz`.

The only place where the positivity of `z` matters is the *division* by `w(z)²`, which vanishes
at `z = 0`; the `z`-integral itself becomes the unweighted expression by a pointwise rewriting
(`mul_w_sin_rpow_sq`) alone, so it holds on all of `Iz`. -/
theorem HkMem_zero_slices {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α 0 g) :
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        Work.Spaces.Iz := by
  have hL : Work.Spaces.L2Mem (fun z θ => g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :=
    Work.Coercivity.L2Mem_DzIter_Hwt α 0 g hsm hmem 0 (le_refl 0)
  constructor
  · -- angular slices: divide the weighted integrand by the nonzero constant `w(z)²`
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hwz : Work.Spaces.w z ≠ 0 := by
      simp only [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
    have hbase : MeasureTheory.IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := (hL.1 z hzIz).const_mul _
    refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    show ((Work.Spaces.w z) ^ 2)⁻¹
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
    have h := Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ
    rw [h]
    have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
    field_simp
  · -- the radial integral: a pointwise rewriting inside the integral suffices
    refine hL.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-! ## The main theorem -/

theorem pth_zero_of_HkMem {Ψ : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd Ψ) {α : ℝ}
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ)) :
    ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.pth Ψ 0 θ = 0 := by
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.pth Ψ) := Work.Spaces.SmoothNbhd.pth hsm
  obtain ⟨hsl, hzl⟩ := HkMem_zero_slices hsm' hmem
  intro θ₀ hθ₀
  by_contra hne
  -- `∂_θΨ` is continuous at `(0,θ₀)`: it is smooth on an open neighbourhood of the quadrant
  have hcont : ContinuousAt (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2) (0, θ₀) := by
    have hmem_nhds : Work.Spaces.nbhU ∈ 𝓝 (((0 : ℝ), θ₀) : ℝ × ℝ) :=
      Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU Work.Spaces.zero_mem_Iz hθ₀)
    exact (hsm'.continuousOn).continuousAt hmem_nhds
  obtain ⟨ε, hε, c, hc, hlow⟩ :=
    theta_integral_lower (Work.Spaces.pth Ψ) Work.Spaces.eta θ₀ hθ₀ hcont hne hsl
  exact slice_not_integrable_of_lower_bound (Work.Spaces.pth Ψ) Work.Spaces.eta
    ⟨ε, hε, c, hc, hlow⟩ hzl

end Work.FTS.EllipticEst.remov
