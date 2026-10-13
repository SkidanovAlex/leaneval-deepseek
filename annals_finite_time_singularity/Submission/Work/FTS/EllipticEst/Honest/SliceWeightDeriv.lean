/-
Work module: the pointwise derivatives of the two angular weights `sig η` and `rho η`
of `SliceIbpDefs` on the open interval `Iθo = (0, π/2)`.

* `sig η θ = sin(2θ)^{-η}` has derivative `sigD η θ = -2η cos(2θ) sin(2θ)^{-η-1}`;
* `rho η θ = cos(2θ) sin(2θ)^{-η-1}` has derivative
  `rhoD η θ = -2 sin(2θ)^{-η} - 2(η+1) cos²(2θ) sin(2θ)^{-(2+η)}`.

Both are plain chain-rule computations: on `(0, π/2)` the base `sin(2θ)` is strictly
positive, so `HasDerivAt.rpow_const` applies to `x ↦ x^{-η}` (resp. `x ↦ x^{-η-1}`
together with the product rule for `cos(2θ)·(·)`).  The only algebra is
`Real.rpow_add` at the positive base `sin(2θ)`, converting
`sin(2θ) · sin(2θ)^{-η-1}` into `sin(2θ)^{-η}`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

/-- On the open interval `Iθo` the base `sin(2θ)` is strictly positive. -/
theorem sin_two_pos_of_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) := by
  rw [Iθo, Set.mem_Ioo] at hθ
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- The derivative of `θ ↦ sin(2θ)` on the open interval. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := hasDerivAt_const_mul (2 : ℝ)
  exact (HasDerivAt.comp (hh₂ := Real.hasDerivAt_sin (2 * θ)) (hh := h1)).congr_deriv (by ring)

/-- The derivative of `θ ↦ cos(2θ)` on the open interval. -/
theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := hasDerivAt_const_mul (2 : ℝ)
  exact (HasDerivAt.comp (hh₂ := Real.hasDerivAt_cos (2 * θ)) (hh := h1)).congr_deriv (by ring)

/-- The weight `sig η` has derivative `sigD η` at every point of the open interval. -/
theorem sig_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    HasDerivAt (sig η) (sigD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Iθo hθ
  have hpow := (hasDerivAt_sin_two θ).rpow_const (p := -η) (Or.inl (ne_of_gt hspos))
  refine hpow.congr_deriv ?_
  simp only [sigD]
  ring

/-- The weight `rho η` has derivative `rhoD η` at every point of the open interval. -/
theorem rho_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    HasDerivAt (rho η) (rhoD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Iθo hθ
  have hpow := (hasDerivAt_sin_two θ).rpow_const (p := -η - 1) (Or.inl (ne_of_gt hspos))
  have hprod := (hasDerivAt_cos_two θ).mul hpow
  refine hprod.congr_deriv ?_
  rw [show -η - 1 - 1 = -η - 2 by ring]
  -- `sin(2θ) · sin(2θ)^{-η-1} = sin(2θ)^{-η}` at the positive base
  have hrw : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η - 1) = Real.sin (2 * θ) ^ (-η) := by
    nth_rewrite 1 [← Real.rpow_one (Real.sin (2 * θ))]
    rw [← Real.rpow_add hspos (1 : ℝ) (-η - 1)]
    congr 1
    ring
  simp only [rhoD]
  rw [show (-2 * Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (-η - 1)
        = -2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η - 1)) by ring, hrw]
  rw [show -η - 2 = -(2 + η) by ring]
  ring

theorem SliceWeightDeriv (η : ℝ) :
    (∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo,
        HasDerivAt (Work.FTS.EllipticEst.Honest.sig η) (Work.FTS.EllipticEst.Honest.sigD η θ) θ) ∧
    (∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo,
        HasDerivAt (Work.FTS.EllipticEst.Honest.rho η) (Work.FTS.EllipticEst.Honest.rhoD η θ) θ) :=
  ⟨fun _ hθ => sig_hasDerivAt η hθ, fun _ hθ => rho_hasDerivAt η hθ⟩

end Work.FTS.EllipticEst.Honest
