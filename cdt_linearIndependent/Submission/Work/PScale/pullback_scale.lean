import Mathlib
import Submission.CDTPlan.InterfacesA2

/-! Guidance from the project lead (the requester):

# Area PScale — pullbacks under z ↦ ρz (`PullbackScale`), small generic lemma
Given P, N from `PullbackMero f φ`: use P(ρz) (polynomial `P.comp (C ρ * X)`, value at 0 unchanged) and
N(ρz) (holomorphic on ball(0,1) since ρ ≤ 1); the HasSum germ at 0 transports by continuity of z ↦ ρz.
Contracts: `Submission/CDTPlan/InterfacesA2.lean` (Theorem A template), `InterfacesA.lean` (ψ_A, φ_A,
ANumerics, Zagier integrality), `InterfacesC.lean` (intY, tq, dY), `Interfaces.lean`.
The Theorem-C side has already solved the analogous pieces — REUSE, do not rebuild:
`Submission/Work/CPhi/` (lift of φ_C), `Submission/Work/CPull/` (germs.lean: `germ_of_even`,
`pullbackMero_of_germ`, `germ_intY`, `germ_tq`, pullbackMero_B2/B3/B4, deriv_phiC_zeros_finite),
`Submission/Work/CLift/` (continuation of P along Φ with OdeContinuation),
`Submission/Work/CDcl/` (symmetrised-powers route to the d/dy-closure), `Submission/Work/CDen/`.
Axiom-clean A-side facts: `Submission.Work.Purge.a_side_clean` bundles HA_ode, HB_ode, HC_ode,
GA_odeLHS_eq_zero, Cintegral/Aintegral identities, overconvergesB/C (use it instead of the
native_decide-tainted originals); `Work.ZagBI` re-proved HA_ode cleanly too. Never depend on
`native_decide` (check #print axioms).
-/

namespace Work.PScale

open Submission.CDTPlan
open Complex Metric Filter Topology
open scoped BigOperators

/-- The scaled map `z ↦ ρ z` (`0 < ρ ≤ 1`) maps the unit ball into itself. -/
private lemma mapsTo_scale (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Set.MapsTo (fun z : ℂ => (ρ : ℂ) * z) (ball 0 1) (ball 0 1) := by
  intro z hz
  simp only [mem_ball, dist_zero_right] at hz ⊢
  have h1 : ‖((ρ : ℂ))‖ = ρ := by simp [abs_of_pos hρ0]
  rw [norm_mul, h1]
  nlinarith [norm_nonneg z, hz]

/-- `z ↦ ρ z` is continuous at `0` and fixes `0`. -/
private lemma tendsto_scale (ρ : ℝ) :
    Tendsto (fun z : ℂ => (ρ : ℂ) * z) (𝓝 0) (𝓝 0) := by
  simpa using (tendsto_const_nhds.mul tendsto_id :
    Tendsto (fun z : ℂ => (ρ : ℂ) * z) (𝓝 (0 : ℂ)) (𝓝 ((ρ : ℂ) * 0)))

/-- `PullbackMero` is stable under shrinking the disc: if the germ of `f ∘ φ` at `0` is
meromorphic with polynomial denominator `P ∤ 0`, then so is that of `f ∘ (z ↦ φ (ρz))`, with
denominator `P(ρX)` (which does not vanish at `0` either) and numerator `N(ρz)`. -/
theorem pullback_scale : PullbackScale := by
  intro f φ ρ hρ0 hρ1 hp
  obtain ⟨P, N, hP0, hN, hgerm⟩ := hp
  refine ⟨P.comp (Polynomial.C (ρ : ℂ) * Polynomial.X), fun z => N (ρ * z), ?_, ?_, ?_⟩
  · -- the polynomial denominator `P(ρX)` still does not vanish at `0`
    rw [Polynomial.eval_comp]
    simp [hP0]
  · -- the numerator `z ↦ N (ρ z)` is holomorphic on the unit disc, since `ρ ≤ 1`
    have hlin : DifferentiableOn ℂ (fun z : ℂ => (ρ : ℂ) * z) (ball 0 1) :=
      (differentiableOn_const _).mul differentiableOn_id
    exact hN.comp hlin (mapsTo_scale ρ hρ0 hρ1)
  · -- the `HasSum` germ at `0` transports along the continuous map `z ↦ ρ z`
    have h2 := Filter.Tendsto.eventually (tendsto_scale ρ) hgerm
    simpa [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using h2

end Work.PScale
