import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Submission.Work.BoseBoxFock.cutFam_exists
import Submission.Work.BoseBoxFock.lap3_ibp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lap3_decay_aux` — vocabulary for the cutoff proof of `lap3_ibp_of_decay`

`Submission/Work/BoseBoxFock/lap3_ibp_of_decay.lean` proves the integration-by-parts identity
`∫ f · Δ³ g = ∫ (Δ³ f) · g` for smooth `f` (`Δ³ f` integrable) and *bounded* smooth `g` whose
derivatives decay in the sense that `p ↦ ‖f p‖ ‖D^k g p‖` is integrable for `k ≤ 6`.

The route is a cutoff argument: multiply `g` by the smooth family `θ R` of
`cutFam_exists` (`θ R = 1` on `B(0,R)`, `θ R = 0` off `B(0,2R)`), use the compactly
supported identity `lap3_ibp` at each `R`, and let `R → ∞` by dominated convergence.

This module collects the shared vocabulary of that argument:

* `CutoffHyp θ` — the bundle of properties of the cutoff family (exactly the conclusion of
  `cutFam_exists`), together with `cutoffHyp_exists`;
* `norm_iteratedFDeriv_ofReal` — the complex lift `ℝ → ℂ` is an isometry for
  `iteratedFDeriv`, so the derivative bounds of a real cutoff carry over verbatim;
* `cutoff_deriv_bound_le` — the uniform-in-`R ≥ 1` derivative bound for the complex cutoff
  `fun y => ((θ R y : ℝ) : ℂ)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The bundle of properties of the cutoff family used by the decay integration by parts:
smoothness, values in `[0,1]`, `θ R = 1` on `closedBall 0 R`, `θ R = 0` off `closedBall 0 (2R)`,
compact support, and the scaling derivative bound `‖D^k (θ R) x‖ ≤ C / R^k` with `C`
independent of `R ≥ 1`.  This is exactly the conclusion of `cutFam_exists`. -/
structure CutoffHyp (θ : ℝ → E3 → ℝ) : Prop where
  contDiff : ∀ R, ContDiff ℝ (⊤ : ENat) (θ R)
  nonneg : ∀ R x, 0 ≤ θ R x
  le_one : ∀ R x, θ R x ≤ 1
  eq_one : ∀ R, 0 < R → ∀ x, ‖x‖ ≤ R → θ R x = 1
  eq_zero : ∀ R, 0 < R → ∀ x, 2 * R ≤ ‖x‖ → θ R x = 0
  compactSupport : ∀ R, 0 < R → HasCompactSupport (θ R)
  derivBound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 1 ≤ R → ∀ x,
      ‖iteratedFDeriv ℝ k (θ R) x‖ ≤ C / R ^ k

/-- A cutoff family with the properties above exists. -/
theorem cutoffHyp_exists : ∃ θ : ℝ → E3 → ℝ, CutoffHyp θ := by
  obtain ⟨θ, h1, h2, h3, h4, h5, h6⟩ := cutFam_exists
  exact ⟨θ, h1, (fun R x => (h2 R x).1), (fun R x => (h2 R x).2), h3, h4, h5, h6⟩

/-- Composition with the isometric embedding `ℝ → ℂ` does not change the norm of an iterated
derivative. -/
lemma norm_iteratedFDeriv_ofReal {u : E3 → ℝ} (hu : ContDiff ℝ (⊤ : ENat) u) (k : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ k (fun y => ((u y : ℝ) : ℂ)) x‖ = ‖iteratedFDeriv ℝ k u x‖ := by
  have h : (fun y : E3 => ((u y : ℝ) : ℂ)) = ⇑Complex.ofRealLI ∘ u := rfl
  rw [h]
  exact LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI hu.contDiffAt
    (WithTop.coe_le_coe.mpr le_top)

/-- The uniform-in-`R ≥ 1` bound on the iterated derivatives of the *complex* cutoff
`fun y => ((θ R y : ℝ) : ℂ)`. -/
lemma cutoff_deriv_bound_le {θ : ℝ → E3 → ℝ} (hθ : CutoffHyp θ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 1 ≤ R → ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => ((θ R y : ℝ) : ℂ)) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hθ.derivBound k
  refine ⟨C, hC0, fun R hR x => ?_⟩
  rw [norm_iteratedFDeriv_ofReal (hθ.contDiff R) k x]
  refine (hC R hR x).trans ?_
  rw [div_le_iff₀ (by positivity)]
  exact le_mul_of_one_le_right hC0 (one_le_pow₀ hR)

end Work.BoseBoxFock

end
