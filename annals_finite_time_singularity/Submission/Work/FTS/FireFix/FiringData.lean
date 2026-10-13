/-
# `Work.FTS.FireFix.FiringData` — the auxiliary clauses of the firing theorem

This module contains the clauses of the firing theorem `blowupAtTop_of_regPkg'` that are proved
from the *structural* data of the reconstruction (as opposed to the analytic clauses
`physOmega_timeDeriv_continuous`, `physOmega_fderiv_locallyIntegrable` and
`physOmega_hasDerivWithinAt` of `FireFix/Clauses/`, which are proved separately):

* `negPhysOmega_lower` — the `c/(C.T − t)` lower bound for `‖ω(·,t)‖_∞`, from the smallness of the
  perturbation (`hsmall`) via `Work.FTS.Physical.RegPkg.profFull_ge_of_small` and
  `fakeLower_of_Fstar`, together with the clock comparison `A(τ(t)) ≤ 2(C.T − t)`.

The factor `2` of the clock (design correction 2, `C.A = 2·A`) enters in the conversion
`A τ = C.A τ / 2`, which is what makes the bound `c/(2(C.T − t))` available.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.FireFix.PhysFields
import Submission.Work.FTS.FireFix.VortEqLocal
import Submission.Work.FTS.FireFix.Prime.PhysVortBundle
import Submission.Work.FTS.Physical.RegPkg.profFull_ge_of_small
import Submission.Work.FTS.Physical.RegPkg.fakeLower_of_Fstar
import Submission.Work.FTS.Physical.Clock.A_le_two_mul_tail
import Submission.Work.FTS.Physical.Clock.tail_le_two_mul
import Submission.Work.FTS.Physical.Clock.T_pos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Physical (PhysClock)

/-- **The `c/(C.T − t)` lower bound for the sup-norm of the negated physical vorticity.**  From the
smallness of the perturbation (`hsmall`) the full profile is `≥ 3α/100` at some point of the domain
at every fake time, whence the vorticity is `≥ c/A(τ(t)) ≥ c/(2(C.T − t))` by the clock comparison
`A(τ(t)) ≤ C.T − t`. -/
theorem negPhysOmega_lower {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * (α : ℝ) / 200) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 C.T,
      c / (C.T - t) ≤ ⨆ x : R3, ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖ := by
  have hApos : ∀ τ : ℝ, 0 ≤ τ → 0 < A τ := fun τ hτ =>
    (hreg (τ + 1) (by linarith)).hA τ ⟨hτ, by linarith⟩
  have hBpos : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ := fun τ hτ =>
    (hreg (τ + 1) (by linarith)).hB τ ⟨hτ, by linarith⟩
  have hF := Work.FTS.Physical.RegPkg.profFull_ge_of_small hα (by linarith [hα13]) hsmall
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    Work.FTS.Physical.RegPkg.fakeLower_of_Fstar hα hApos hBpos hF
  refine ⟨c₀ / 2, by linarith, fun t ht => ?_⟩
  have hτnn : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C ht
  have hTt : (0 : ℝ) < C.T - t := sub_pos.mpr ht.2
  have htail : C.A (Work.FTS.Physical.clockInv C t) ≤ 2 * (C.T - t) := by
    have h := Work.FTS.Physical.Clock.A_le_two_mul_tail C hτnn
    rwa [Work.FTS.Physical.clockInv_clock C ht] at h
  have hAτ : A (Work.FTS.Physical.clockInv C t) ≤ 2 * (C.T - t) := by
    have h2 : A (Work.FTS.Physical.clockInv C t)
        = C.A (Work.FTS.Physical.clockInv C t) / 2 := by
      have h := hAeq (Work.FTS.Physical.clockInv C t) hτnn
      linarith
    rw [h2]; linarith [htail]
  have hAposτ : 0 < A (Work.FTS.Physical.clockInv C t) := hApos _ hτnn
  obtain ⟨x, hx⟩ := hc₀ (Work.FTS.Physical.clockInv C t) hτnn
  have hstep : c₀ / (2 * (C.T - t)) ≤ c₀ / A (Work.FTS.Physical.clockInv C t) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hAposτ hAτ) hc₀pos.le
  have hrew : (c₀ / 2) / (C.T - t) = c₀ / (2 * (C.T - t)) := by rw [div_div]
  have hbd : BddAbove (Set.range (fun x : R3 =>
      ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖)) := by
    obtain ⟨M, _hM0, hM⟩ := Prime.physVort_bound
      (hreg (Work.FTS.Physical.clockInv C t + 1) (by linarith))
    refine ⟨M, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hM (Work.FTS.Physical.clockInv C t) ⟨hτnn, by linarith⟩ y
    simpa only [Work.FTS.Physical.physOmega_apply, norm_neg] using h
  rw [hrew]
  calc c₀ / (2 * (C.T - t)) ≤ c₀ / A (Work.FTS.Physical.clockInv C t) := hstep
    _ ≤ ‖Work.FTS.Regularity.physVort (α : ℝ) A B g x (Work.FTS.Physical.clockInv C t)‖ := hx
    _ = ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖ := by
        rw [Work.FTS.Physical.physOmega_apply, norm_neg]
    _ ≤ ⨆ x : R3, ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖ := le_ciSup hbd x

end Work.FTS.FireFix
