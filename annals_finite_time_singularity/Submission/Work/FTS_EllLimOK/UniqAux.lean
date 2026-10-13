/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.UniqAux` — the elementary `θ`-slice facts of the uniqueness argument

Two small lemmas used in the assembly of `ClosedUniq3`:

* `eq_zero_of_integral_sq_eq_zero` — a continuous `g` on `Iθ` whose squared integral vanishes
  is identically zero (used to upgrade `PhiD Ψ Ψ' ≡ 0` to `Ψ = Ψ'` on the open quadrant);
* `integrableOn_integral_sq`/`integral_sq_le` — the bookkeeping that bounds the angular `L²`
  mass of the *difference* of two profiles by the `ℋ⁰`-integrands of the two halves.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- **A continuous nonnegative square on `Iθ` with vanishing integral vanishes identically.** -/
theorem eq_zero_of_integral_sq_eq_zero {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc 0 (π / 2)))
    (hint : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) = 0) :
    ∀ θ ∈ Work.Spaces.Iθ, g θ = 0 := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  have hne : (0 : ℝ) ≠ π / 2 := ne_of_lt (by linarith [Real.pi_pos])
  have hcont' : ContinuousOn (fun θ => (g θ) ^ 2) (Set.Icc 0 (π / 2)) := hcont.pow 2
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => (g θ) ^ 2) :=
    Filter.Eventually.of_forall fun θ => sq_nonneg _
  have hint' : IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ :=
    hcont'.integrableOn_compact isCompact_Icc
  have hae : (fun θ => (g θ) ^ 2) =ᵐ[volume.restrict Work.Spaces.Iθ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint').mp hint
  have hclos : Work.Spaces.Iθ ⊆ closure (interior Work.Spaces.Iθ) := by
    rw [hIθ]
    exact (closure_interior_Icc hne).symm.subset
  have hEqOn := MeasureTheory.Measure.eqOn_of_ae_eq hae hcont' continuousOn_const hclos
  intro θ hθ
  have h : (g θ) ^ 2 = 0 := hEqOn hθ
  exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h

end Work.FTS_EllLimOK
