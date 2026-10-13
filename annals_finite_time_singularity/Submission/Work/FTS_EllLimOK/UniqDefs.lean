/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.UniqDefs` — the vocabulary of the uniqueness (energy) argument

The uniqueness obligation `ClosedUniq3` compares two order-`3` jet-cluster-limits `Ψ`, `Ψ'` of
the same operator along the same sequence.  Both satisfy the same elliptic law with the same
source, so their difference

`diff Ψ Ψ' = (fun z θ => Ψ z θ - Ψ' z θ)`

solves the *homogeneous* problem, and the chapter's uniqueness proof runs on it:

* its angular moment `Fstar (diff Ψ Ψ')` vanishes (`Fstar_zero`);
* its angular `L²` mass `PhiD Ψ Ψ' z = ∫_θ (diff Ψ Ψ' z θ)² dθ` is a nonnegative, integrable
  function of `z`, whose Euler gap inequality holds (`EnergyGap`);
* the Grönwall lemma `phi_eq_zero_of_euler_gap_weighted` then forces `PhiD Ψ Ψ' ≡ 0`, whence
  `Ψ = Ψ'` on the open quadrant.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS_EllLimOK.BoxReg

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

/-- The **difference of two profiles** — the solution of the homogeneous elliptic problem in the
uniqueness argument. -/
def diff (Ψ Ψ' : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Ψ z θ - Ψ' z θ

@[simp] theorem diff_apply (Ψ Ψ' : ℝ → ℝ → ℝ) (z θ : ℝ) :
    diff Ψ Ψ' z θ = Ψ z θ - Ψ' z θ := rfl

/-- The **angular `L²` mass of the difference of two profiles**: `Φ(z) = ∫_θ δ(z,θ)² dθ`. -/
def PhiD (Ψ Ψ' : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ) ^ 2

@[simp] theorem PhiD_apply (Ψ Ψ' : ℝ → ℝ → ℝ) (z : ℝ) :
    PhiD Ψ Ψ' z = ∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ) ^ 2 := rfl

theorem PhiD_nonneg (Ψ Ψ' : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ PhiD Ψ Ψ' z :=
  integral_nonneg fun θ => sq_nonneg _

/-- `BoxReg` of the difference of two box-regular profiles. -/
theorem BoxReg.diff {Ψ Ψ' : ℝ → ℝ → ℝ} (hΨ : BoxReg Ψ) (hΨ' : BoxReg Ψ') :
    BoxReg (diff Ψ Ψ') := by
  change BoxReg (fun z θ => Ψ z θ - Ψ' z θ)
  exact hΨ.sub hΨ'

end Work.FTS_EllLimOK
