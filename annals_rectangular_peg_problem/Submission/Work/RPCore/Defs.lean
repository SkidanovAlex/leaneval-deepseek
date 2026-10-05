import Submission.Work.RPV.Defs
import Submission.Work.RPCore.Port.ODE.SmoothFlow
import Submission.Work.RPCore.Port.ODE.GlobalFlow
import Mathlib
import Submission.Work.RPCore.Port.Whitney.noRetractionBallSphere

/-!
# `Work.RPCore`: CORE block of the generating-function route

Auxiliary definitions for the CORE block (nodes C0–C5 and the assembly) of
`RECTPEG_ROUTE_LEAD.md`.  The shared vocabulary lives in `Submission.Work.RPV.Defs` and is
imported here; the node statements themselves are stated in namespace `RectPeg` (as in the
route document) in the sibling modules of this directory.

What lives here:

* `IsSymplectic` : the map preserves `ω = symp` (linearised form);
* `autoVF` : the autonomous vector field `(1, X_H)` on `ℝ × PS` used to make the
  time-dependent Hamiltonian flow autonomous;
* `slab` : the support slab `{|q₁| + |p₁| + |p₂| ≥ R}` of `CptPerHam`;
* a few elementary transport lemmas for `Tk`, `slab`, `hamVF` that every node uses.

The ported fleet code (smooth flows, no-retraction) lives under `Submission/Work/RPCore/Port/`.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

open Work.RPV

namespace Work.RPCore

/-- `ψ` preserves the symplectic form `ω = symp`:  the linearised form of symplecticity. -/
def IsSymplectic (ψ : PS → PS) : Prop :=
  ∀ x a b, symp (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = symp a b

/-- The support slab of a compactly supported Hamiltonian: `{|q₁| + |p₁| + |p₂| ≥ R}`. -/
def slab (R : ℝ) : Set PS := {x | R ≤ |x.1.1| + |x.2.1| + |x.2.2|}

@[simp] theorem mem_slab {R : ℝ} {x : PS} : x ∈ slab R ↔ R ≤ |x.1.1| + |x.2.1| + |x.2.2| :=
  Iff.rfl

/-- The autonomous vector field `(1, X_H)` on `ℝ × PS` whose flow, read in the second factor,
is the flow of the time-dependent Hamiltonian `H`. -/
def autoVF (H : ℝ → PS → ℝ) (z : ℝ × PS) : ℝ × PS := (1, hamVF (H z.1) z.2)

@[simp] theorem autoVF_apply (H : ℝ → PS → ℝ) (z : ℝ × PS) : autoVF H z = (1, hamVF (H z.1) z.2) :=
  rfl

theorem autoVF_fst (H : ℝ → PS → ℝ) (z : ℝ × PS) : (autoVF H z).1 = 1 := rfl

/-- `Tk 1` is the shift of the angle `q₂` by `2π`. -/
@[simp] theorem Tk_one_fst (x : PS) : (Tk 1 x).1.1 = x.1.1 := rfl

@[simp] theorem Tk_one_pos (x : PS) : (Tk 1 x).2 = x.2 := rfl

@[simp] theorem Tk_one_q₂ (x : PS) : (Tk 1 x).1.2 = x.1.2 + 2 * π := by simp [Tk]

theorem Tk_zero (x : PS) : Tk 0 x = x := by simp [Tk]

end Work.RPCore
