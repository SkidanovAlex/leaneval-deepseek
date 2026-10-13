import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/mixedABasic`: the elementary structural layer of `mixedA`

`mixedA`'s right-hand side is the *pure* (`z`-only) part of `HkSq α 2 (z²∂_z²Ψ)`; this module
proves the calculus facts that identify it as such, and nothing else, so that it can be imported
freely (the module carrying the target itself, `H2W/mixedA`, still contains the open `sorry`).

* `DzIter_add`, `pzIter_add` — the `D_z`/`∂_z` iterates compose;
* `z2_mul_deriv_deriv` — pointwise `z² g'' = z(z g')' − z g'` for a one-variable function;
* `z2_pzIter2_eq` — pointwise `z²∂_z² = D_z² − D_z` in the `(z,θ)` variables.

From these, `z²∂_z²` commutes with every `D_z^j` (both are polynomials in `D_z`), which is the
identity used by `H2W/mixedA` and by `H2W/hksqSplitMixed`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The iterates compose -/

theorem DzIter_add (a b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (a + b) f = Work.Spaces.DzIter a (Work.Spaces.DzIter b f) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]

theorem pzIter_add (a b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter (a + b) f = Work.Spaces.pzIter a (Work.Spaces.pzIter b f) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]

/-! ## The operator identity `z²∂_z² = D_z² − D_z` -/

/-- Pointwise form of the operator identity for a single radial slice: for a function `g` of one
variable which is twice differentiable at `z`,
`z² g''(z) = z·(z·g')'(z) − z·g'(z)`. -/
theorem z2_mul_deriv_deriv (g : ℝ → ℝ) (z : ℝ)
    (h1 : DifferentiableAt ℝ g z) (h2 : DifferentiableAt ℝ (deriv g) z) :
    z ^ 2 * deriv (deriv g) z
      = z * deriv (fun z' => z' * deriv g z') z - z * deriv g z := by
  have h : deriv (fun z' => z' * deriv g z') z = deriv (id * deriv g) z := rfl
  rw [h, deriv_mul differentiableAt_id h2]
  simp only [deriv_id, id_eq, one_mul]
  ring

/-- **The pointwise identity `z²∂_z² = D_z² − D_z` in the `(z,θ)` variables.** -/
theorem z2_pzIter2_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h1 : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (h2 : DifferentiableAt ℝ (fun z' => deriv (fun z'' => f z'' θ) z') z) :
    z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ := by
  have h := z2_mul_deriv_deriv (fun z' => f z' θ) z h1 h2
  simpa only [Work.Spaces.DzIter, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.Dz, Work.Spaces.pz] using h

end Work.FTS.EllipticEst.H2W
