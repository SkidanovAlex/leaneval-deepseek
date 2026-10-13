/-
# The open quadrant `(0,∞) × (0,π/2)` and the class of smooth functions on it

`CommutZ_HkIntegrand_add_le` is stated for `u, v` which are `C^∞` on the *open*
quadrant `(0,∞) × (0,π/2)` (not on a neighbourhood of the closed quadrant).  The
existing `DerivLike` instances `Work.Spaces.Zb_DerivLike` / `Work.Spaces.Tb_DerivLike`
are formulated on the larger open set `Work.Spaces.quadU = (-1,∞) × (0,π/2)`, so they
do not apply directly.  This file introduces the matching pair for the open quadrant,
`quadQ` and `SmoothQ`, together with the trivial closure properties.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeDefs
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Coercivity

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def quadQ : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

lemma isOpen_quadQ : IsOpen quadQ := isOpen_Ioi.prod isOpen_Ioo

/-- The class of uncurried functions which are `C^∞` on the open quadrant `quadQ`. -/
def SmoothQ (F : ℝ × ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ F quadQ

lemma SmoothQ.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothQ F) {p : ℝ × ℝ}
    (hp : p ∈ quadQ) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (isOpen_quadQ.mem_nhds hp)).differentiableAt (by norm_num)

/-- `SmoothQ` is closed under `+`, `*` and scalar multiplication. -/
theorem SmoothQ_FunClass : Work.Spaces.FunClass (X := ℝ × ℝ) SmoothQ where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ ⊤ (fun p => c * A p) quadQ
    exact ContDiffOn.const_smul c hA

end Work.Coercivity
