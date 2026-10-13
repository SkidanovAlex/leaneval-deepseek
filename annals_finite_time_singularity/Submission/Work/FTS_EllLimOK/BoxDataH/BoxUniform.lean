/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.BoxUniform` — the box-uniform data of a family, and the slice data

`RulingELF.PkgBoxH` gives, for every box `cbox a b = [a,b] × [0,π/2]` (`0 < a ≤ b`), constants
`K, β > 0` — *uniform in the source* `g` — such that every `E g` is `C²` within the box, all
within-derivatives of order `≤ 2` are bounded by `K · Xn6 α g`, and the second within-derivative
has Hölder modulus `β` with constant `K · Xn6 α g`.

`BoxUniform2 a b H` is the same data for an abstract family `H : ℕ → ℝ → ℝ → ℝ` (the members
`fun z θ => E (fn n) z θ` of a `LimSeq4`, all with `Xn6 α (fn n) ≤ B`, so that `K` can be taken
to be `K_ab · B` for one constant).  It is the hypothesis of the `C^{2,β}` Arzelà–Ascoli crux
`contDiffOn_two_of_boxUniform2`, and it is exactly what `PkgBoxH` supplies along a `LimSeq4`.

`SliceData a b F` bundles the six one-variable within-derivative statements of a `C²`-within-the-
box function `F` needed by the three installments of
`BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-- **The uniform `C^{2,β}` data of a family on a box** — the abstract form of `PkgBoxH` along a
sequence. -/
def BoxUniform2 (a b : ℝ) (H : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∃ K β : ℝ, 0 < β ∧
    (∀ n, ContDiffOn ℝ 2 (Function.uncurry (H n)) (cbox a b)) ∧
    (∀ n k : ℕ, k ≤ 2 → ∀ p ∈ cbox a b,
      ‖iteratedFDerivWithin ℝ k (Function.uncurry (H n)) (cbox a b) p‖ ≤ K) ∧
    (∀ n, ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
      ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (cbox a b) p
        - iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (cbox a b) q‖
        ≤ K * ‖p - q‖ ^ β)

/-- **The slice data** of a function `F` on the box: the six one-variable within-derivatives of
`F`, `wPz F` and `wPth F` on the two intervals of the box.  (The two mixed components are the
`z`-derivative of the `wPth`-slice and the `θ`-derivative of the `wPz`-slice, in this order.) -/
def SliceData (a b : ℝ) (F : ℝ × ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun z' => F (z', θ)) (wPz (cbox a b) F (z, θ)) (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun θ' => F (z, θ')) (wPth (cbox a b) F (z, θ)) (Set.Icc 0 (π / 2)) θ) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun z' => wPz (cbox a b) F (z', θ)) (wPzz (cbox a b) F (z, θ))
      (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun θ' => wPz (cbox a b) F (z, θ')) (wPtz (cbox a b) F (z, θ))
      (Set.Icc 0 (π / 2)) θ) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun z' => wPth (cbox a b) F (z', θ)) (wPzt (cbox a b) F (z, θ))
      (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun θ' => wPth (cbox a b) F (z, θ')) (wPtt (cbox a b) F (z, θ))
      (Set.Icc 0 (π / 2)) θ)

end Work.FTS_EllLimOK.BoxDataH
