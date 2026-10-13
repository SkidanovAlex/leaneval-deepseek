/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.EllExist.Defs` — the honest elliptic solution class of the Galerkin chapter

This module fixes the vocabulary of the `FTS/EllExist` area, whose deliverable is

  `ellClassO_exists : ∃ α₀ > 0, ∀ α ∈ (0,α₀], ∀ g, GalClass α g → ∃ Ψ, EllClassO α g Ψ`

(design `FTS/FTS_ELL_GALERKIN.md` §1, item (b)): every admissible perturbation `g` of the
Galerkin chapter has an elliptic stream function `Ψ` in the class `EllClassO`.

## The class

`EllClassO α g Ψ` bundles exactly the three things the Hamel/linearity construction of the
solution operator `EllSol` needs (design §1 items (b),(c),(d)):

* `IsBslSol α g Ψ` — `Ψ` solves `bslOp α Ψ = g` on the *open* quadrant, with the two Dirichlet
  values and the decay at `z → ∞` (the paper's (PolarBSL) with its boundary conditions);
* `SmoothOpen Ψ` — `Ψ` is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`);
* `TT.EllWeakPos α 4 (orthSource g) (shiftSing α g Ψ)` — the *shifted* unknown
  `shiftSing α g Ψ = Ψ + Gsing α g · sin 2θ` is a datum of the weak hypothesis class of the
  elliptic estimates, with the *orthogonalised* source `orthSource g = g - (15/4) sin 2θ · F_*(g)`.

The shift is the paper's §'The singular term' construction: `sin 2θ` lies in the kernel of the
`α = 0` operator `Lzero`, and `Gsing α g` is chosen so that

  `bslOp α (Ψ + Gsin 2θ) = bslOp α Ψ - (15/4) F_*(g) sin 2θ`,

i.e. so that the right-hand side becomes orthogonal to `sin θ cos²θ`
(`Work.Elliptic.Fstar_orthSource`), which is the solvability condition of `prop:L2`.

## What is NOT in the class

The class deliberately says nothing about the *estimates*: `TT.EllWeakPos` is the hypothesis
bundle of `prop:Hk`, and the estimate itself (`TT.EllEstUnif`) is a separate input of the
chapter (`FTS/EllSol`).  `EllClassO` is exactly the "existence" node.

## A sharp necessary condition (recorded here for the consumer)

Because `EllClassO` asks for `SmoothOpen Ψ` *and* `TT.EllWeakPos` asks for
`C^∞` of `shiftSing α g Ψ` on the open quadrant, the difference

  `shiftSing α g Ψ - Ψ = (fun z θ => Gsing α g z * sin (2θ))`

is `C^∞` on the open quadrant.  Hence

  **`Gsing α g` is `C^∞` on `(0,∞)`** whenever `EllClassO α g Ψ` holds for some `Ψ`;

see `EllClassO.contDiffOn_Gsing`.  Since `Gsing α g = Gstar α g + Gbar α g` is an explicit
functional of the angular moment `F_*(g)(z) = ∫_θ g(z,θ) sinθcos²θ dθ`, this makes the
`smoothness of the angular moment` a genuine part of the existence node.  The area proves
`ContDiffOn ℝ m (Fstar g) (Ioi 0)` for `m ≤ 5` from `GalClass` without further hypotheses
(`Fstar_GalClass.contDiffOn_Fstar_le`), and records the all-orders statement as the sharp
remaining input.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The honest elliptic solution class** of the Galerkin chapter (design §1 (b)).

`EllClassO α g Ψ` says: `Ψ` solves the elliptic problem with source `g` on the open quadrant
(with the Dirichlet data and the decay), `Ψ` is `C^∞` on the open quadrant, and the shifted
unknown `Ψ + Gsing α g · sin 2θ` is a datum of the weak hypothesis class of the `ℋ^4`
elliptic estimate, with the orthogonalised source `orthSource g`.

This is the definition of `Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean` (namespace
`Work.FTS.ScratchC46`), copied verbatim into the namespace of the area. -/
def EllClassO (α : ℝ) (g Ψ : Fn) : Prop :=
  Work.Elliptic.IsBslSol α g Ψ ∧ Work.FTS.EllipticEst.SmoothOpen Ψ ∧
  Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
    (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ))

/-- **The shifted unknown** `Ψ ↦ Ψ + Gsing α g · sin 2θ` of §'The singular term'.

`shiftSing α g Ψ` is the quantity that the `ℋ^k` estimates of the paper are applied to: it is
`Ψ` plus the radial multiple of `sin 2θ` that removes the non-orthogonal part of the source.  It
is the third component of `EllClassO`. -/
def shiftSing (α : ℝ) (g Ψ : Fn) : Fn :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)

@[simp] theorem shiftSing_apply (α : ℝ) (g Ψ : Fn) (z θ : ℝ) :
    shiftSing α g Ψ z θ = Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- `shiftSing α g` is (definitionally) the function written out in `EllClassO`. -/
theorem shiftSing_eq (α : ℝ) (g Ψ : Fn) :
    shiftSing α g Ψ = fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- The second component of `EllClassO`. -/
theorem EllClassO.smoothOpen {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := h.2.1

/-- The third component of `EllClassO`, stated with the named shifting map. -/
theorem EllClassO.weakPos {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) (shiftSing α g Ψ) :=
  h.2.2

/-- The first component of `EllClassO`. -/
theorem EllClassO.isBslSol {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Elliptic.IsBslSol α g Ψ := h.1

/-- The equation clause of an `EllClassO` element, on the open quadrant. -/
theorem EllClassO.eq {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = g z θ :=
  h.1.1

/-- The two Dirichlet values of an `EllClassO` element. -/
theorem EllClassO.vanish {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Spaces.VanishTheta Ψ := ⟨h.1.2.1, h.1.2.2.1⟩

/-- The decay clause of an `EllClassO` element. -/
theorem EllClassO.decay {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (𝓝 0) := h.1.2.2.2

/-- **The three components of `EllClassO`, unpacked for the consumer.** -/
theorem ellClassO_iff (α : ℝ) (g Ψ : Fn) :
    EllClassO α g Ψ ↔
      (Work.Elliptic.IsBslSol α g Ψ ∧ Work.FTS.EllipticEst.SmoothOpen Ψ ∧
        Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
          (shiftSing α g Ψ)) := Iff.rfl

end Work.FTS.EllExist
