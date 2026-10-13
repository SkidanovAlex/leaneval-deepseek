/-
# The algebra of the counterexample to `Work.FTS.EllSol.PkgK5.ropTransferK5`

`Work.FTS.EllSol.PkgK5.ropTransferK5` (and its siblings `uopTransferK5`, `vopTransferK5`) is
**false**: its hypotheses do not control the `sin 2θ`-mode of the *source* `g`.  This file
records the two algebraic facts on which the witness family rests (see
`NOTES_ropTransferK5.md` for the full analysis):

* `rop_radial_sin` — for **any** radial profile `Λ`, the `sin 2θ`-direction of `Rop` is purely
  radial:  `ℛ(Λ(z)·sin 2θ) = 2Λ + 2·(α D_zΛ)·sin²θ`.  Hence `ℛ` of the singular layer
  `-Ḡ·sin 2θ` is `2Ḡ(5sin²θ-1) + (3/2)F_*(g)·sin²θ` (using the definitional relation
  `α D_z Ḡ = -5Ḡ - (3/4)·F_*(g)`, which is the ODE `Work.Elliptic.Gsing_ode`); the second
  summand is the *source* mode `F_*(g)`, on which the hypotheses put no `ℋᵏ`-control beyond
  `ClassC.mem : HkMem α 7 g`.
* `ellResid_witness` — for `Φg := -Gsing α g · sin 2θ` the residual of Theorem `RemovingL12`
  is *exactly* the singular layer: `EllResid α g Φg = -Ḡ(α,g)·sin 2θ` (no hypothesis used;
  `Construction.PhiTil = Elliptic.EllResid` definitionally).

Together with the tree's `Work.Elliptic.bslOp_sinG`, `Work.Elliptic.Gsing_ode` and the two
identities `Fstar (lm·sin 2θ) = (4/15)·lm`, `orthSource (lm·sin 2θ) = 0`
(`Submission/Work/FTS/EllSol/PkgK5/_probe_cex.lean`), they show that for
`g = lm·sin 2θ`, `Φg = -Gsing α g·sin 2θ`:

* `IsBslSolPos α g Φg` holds (`bslOp α Φg = (15/4)F_*(g) sin 2θ = lm·sin 2θ = g`),
* `ellShift α g Φg = 0` and `orthSource g = 0`, so the three remaining hypotheses reduce to the
  proved statements `ellWeakPos_zero` / `HkMem_zero`,
* while `ℛ(PhiTil α g Φg) = 2Ḡ(5sin²θ-1) + (2/5)·lm·sin²θ` needs `D_z^k lm ∈ L²(w²)`, which
  `ClassC.mem` (`HkMem α 7 g`) supplies only for `k ≤ 7`: with `lm = ψ·z^{-8}cos z`
  (`D_z^8 lm = cos z + O(z^{-1})`) the first conjunct of the conclusion fails at `k = 8`.

Everything in this file is `sorry`-free.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.CexAlgebra

set_option autoImplicit false

/-- **The `sin 2θ`-direction of `ℛ` is purely radial**: for every radial `Λ`,
`ℛ(Λ(z)·sin 2θ) = 2Λ(z) + 2·(α z ∂_zΛ(z))·sin²θ` on the open quadrant. -/
theorem rop_radial_sin (α : ℝ) (Λ : ℝ → ℝ) (z θ : ℝ) (hΛ : DifferentiableAt ℝ Λ z)
    (hcos : Real.cos θ ≠ 0) :
    Work.Construction.Rop α (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = 2 * Λ z + 2 * (α * (z * deriv Λ z)) * Real.sin θ ^ 2 := by
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hcos2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hpz : Work.Spaces.pz (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = deriv Λ z * Real.sin (2 * θ) := by
    have h := hΛ.hasDerivAt.mul_const (Real.sin (2 * θ))
    simpa [Work.Spaces.pz] using h.deriv
  have hpth : Work.Spaces.pth (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = Λ z * (2 * Real.cos (2 * θ)) := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h := h1.sin
      simpa [mul_comm] using h
    have h3 : HasDerivAt (fun θ' : ℝ => Λ z * Real.sin (2 * θ')) (Λ z * (2 * Real.cos (2 * θ))) θ :=
      h2.const_mul (Λ z)
    simpa [Work.Spaces.pth] using h3.deriv
  have htrig : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hmain : (2 * Real.sin θ * (Λ z * Real.sin (2 * θ))
        + α * Real.sin θ * z * (deriv Λ z * Real.sin (2 * θ))
        + Real.cos θ * (Λ z * (2 * Real.cos (2 * θ))))
      = (2 * Λ z + 2 * (α * (z * deriv Λ z)) * Real.sin θ ^ 2) * Real.cos θ := by
    rw [hsin2, hcos2]
    linear_combination (4 * Λ z * Real.cos θ) * htrig
  rw [Work.Construction.Rop, hpz, hpth]
  exact (div_eq_iff hcos).mpr hmain

/-- **The residual of Theorem `RemovingL12` for the witness is exactly the singular layer**:
for `Φg := -Gsing α g·sin 2θ` one has `EllResid α g Φg = -Ḡ(α,g)·sin 2θ`, definitionally. -/
theorem ellResid_witness (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α g (fun z θ => -(Work.Elliptic.Gsing α g z) * Real.sin (2 * θ))
      = fun z θ => -(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ) := by
  funext z θ
  simp only [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

/-- The assertion of the target in `Elliptic`-vocabulary: `PhiTil` of the witness is the
singular layer (`Construction.PhiTil = Elliptic.EllResid`, `Construction.L12 = Elliptic.L12`,
`Construction.s2 = sin (2·)`, all definitional). -/
theorem phiTil_witness (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Construction.PhiTil α g (fun z θ => -(Work.Elliptic.Gsing α g z) * Real.sin (2 * θ))
      = fun z θ => -(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ) := by
  have h := ellResid_witness α g
  funext z θ
  rw [show Work.Construction.PhiTil α g
        (fun z θ => -(Work.Elliptic.Gsing α g z) * Real.sin (2 * θ))
      = Work.Elliptic.EllResid α g
        (fun z θ => -(Work.Elliptic.Gsing α g z) * Real.sin (2 * θ)) from rfl]
  exact congrFun (congrFun h z) θ

end Work.FTS.EllSol.PkgK5.CexAlgebra
