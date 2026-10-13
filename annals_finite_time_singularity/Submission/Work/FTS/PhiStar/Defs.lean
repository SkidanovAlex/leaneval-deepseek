/-
# `Work.FTS.PhiStar` — the `Φ_*` node: vocabulary

This directory builds the paper's `Φ_*` (the stream function of the profile `F_*`) and the
package `VocabO.StarPkgo` around it, in the **open-quadrant** vocabulary frozen in
`Submission/Work/FTS/VocabO.lean` (`StarPkgo`, `WDp`, `WDMem`, `CoefTh`, `CoefThMem`)
and following the lead design recorded in `Submission/Work/FTS/ELL_H2_LEAD.md` §B4.

## The decomposition (§B4 of the lead design)

Let `φ(z) = 2z/(1+z)²` (`VocabO.phiR`, also `Work.FM.Fstar`) and

`Γ̄(θ) = Γ(θ)/c − (5/4) sin 2θ`   (`VocabO.GamBar`),

the angular part of `F_* = α (Γ/c) φ(z)` with the `sin 2θ`-moment **removed**: the identity
`∫_0^{π/2} sin 2θ · sin θ cos²θ dθ = 4/15` gives `∫ Γ̄ sin θ cos²θ = 0` (`GamBar_moment`,
proved in `Basic.lean`), so `Γ̄` is orthogonal to the kernel of the adjoint of `L₀` and the
Dirichlet problem `L₀ ψ = Γ̄` is solvable (`Psi0_exists`).

The design writes `Φ_*` as three explicitly separated pieces:

1. `Gz(z) · sin 2θ`, where `Gz` is the *decaying* solution of the Euler equation
   `−(α²z²Gz'') − α(5+α)z Gz' = (5α/4)φ`  (`GzOde`) — this is the paper's explicit `G`
   (tex 1179–1190); its `𝒲^{4,∞}`-size is `O(α)` (`PhiStarE/Gbar_wiln`).
2. `α · φ(z) · ψ(θ)`, the *separable leading term*, where `ψ` solves the explicit 1-D
   angular model `L₀ψ = Γ̄`, `ψ(0) = ψ(π/2) = 0`, `∫ψ sin θ cos²θ = 0` (`AngModel`,
   existence in `Psi0_exists`).
3. a remainder `R` solving `bslOp α R = α²·(𝒜φ)(z)·ψ(θ)` (`RemSource`), i.e. an `O(α²)`
   separable source; `𝒜 = αz²∂_zz + (5+α)z∂_z` is `VocabO.phiA`.

The telescoping identity that makes this work is `phiStar_remainder_source` (P2):

`bslOp α (Gz · sin 2θ + α φ ψ) = F_* − α² (𝒜φ) ψ`   on the open quadrant,

so that `Φ_* := Gz sin 2θ + α φ ψ + R` solves `bslOp α Φ_* = F_*`.

## What is in this directory

* `Defs.lean` (this file): `GzOde`, `AngModel`, `Model`, `RemSource`, `GzProfile`,
  `ThetaProfile`, `Aprof`, `PhiTilExpansion`, `StarSplit`.
* `Basic.lean`: the elementary API — `GamBar_moment`, the explicit value of `F_*`, the
  structural decomposition of `bslOp` on separable products (`bslOp_sep`, `bslOp_radial`),
  additivity of `bslOp`, and `IsBslSol_of_pieces`.
* `Gz.lean`: the explicit radial profile `GzProfile` satisfies `GzOde` and its `𝒲`-bounds.
* `Psi0.lean`: the statement `Psi0_exists` (P1).
* `RemSource.lean`: the statement `phiStar_remainder_source` (P2).
* `Exist.lean`: the elliptic existence theorem in the weak class (shared with `EllSol`).
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two model equations -/

/-- **The radial model equation.**  `Gz` is the decaying solution of the Euler-type equation

`−(α²z²Gz'') − α(5+α) z Gz' = (5α/4)·φ(z)`,   `φ = VocabO.phiR`,

i.e. `bslOp α (Gz · sin 2θ) = (5α/4)φ·sin 2θ` on the quadrant (the `θ`-operator `L₀` kills
`sin 2θ`).  The explicit solution is `GzProfile` (`Gz.lean`), which is the paper's `G`.
Note the sign convention: with `Gsing α F` the elliptic section's singular term (solving
`α²z²G'' + α(5+α)zG' = (15/4)F_*`), one has `GzProfile α = −Gsing α (Construction.Fstar α)`. -/
def GzOde (α : ℝ) (Gz : ℝ → ℝ) : Prop :=
  ∀ z, 0 < z →
    -(α ^ 2 * z ^ 2 * iteratedDeriv 2 Gz z) - α * (5 + α) * z * deriv Gz z
      = (5 * α / 4) * Work.FTS.VocabO.phiR z

/-- **The angular model.**  `ψ` solves the explicit 1-D problem `L₀ψ = Γ̄` on `(0,π/2)` with
Dirichlet data at both endpoints, the moment normalisation `∫ψ sinθcos²θ = 0` (which pins down
the free additive multiple of `sin 2θ ∈ ker L₀`), and is smooth on the open interval.

The existence statement is `Psi0_exists` (`Psi0.lean`).  The moment condition is what makes the
source `α²φψ` of the remainder have vanishing `F_*`-moment, as required by the weak-class
elliptic estimates (`TT.EllWeakPos`). -/
structure AngModel (α : ℝ) (ψ : ℝ → ℝ) : Prop where
  /-- smooth on the open angular interval -/
  smooth : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioo 0 (π / 2))
  /-- continuous up to the endpoints -/
  cont : ContinuousOn ψ (Set.Icc 0 (π / 2))
  /-- left Dirichlet value -/
  bdry0 : ψ 0 = 0
  /-- right Dirichlet value -/
  bdry1 : ψ (π / 2) = 0
  /-- the model equation -/
  eq : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ
  /-- the moment normalisation -/
  moment : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0

/-! ## The decomposition of `Φ_*` -/

/-- The **two-term model** `Gz(z)·sin 2θ + α·φ(z)·ψ(θ)`: the part of `Φ_*` whose
`bslOp`-image is `F_* − α²(𝒜φ)ψ` (`phiStar_remainder_source`). -/
def Model (α : ℝ) (Gz ψ : ℝ → ℝ) : Fn :=
  fun z θ => Gz z * Real.sin (2 * θ) + α * Work.FTS.VocabO.phiR z * ψ θ

/-- The **remainder source** `α²·(𝒜φ)(z)·ψ(θ)`: the `O(α²)` separable source left after the
telescoping.  It is orthogonal to `sin θ cos²θ` at every `z` (by `AngModel.moment`), so the
weak-class elliptic estimates apply to it. -/
def RemSource (α : ℝ) (ψ : ℝ → ℝ) : Fn :=
  fun z θ => α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ

/-- The paper's profile `φ = 2z/(1+z)²` is `Work.FM.Fstar`; the source of the remainder is
`O(α²)` and separable. -/
theorem RemSource_apply (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    RemSource α ψ z θ = α ^ 2 * (α * z ^ 2 * iteratedDeriv 2 Work.FM.Fstar z
      + (5 + α) * z * deriv Work.FM.Fstar z) * ψ θ := rfl

/-! ## The explicit radial profile and the residual splitting -/

/-- **The explicit radial profile** `Gz = −Gsing α (F_*)`, the decaying solution of `GzOde`
(the paper's explicit `G`).  Its `𝒲`-size is `O(α)` (`Gz.lean`). -/
def GzProfile (α : ℝ) : ℝ → ℝ := fun z => -(Work.Elliptic.Gsing α (Work.Construction.Fstar α) z)

/-- The radial factor of the singular part `Θ = (1/4α) sin 2θ L₁₂(F_*)`: one has
`Θ(z,θ) = ThetaProfile z · sin 2θ`. -/
def ThetaProfile : ℝ → ℝ := fun z => 1 / (2 * (1 + z))

/-- The **flat radial factor of `Φ̃_* = Φ_* − Θ`**:  writing
`Φ_* = Gz(z) sin 2θ + α φ(z) ψ(θ) + R`, one has

`Φ̃_* = Aprof α(z)·sin 2θ + α φ(z) ψ(θ) + R`,   `Aprof α = GzProfile α − 1/(2(1+z))`,

and `Aprof α = −Gbar α (F_*)` is of size `O(α)` in `𝒲^{4,∞}`. -/
def Aprof (α : ℝ) : ℝ → ℝ := fun z => GzProfile α z - ThetaProfile z

/-- The explicit expansion of `Φ̃_*` used by the sup-estimates: the flat part, the separable
model part and the remainder. -/
def PhiTilExpansion (α : ℝ) (ψ : ℝ → ℝ) (R : Fn) : Fn :=
  fun z θ => Aprof α z * Real.sin (2 * θ) + α * Work.FTS.VocabO.phiR z * ψ θ + R z θ

/-- `Φ_*` is presented as `Model + R` with `Gz` solving the radial model, `ψ` the angular
model and `R` solving the `O(α²)` remainder equation.  This is the interface consumed by the
sup-estimate nodes; `Uop`, `Vop`, `Rop` of `Φ̃_*` are then read off from `PhiTilExpansion`. -/
structure StarSplit (α : ℝ) (Φs : Fn) (Gz ψ : ℝ → ℝ) (R : Fn) : Prop where
  hα : 0 < α
  gz : GzOde α Gz
  ang : AngModel α ψ
  decomp : Φs = fun z θ => Model α Gz ψ z θ + R z θ
  rem_eq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
    Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ
  rem_smooth : Work.FTS.EllipticEst.SmoothOpen R
  rem_dir0 : ∀ z, R z 0 = 0
  rem_dir1 : ∀ z, R z (π / 2) = 0
  rem_decay : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)
  rem_mom : ∀ z, 0 < z → Work.Elliptic.Fstar R z = 0

end Work.FTS.PhiStar
