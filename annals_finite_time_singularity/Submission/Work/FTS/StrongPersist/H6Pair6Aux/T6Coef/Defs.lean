/-
# `H6Pair6Aux/T6Coef/Defs.lean` — the `CoefData`/`DatData` vocabulary of the level-six
coefficient rows

The `N`-row of the level-six pairing (`H6Pair6Aux/row_N_pair.lean`) decomposes into pieces
`A · P` where `A` is a *coefficient field* (the perturbed residual `Rop/Uop/Vop(PhiTil α f (E f))`,
a star field, or an angular moment `FK f`) and `P ∈ {f, ∂_θf, D_zf, F_*, ∂_θF_*, D_zF_*}`.

Each such piece is paired against the datum `f` itself, and the level-six pairing is a sum of
slot pairings `∫∫ ρ (D_z^bD_θ^a (A·P)) (D_z^bD_θ^a f)` (`TransportS.ip4_unfold_bound`).  The
per-slot rows therefore need exactly two kinds of data:

* on the coefficient `A` — smoothness on the open quadrant, `ℋ⁴`- and `ℋ⁶`-membership with the
  *norms* controlled (the `EllPkgGo`/`EllPkgK` pricing, and the pointwise pricing of
  `row_N_resid_pt`), see `CoefData`;
* on the datum `f` — the honest open-quadrant class with the angular vanishing, see `DatData`.

## Why the *norms* and not a `𝒲^{6,∞}`-bound

The level-six `𝒲^{6,∞}`-pricing of the coefficient slot is **not** usable: the per-summand
estimate `T6Gen.summand_le_mismatch` was refuted
(`T6Gen/NOTES_summand_le_mismatch_FALSE.md`) — with only `WlInf α 6 A ≤ K` the sharp
derivability bound `|D_θA| ≤ 1000K(α+s)s^{α/5}` loses more than the `ℋ⁶`-norm of the datum can
pay, at the single index quadruple `(a,b,b₁) = (1,5,0)`, for `α < 1/30`.  The rows below
therefore price the coefficient slots by their **`L²`-norms** (`∫∫ρ (slot A)² ≤ |A|²_{ℋ^k}`,
`intSlotLeHkSq`), which is exactly the Cauchy–Schwarz-optimal price and carries no divergence;
the pointwise price `K0` is used only for the *order-zero* slot.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The data of a coefficient field `A` available for the level-six rows.**

`K0` prices the field itself pointwise on the open quadrant (for the perturbation residual this
is `row_N_resid_pt`; for a star field `StarPkg6`; for `FK f` its explicit bound), `K4` prices its
`ℋ⁴`-norm (`Xn α A`, from `EllPkgGo`) and `K6` its `ℋ⁶`-norm (from `EllPkgK α 6`). -/
structure CoefData (α : ℝ) (A : Fn) (K0 K4 K6 : ℝ) : Prop where
  /-- interior smoothness on the open quadrant. -/
  sm : Work.FTS.EllipticEst.SmoothOpen A
  /-- `ℋ⁴`-honesty. -/
  h4 : Work.Spaces.HkMem α 4 A
  /-- `ℋ⁶`-honesty. -/
  h6 : Work.Spaces.HkMem α 6 A
  /-- the pointwise pricing on the open quadrant. -/
  val : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0
  /-- the `ℋ⁴`-pricing. -/
  n4 : Work.FTS.Nonlin.Xn α A ≤ K4
  /-- the `ℋ⁶`-pricing. -/
  n6 : Work.Spaces.HkNorm α 6 A ≤ K6

/-- **The data of the datum `f`** for the level-six rows: the slice class `H6Adm` (honest `ℋ⁶`
with the angular/axis vanishing), order-seven honesty (needed by the transport lemmas), and the
a-priori `ℋ⁴`-bound `Xn α f ≤ M`. -/
structure DatData (α : ℝ) (f : Fn) (M : ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen f
  h6 : Work.Spaces.HkMem α 6 f
  h7 : Work.Spaces.HkMem α 7 f
  vanish : Work.Spaces.VanishTheta f
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  bdd : Work.FTS.Nonlin.Xn α f ≤ M

/-- The datum data of a slice in `L6Ctx`. -/
theorem datData_of_H6Adm {α M : ℝ} {f : Fn}
    (hreg : Work.FTS.StrongPersist.H6Adm α f) (h7 : Work.Spaces.HkMem α 7 f)
    (hbdd : Work.FTS.Nonlin.Xn α f ≤ M) :
    DatData α f M :=
  ⟨hreg.reg.1, hreg.reg.2, h7, hreg.vanish, hreg.axis, hbdd⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
