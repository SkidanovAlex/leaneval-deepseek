/-
# `Npair6Aux/Defs.lean` — the vocabulary of the `N`-row (`Npair6`)

Target (my task): `Submission/Work/FTS/StrongPersist/H6Rows/Npair6.lean`,

```
theorem Npair6 : ∀ Ce, 0 < Ce → ∃ K α₂, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
  ∀ α ∈ Ioc 0 α₂, ∀ (g Φ : Fam) (τ M Cs) (E : Fn → Fn) (Φs : Fn), 0 ≤ τ →
    L6Ctx (IP6 1…1) α M Ce Cs E Φs g Φ τ →
    HkMem α 6 (N α (Ftau α g τ) (slice Φ τ)) ∧
    |IP6 1…1 α (N α (Ftau α g τ) (slice Φ τ)) (slice g τ)|
      ≤ K * (1+|Ce|+|Cs|)^4 * α^{-10} * (1+M)^4 * (1 + Sq6 α (slice g τ))
```

## The route (see `NOTES_Npair6.md` for the analysis)

Write `f := slice g τ`, `F := Ftau α g τ = F_* + f`, `Ψ := slice Φ τ`, and
`Ξ := PhiTil α F Ψ = PhiTs α Φs + PhiTil α f (E f) =: Ξ₁ + Ξ₂` (using `Ell6Ctx.hsum`).
The eight pieces of `N` are

```
2 Rop(Ξ) F,  -2 Uop(Ξ) pth F,  -2α Vop(Ξ) Dz F,  -(1/2) s2 (FK F) pth F,  -sin²θ (FK F) F.
```

Every piece is of the form `coefficient × f-slot`, with
`f-slot ∈ {F, pth F, Dz F} = {F_* or f, pth F_* or pth f, Dz F_* or Dz f}`.

* the pieces whose second factor is one of `F_*, pth F_*, Dz F_*`, or whose coefficient
  is a *star* field (`Ξ₁`), are handled by the **product rules** `wprod6`
  (`𝒲^{6,∞}`-priced) and `N6_prod` (`ℋ⁶`) followed by Cauchy–Schwarz `IP6_cs_coeffs`;
  those give *linear* bounds in `Xn6 f`, hence quadratic after Cauchy–Schwarz;
* the pieces `coefficient × f` with the *perturbed* coefficient (`Rop(Ξ₂)`, `Uop(Ξ₂)/s2`,
  `Vop(Ξ₂)`), and the pieces whose coefficient is an angular moment of `f` (`FK f`), need a
  *slot-level* estimate, because the product rules do not apply (`D_z f` has unbounded
  `ℋ⁶`-norm, and the perturbed residual is not `𝒲^{6,∞}`-priced).

`CoefHyp` below records exactly the data available in `L6Ctx` for the perturbed residual:

* `val`  is the pointwise pricing (the `hres_pt` field of `Ell6Ctx`, or `hgo` + Agmon);
* `n4`   is the `ℋ⁴`-pricing (`Ell6Ctx.hgo : EllPkgGo α Ce f (E f)`);
* `n6`   is the `ℋ⁶`-pricing (`Ell6Ctx.hell : EllPkgK α 6 Ce f (E f)`).

The three row lemmas (`rowMul`, `rowDth`, `rowDz` in the sibling files) are the per-slot
estimates; everything else is bookkeeping.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The data of a coefficient available in `L6Ctx`.**

* `K0` prices the sup of the coefficient (the `hres_pt` field of `Ell6Ctx`, or the
  `WlInf`-pricing of a star field);
* `K4` prices its `ℋ⁴`-norm (the `EllPkgGo` field `hgo` of `Ell6Ctx`);
* `K6` prices its `ℋ⁶`-norm (the `EllPkgK α 6` field `hell` of `Ell6Ctx`).

The rows derive from `h4`/`n4` the pointwise bounds of the coefficient's slots of order ≤ 2
(`sup_dz_le_hk`, `mixed_pointwise_le_Xn`, both with `Xn α A = HkNorm α 4 A ≤ K4`), and from
`h6`/`n6` the `L²(ρ)`-bounds of its slots of order ≤ 6 (`intSlotLeHkSq`). -/
structure CoefHyp (α : ℝ) (A : Fn) (K0 K4 K6 : ℝ) : Prop where
  /-- interior smoothness. -/
  sm : Work.FTS.EllipticEst.SmoothOpen A
  /-- `ℋ⁴`-honesty. -/
  h4 : Work.Spaces.HkMem α 4 A
  /-- `ℋ⁶`-honesty. -/
  h6 : Work.Spaces.HkMem α 6 A
  /-- the pointwise pricing. -/
  val : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0
  /-- the `ℋ⁴`-pricing. -/
  n4 : Work.FTS.Nonlin.Xn α A ≤ K4
  /-- the `ℋ⁶`-pricing. -/
  n6 : Work.Spaces.HkNorm α 6 A ≤ K6

/-- The `f`-side data of a slot row: the datum `f` is honest in `ℋ⁶`, its `ℋ⁴`-norm is
bounded by `M`, and it vanishes on the two angular boundary lines and (with its first radial
derivative) at the axis — the class `H6Adm` of the slices. -/
structure DatHyp (α : ℝ) (f : Fn) (M : ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen f
  h6 : Work.Spaces.HkMem α 6 f
  h7 : Work.Spaces.HkMem α 7 f
  vanish : Work.Spaces.VanishTheta f
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  bdd : Work.FTS.Nonlin.Xn α f ≤ M

end Work.FTS.StrongPersist.H6Rows.Npair6Aux
