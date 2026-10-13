import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The bundle of open-quadrant facts about the difference `W₁ - W₂` of two `ClassC` profiles**
that the nine per-piece bounds of the `N₀`-difference consume.

Everything is stated for the difference `h = W₁ - W₂` (written out, so that the record can be
built without a `let`), and every field is a `SmoothOpen`-, `HkMem`- or `Xn`-statement about `h`
or about one of the two `D_θ`/`D_z`-derived fields `Dth W₂`, `Dz W₂` of the second profile. -/
structure ClassCDiffFacts (α : ℝ) (W₁ W₂ : Fn) : Prop where
  /-- `h = W₁ - W₂` is `C^∞` on the open quadrant -/
  hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => W₁ z θ - W₂ z θ)
  /-- honesty of the `ℋ⁵`-integrand of `h` (used to reach `D_θh`, `D_zh`) -/
  hmem : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ)
  /-- the `ℋ⁴`-size of `h` is controlled by its `ℋ⁵`-size -/
  hXh : Work.FTS.Nonlin.Xn α (fun z θ => W₁ z θ - W₂ z θ)
    ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
  /-- smoothness of `D_θh` -/
  hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ))
  /-- honesty of the `ℋ⁴`-integrand of `D_θh` -/
  hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ))
  /-- the `ℋ⁴`-size of `D_θh` is controlled by the `ℋ⁵`-size of `h` -/
  hDthXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ))
    ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
  /-- smoothness of `D_zh` -/
  hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ))
  /-- honesty of the `ℋ⁴`-integrand of `D_zh` -/
  hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ))
  /-- the `ℋ⁴`-size of `D_zh` is controlled by the `ℋ⁵`-size of `h` -/
  hDzXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ))
    ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
  /-- smoothness of the radial function `z ↦ L₁₂(h)(z)` -/
  hLhSm : Work.FTS.EllipticEst.SmoothOpen
    (fun z _ => Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) z)
  /-- the zero mode of `L₁₂(h)` vanishes -/
  hLh0 : Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) 0 = 0
  /-- smoothness of the radial function `z ↦ L₁₂(W₁)(z)` -/
  hLW₁Sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 W₁ z)
  /-- the `ℋ⁴`-size of `W₁` is controlled by its `ℋ⁵`-size -/
  hXW₁ : Work.FTS.Nonlin.Xn α W₁ ≤ Work.FTS.GalFields.Xn5 α W₁
  /-- the `ℋ⁴`-size of `W₂` is controlled by its `ℋ⁵`-size -/
  hXW₂ : Work.FTS.Nonlin.Xn α W₂ ≤ Work.FTS.GalFields.Xn5 α W₂
  /-- smoothness of `D_θW₂` -/
  hDthW₂Sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth W₂)
  /-- honesty of the `ℋ⁴`-integrand of `D_θW₂` -/
  hDthW₂Mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth W₂)
  /-- the `ℋ⁴`-size of `D_θW₂` is controlled by the `ℋ⁵`-size of `W₂` -/
  hDthW₂Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth W₂) ≤ Work.FTS.GalFields.Xn5 α W₂
  /-- smoothness of `D_zW₂` -/
  hDzW₂Sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz W₂)
  /-- honesty of the `ℋ⁴`-integrand of `D_zW₂` -/
  hDzW₂Mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W₂)
  /-- the `ℋ⁴`-size of `D_zW₂` is controlled by the `ℋ⁵`-size of `W₂` -/
  hDzW₂Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz W₂) ≤ Work.FTS.GalFields.Xn5 α W₂

end Work.FTS.StrongEps.EpsRLX
