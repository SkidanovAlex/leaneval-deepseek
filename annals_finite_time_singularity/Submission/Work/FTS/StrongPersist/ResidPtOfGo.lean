/-
# `Work.FTS.StrongPersist.ResidPtOfGo` — the pointwise pricing of the perturbation residual

The obstruction found by the `H6Pair6` audit (`H6Pair6Aux/NOTES_resid_pointwise.md`) is that
`EllPkgK α 6` prices the three residual components `Rop(Φ̃_f)`, `Uop(Φ̃_f)/sin 2θ`, `Vop(Φ̃_f)`
**only through the `ℋ⁶`-norm**, and `HkNorm α 6 f` is unbounded on the class
`{H6Adm α f ∧ HkNorm α 4 f ≤ M}` — a crude Agmon bound then gives a term *cubic* in `Xn6 f`,
against `H6Pair`'s quadratic right-hand side.

The lead's ruling (17:10) is that the data needed is already available: `ExistsEllSolC`'s first
conjunct is the **level-four** elliptic package `Work.FTS.VocabO.EllPkgGo α Ce f (E f)`, which
prices the same three fields by `Ce·HkNorm α 4 f ≤ Ce·M`.  This module performs the one bridge
from that package to the pointwise form the rows consume:

```
ResidPtOfGo : |Rop(Φ̃_f)|, |Uop(Φ̃_f)/sin 2θ|, |Vop(Φ̃_f)| ≤ K α^{-1/2} Ce HkNorm α 4 f   on Q0,
```

by the open-quadrant Agmon bound `SupOpenH2` (`|h z θ| ≤ C α^{-1/2} HkNorm α 2 h` for
`HQo α 2 h`) together with the two monotonicities `HkNorm α 2 ≤ HkNorm α 4` and
`HkMem α 4 ⟹ HkMem α 2` (the latter for `SmoothOpen` data).  Everything rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongLWP.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The pointwise pricing of the perturbation residual from the level-four elliptic package.**
From `EllPkgGo α Ce f Ψ` (the first conjunct of `ExistsEllSolC`) and the open-quadrant Agmon bound
`SupOpenH2`, the three transported-residual components of `Φ̃_f = PhiTil α f Ψ` are dominated
*pointwise* on the open quadrant by `K α^{-1/2} Ce HkNorm α 4 f` — the `ℋ⁴`-pricing that the
level-six rows of `H6Pair` consume (and, through `HkNorm α 4 f ≤ M`, the `M`-pricing of
`H6Pair`'s right-hand side). -/
theorem ResidPtOfGo : ∃ K : ℝ, 0 < K ∧ ∀ (α Ce : ℝ), 0 < α → α ≤ 1 → 0 ≤ Ce →
    ∀ f Ψ : Fn, Work.FTS.VocabO.EllPkgGo α Ce f Ψ →
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      (|Work.Construction.Rop α (Work.Construction.PhiTil α f Ψ) z θ|
          ≤ K * α ^ (-(1 / 2 : ℝ)) * Ce * HkNorm α 4 f ∧
        |Work.Construction.Uop α (Work.Construction.PhiTil α f Ψ) z θ
            / Work.Construction.s2 θ| ≤ K * α ^ (-(1 / 2 : ℝ)) * Ce * HkNorm α 4 f ∧
        |Work.Construction.Vop (Work.Construction.PhiTil α f Ψ) z θ|
          ≤ K * α ^ (-(1 / 2 : ℝ)) * Ce * HkNorm α 4 f) := by
  obtain ⟨C, hC, hsup⟩ := SupOpenH2
  refine ⟨C, hC, ?_⟩
  intro α Ce hα hα1 hCe f Ψ hgo z θ hzθ
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCf : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hC.le hr
  -- the single residual estimate
  have key : ∀ {g : Fn}, Work.FTS.VocabO.HQo α 4 g →
      Work.FTS.Nonlin.Xn α g ≤ Ce * Work.FTS.Nonlin.Xn α f →
      |g z θ| ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * HkNorm α 4 f := by
    intro g hQ4 hb
    obtain ⟨hsm, hm4⟩ := hQ4
    have hm2 : HkMem α 2 g := Work.FTS.OpenPkg.HkMem_mono_open hsm 2 (by norm_num) hm4
    have h1 : |g z θ| ≤ C * α ^ (-(1 / 2 : ℝ)) * HkNorm α 2 g :=
      hsup α hα hα1 g ⟨hsm, hm2⟩ z θ hzθ
    have h2 : HkNorm α 2 g ≤ HkNorm α 4 g :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hm4
    calc |g z θ| ≤ C * α ^ (-(1 / 2 : ℝ)) * HkNorm α 2 g := h1
      _ ≤ C * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 g := mul_le_mul_of_nonneg_left h2 hCf
      _ ≤ C * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul_of_nonneg_left hb hCf
      _ = C * α ^ (-(1 / 2 : ℝ)) * Ce * HkNorm α 4 f := by ring
  exact ⟨key hgo.R.1 hgo.R.2, key hgo.U.1 hgo.U.2, key hgo.V.1 hgo.V.2⟩

end Work.FTS.StrongPersist
