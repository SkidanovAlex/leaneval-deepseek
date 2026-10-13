/-
# `Submission/Work/FTS/LocData6/` — order-`6` data for the strong-solution route

This chapter is the **order-`6` extension of the localised-data node** of the route
(`Submission/Work/FTS/LocData/` = node **N9**, `Submission/Work/FTS/LocDataExt/` = the order-`4`
and order-`5` extension **N9-ext**).  It exists because the strong-solution route of the lead
(`Submission/Work/FTS/FTS_STRONG_ROUTE.md`, items S1/S5) consumes its datum in the class
`Work.FTS.Nonlin.GalClass α g`, whose `reg` field is

  `Work.FTS.Nonlin.RegQ α 6 g = SmoothQuad g ∧ HkMem α 6 g ∧ BdryTraces α 6 g`,

and the local-existence theorem `Work.FTS.StrongGlobal.LWPStrong α Φs EllSol α₀ K δ` is stated
for data with `RegQ α 6 g₀` and `Xn₆(g₀) ≤ K·α²`.  The delivered chapters give the localised
datum `locG α L β (hLoc α)` only at orders `4` and `5`
(`Work.FTS.LocDataExt.regQ_locG5_uncond`, `galData_exists_both`).

**The deliverable of this chapter** is the order-`6` analogue, at the *same* parameters
(`0 < α ≤ 1`, `L ≥ 1`, the bump `hLoc α`, N9's normalising scalar `β`):

* `Work.FTS.LocData6.regQ_locG6_uncond` — `RegQ α 6 (locG α L β (hLoc α))` for every `β`;
* `Work.FTS.LocData6.locG6_data` — for every `K > 0` there is `L₀` such that for every `L ≥ L₀`
  there is `β` with `|β| ≤ K α²`, `DataAdm α (·)`, `RegQ α 6 (·)`, `GalClass α (·)`,
  `L₁₂(·)(0) = 0`, `Xn α (·) ≤ α²` **and** `Xn₆ (·) ≤ K α²` — exactly the datum hypotheses of
  `Work.FTS.StrongGlobal.global_strong` (its `hData`, `hXn4₀` and `hXn6₀`).

Nothing here re-proves the order-`4`/order-`5` material: it is *imported* from
`Submission.Work.FTS.LocDataExt.Final`.  What is new is the order-`6` chain of estimates:

| order-`6` input | statement | module |
|---|---|---|
| angular jet of `Γ` | `\|D_θ^iΓ\| ≤ 10⁵Γ`, `i ≤ 6` | `LocData6.AngJet6` |
| cut-off jets of `1 - χ(·/L)` | uniformly bounded in `L`, `c ≤ 6` | `LocData6.CutJet6` |
| profile jets of `FM.Fstar` | `\|D_z^jφ\| ≤ C/z`, `j ≤ 6` | `LocData6.ProfJet6` |
| far-factor jets of `zfarR L` | `\|D_z^j zfarR L\| ≤ A/z` on `[L,2L]` | `LocData6.ZfarJet6` |
| bump majorant | `HkIntegrand α 6 (hLoc α) ≤ K angMaj/(1+z)²` | `LocData6.HLocMaj6` |
| far part in `ℋ⁶` | `HkSq α 6 (zfar L F_*) ≤ Cα/L` | `LocData6.ZfarSq6` |
| decay | `DecayAll 6 (locG α L β (hLoc α))` | `LocData6.Decay6` |

All of it rests on `[propext, Classical.choice, Quot.sound]` only.

## The vocabulary of this chapter

* `Fn = ℝ → ℝ → ℝ` (curried functions of the self-similar variables `(z,θ)`);
* `Xn6 α g = |g|_{ℋ⁶} = Work.Spaces.HkNorm α 6 g` (the `X n` of `StrongGlobal.Defs` is the
  order-`4` `Work.FTS.Nonlin.Xn`);
* `locG6 α L β = locG α L β (hLoc α)` — the localised perturbation at the concrete bump, so
  that the statements below read at the parameters of N9.

Everything else (the weights, `SmoothQuad`, `HkMem`, `HkSq`, `RegQ`, `GalClass`, `BdryTraces`,
`locG`, `hLoc`, `angMaj`, `zfarR`, `locR`) keeps its frozen meaning.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS.LocDataExt.Traces
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.LocData.Main
import Submission.Work.FTS.Vocab
import Submission.Work.Stability.HkSqZfar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false

/-- Functions of the self-similar variables `(z,θ)`, curried. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-- The `ℋ⁶`-size `Xn₆(g) = |g|_{ℋ⁶} = Work.Spaces.HkNorm α 6 g` — the order-`6` companion of
the frozen `Work.FTS.Nonlin.Xn α g = |g|_{ℋ⁴}`. -/
abbrev Xn6 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 6 g

/-- The localised perturbation `g = locData α L β (hLoc α) - F_*` at the concrete bump of N9 —
the datum of the strong-solution route, abbreviated so that the statements of this chapter read
at the parameters of `LocData`. -/
abbrev locG6 (α L β : ℝ) : Fn := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)

theorem locG6_eq (α L β : ℝ) :
    locG6 α L β = Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α) := rfl

end Work.FTS.LocData6
