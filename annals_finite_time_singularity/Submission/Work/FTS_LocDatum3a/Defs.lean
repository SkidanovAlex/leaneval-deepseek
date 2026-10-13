/-
# `Submission/Work/FTS_LocDatum3a/` — the `locG6` data lie in `EpsDatum` (Final core field 3a)

This chapter is the **producer of clause (3a)** of the strong-solution interface v2
(`Submission/Work/FTS/StrongEps/LEAD_strong_iface_v2.md`, edit **E24**; installed in
`Submission/Work/FTS/Final/Assembly.lean`, field `hDat` of `exists_blowupAt_of_data`):

> the localised order-`6` datum `locG6 α L β` of `Work.FTS.LocData6` lies in
> `Work.FTS.StrongEps.EpsDatum α ρ ε` for every `ε > 0`.

Recall the definitions of the interface (`Work.FTS.StrongEps.EpsODE`):

  `EpsDatum α ρ ε h = SmoothOpen h ∧ HkMem α 6 h ∧ ClassC α (J_ε h)`,

where

* `Work.FTS.EllipticEst.SmoothOpen h` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`;
* `Work.Spaces.HkMem α 6 h` is the honest `ℋ⁶`-membership of the profile;
* `Work.FTS.ClassC.ClassC α g` is the **elliptic source class** of
  `Submission/Work/FTS/ClassC/Defs.lean`: `normTh g = g`, `SmoothOpen g`, `HkMem α 7 g`,
  `HkMem α 8 g`, `BdryTraces α 6 g`, `BdryTraces α 7 g`, `∀ m, ContDiffOn ℝ m (F_* g) (0,∞)`,
  the axis condition `g(z,θ)/z → 0` and the vanishing of the `L₁₂`-zero-mode `L₁₂ g 0 = 0`;
* `J_ε = Work.FTS.StrongEps.Jeps ρ ε` is the log-coordinate mollifier of the `ε`-scheme
  (with `ρ` an `IsSmoothKernel`).

## What this chapter proves

The two easy conjuncts come straight from the interior-regularity class `RegQ α 6 (locG6 α L β)`
of the producer chapter `Submission/Work/FTS/LocData6/` (which is *unconditional* for `0 < α ≤ 1`,
`1 ≤ L`, every `β`): `SmoothQuad` refines to `SmoothOpen`, and `HkMem α 6` is the second field of
`RegQ`.

The third conjunct `ClassC α (J_ε (locG6 α L β))` is the real content.  The mollifier chapter
`Work.FTS.StrongEps.softClass_Jeps` (`MolClassC.lean`) already supplies, for any datum `f` with
`C^∞`-regularity on the open quadrant, the **five mollifier clauses** of the class:

  `norm` (`normTh_Jeps`), `reg` (`Jeps_contDiffOn`), `mem8` (`HkMem_Jeps` at level `8`),
  `tr7` (`BdryTraces_Jeps` at level `7`), `axis` (`axis_Jeps`),

under the datum-side hypotheses

  `∀ n, ContDiffOn ℝ n (uncurry f) Quad`, `HkMem α 8 f`, the uniform bound of `mixed b a f`
  (`a + b ≤ 7`), the four endpoint vanishing conditions `hz0/hzin/ht0/ht1` (`a + b ≤ 7`) and
  the axis condition `hax`; plus `LocallyIntegrable (logPull f)` for `reg`.

The two **non-mollifier** clauses of `ClassC` (`fsm`, `l12`) must come from the datum, and this
chapter produces them for the *concrete separable* datum

  `locG6 α L β = locR α L β(z) · Γ(θ)`   (`Work.FTS.LocDataExt.locG_locR_Gam`):

* `fsm`: `∀ m, ContDiffOn ℝ m (F_* (J_ε (locR·Γ))) (0,∞)`;
* `l12`: `L₁₂ (J_ε (locR·Γ)) 0 = 0`, which holds **because** `L₁₂ (locG6) 0 = 0` (the `β` chosen
  by `LocData6.locG6_data` is exactly the normalising scalar making this true) — the logarithmic
  `z`-mollification shifts the scale but preserves `∫ dt/t`, and the angular mollification drops
  out of the `t`-integral.  **Consequently clause (3a) is not available for arbitrary `β`**: the
  interface hypothesis `L₁₂ (locG6 α L β) 0 = 0` is genuinely needed (see `Main.lean`).

## Contents of this module

Only the vocabulary: the abbreviations `Fn`, `locR`, `locG6`, `Jeps` and the target predicate.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS.LocDataExt.Final

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

/-- Profiles in the self-similar variables `(z,θ)`, curried. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-- The **radial factor** of the localised order-`6` datum:
`locG α L β (hLoc α) = locR α L β(z)·Γ(θ)`
(`Work.FTS.LocDataExt.locG_locR_Gam`). -/
abbrev locR (α L β : ℝ) : ℝ → ℝ := Work.FTS.LocDataExt.locR α L β

/-- The localised order-`6` datum of the strong-solution route (`Work.FTS.LocData6.locG6`). -/
abbrev locG6 (α L β : ℝ) : Fn := Work.FTS.LocData6.locG6 α L β

/-- The log-coordinate mollifier `J_ε` of the `ε`-scheme. -/
abbrev Jeps (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : Fn → Fn := Work.FTS.StrongEps.Jeps ρ ε

/-- The `sin θ cos²θ`-moment `F_* g z = ∫_θ g(z,θ) sin θ cos²θ dθ` of the elliptic layer. -/
abbrev Fstar : Fn → ℝ → ℝ := Work.Elliptic.Fstar

/-- **Clause (3a) of the interface**, as a predicate: the localised order-`6` datum is regular
data of the `ε`-scheme. -/
def LocG6EpsDatum (α L β : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : Prop :=
  Work.FTS.StrongEps.EpsDatum α ρ ε (locG6 α L β)

theorem locG6_eq_locR_mul (α L β : ℝ) :
    locG6 α L β = fun z θ => locR α L β z * Work.Spaces.Gam α θ :=
  Work.FTS.LocDataExt.locG_eq_locR_Gam α L β

end Work.FTS_LocDatum3a
