/-
# `Submission/Work/FTS_LocDatum3a/Assembly.lean` — clause (3a′): `locG6_epsDatum`

This is the assembly of the chapter: the localised order-`6` datum

  `locG6 α L β = locR α L β(z) · Γ(θ) = - zfar L F_* + β · hLoc α`

is **regular data of the `ε`-scheme**, i.e. lies in

  `Work.FTS.StrongEps.EpsDatum α ρ ε = SmoothOpen ∧ HkMem α 6 ∧ ClassC α (J_ε ·)`,

for `0 < α ≤ 1`, `1 ≤ L`, `ρ` a smooth mollifier kernel, `ε > 0`, and the datum satisfying

  `L₁₂ (locG6 α L β) 0 = 0`

(the `β` produced by `Work.FTS.LocData6.locG6_data`).  The `L₁₂`-hypothesis is **necessary**:
for arbitrary `β` the class-C clause `l12` fails (the lead's ruling,
`Submission/Work/FTS_LocDatum3a/LEAD_ellim_3a.md` §B), which is why the interface carries the
field `(3a′)` rather than `(3a)`.

## The three conjuncts

* `SmoothOpen (locG6 α L β)`: `Basic.smoothOpen_locG6` (unconditional in `α, L, β`).
* `HkMem α 6 (locG6 α L β)`: the second field of the unconditional
  `Work.FTS.LocData6.regQ_locG6_uncond`.
* `ClassC α (J_ε (locG6 α L β))`: `classC_Jeps_locG6` below, built from
  - the five **mollifier** clauses (`norm`, `reg`, `mem8`, `tr7`, `axis`) supplied by
    `Work.FTS.StrongEps.softClass_Jeps`, whose datum-side hypotheses are
    `forall_contDiffOn_locG6` (smoothness), `HkMem_locG8` (order-8 honesty),
    `BdryTraces_data_locG6` (the four uniform endpoint-vanishing conditions, `a + b ≤ 7`),
    `hax_locG6` (the axis condition) and `locallyIntegrable_logPull_locG6`;
  - the two **non-mollifier** clauses `fsm` and `l12` supplied by the datum:
    `contDiffOn_Fstar_Jeps_locG6` (the angular moment of the log-mollified separable datum is
    `C^∞` on `(0,∞)`) and `L12_Jeps_locG6` (the `L₁₂`-zero-mode is transported by `J_ε`, because
    the logarithmic `z`-mollification preserves `∫ dt/t`).

The remaining `ClassC` fields `mem` (`HkMem α 7`) and `tr` (`BdryTraces α 6`) are the
monotone descents of `mem8` and `tr7`.  The field `mem10` (lead install 2026-10-11) is
`SoftClass.mem10`, i.e. the two-derivative mollifier gain
`StrongEps.HkMem_Jeps_ten_of_eight` applied to `HkMem_locG8`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_LocDatum3a.HkMem_locG8
import Submission.Work.FTS_LocDatum3a.BdryTraces_data_locG6
import Submission.Work.FTS_LocDatum3a.L12_Jeps_locG6
import Submission.Work.FTS_LocDatum3a.contDiffOn_Fstar_Jeps_sep
import Submission.Work.FTS.LocData6.RegQ6
import Submission.Work.FTS.StrongEps.MolClassC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## `fsm`: the angular moment of the log-mollified datum -/

/-- The `fsm` clause of `ClassC` for the localised datum: `F_*(J_ε (locG6 α L β))` is `C^∞` on
`(0,∞)`.  This is the separable form of `contDiffOn_Fstar_Jeps_sep`, read through
`locG6 α L β = locR α L β · Γ`. -/
theorem contDiffOn_Fstar_Jeps_locG6 {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {α L β : ℝ}
    (hα : 0 < α) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε (locG6 α L β))) (Set.Ioi 0) := by
  have h : locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  rw [h]
  exact contDiffOn_Fstar_Jeps_sep (α := α) (a := Work.FTS.LocDataExt.locR α L β)
    hρ hε hα ((Work.FTS.LocDataExt.contDiffOn_locR α L β).mono
      (Set.Ioi_subset_Ioi (by norm_num)))

/-! ## The source class `ClassC` -/

/-- **The localised datum with the mollifier applied is in the elliptic source class**:
`ClassC α (J_ε (locG6 α L β))`. -/
theorem classC_Jeps_locG6 {α L β : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (h12 : Work.Construction.L12 (locG6 α L β) 0 = 0) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Jeps ρ ε (locG6 α L β)) := by
  obtain ⟨hbdd, hz0, hzin, ht0, ht1⟩ := BdryTraces_data_locG6 α L β hα hα1 hL
  have hsoft : Work.FTS.StrongEps.SoftClass α (Work.FTS.StrongEps.Jeps ρ ε (locG6 α L β)) :=
    Work.FTS.StrongEps.softClass_Jeps hρ ⟨hα, hα1⟩ hε
      (forall_contDiffOn_locG6 α L β) (HkMem_locG8 α L β hα hα1 hL)
      hbdd hz0 hzin ht0 ht1 (hax_locG6_eps α L β hL) (locallyIntegrable_logPull_locG6 α L β)
  exact
    { norm := hsoft.norm
      reg := hsoft.reg
      mem := Work.FTS.OpenPkg.HkMem_mono_open hsoft.reg 7 (by norm_num) hsoft.mem8
      mem8 := hsoft.mem8
      mem10 := hsoft.mem10
      tr := Work.FTS.ClassC.bdryTraces_mono (by norm_num : 6 ≤ 7) hsoft.tr7
      tr7 := hsoft.tr7
      fsm := contDiffOn_Fstar_Jeps_locG6 hρ hε hα
      axis := hsoft.axis
      l12 := L12_Jeps_locG6 α L β hα hα1 hL hρ hε h12
      thTr := hsoft.thTr }

/-! ## The deliverable -/

/-- **(3a′) — the localised order-`6` datum is regular data of the `ε`-scheme.**  For
`0 < α ≤ 1`, `1 ≤ L`, an `L₁₂`-orthogonal datum (`L₁₂ (locG6 α L β) 0 = 0`, which the producer
`Work.FTS.LocData6.locG6_data` supplies), a smooth mollifier kernel `ρ` and `ε > 0`,

  `EpsDatum α ρ ε (locG6 α L β) = SmoothOpen ∧ HkMem α 6 ∧ ClassC α (J_ε (locG6 α L β))`. -/
theorem locG6_epsDatum (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (h12 : Work.Construction.L12 (locG6 α L β) 0 = 0)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    Work.FTS.StrongEps.EpsDatum α ρ ε (locG6 α L β) :=
  ⟨smoothOpen_locG6 α L β,
    (Work.FTS.LocData6.regQ_locG6_uncond α L β hα hα1 hL).2.1,
    classC_Jeps_locG6 hα hα1 hL hρ hε h12⟩

/-- The deliverable under the name `<name>_proved` (same statement as `locG6_epsDatum`). -/
theorem locG6_epsDatum_proved (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (h12 : Work.Construction.L12 (locG6 α L β) 0 = 0)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    Work.FTS.StrongEps.EpsDatum α ρ ε (locG6 α L β) :=
  locG6_epsDatum α L β hα hα1 hL h12 hρ hε

/-- **(3a′) in the shape of the core field** of `Submission/Work/FTS/Final/Assembly.lean`: the
same statement at `pExp α = 3α`, with the (unused) hypothesis `RegQ (pExp α) 6 (locG6 …)` of the
interface carried along. -/
theorem core3a'_of_locG6 {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ L β : ℝ, 1 ≤ L → Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 6
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) →
      Work.Construction.L12 (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) 0 = 0 →
      ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (Work.FTS.Regularity.pExp α) ρ ε
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) :=
  fun L β hL _ h12 ε hε =>
    locG6_epsDatum _ L β (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13) hL h12 hρ hε

end Work.FTS_LocDatum3a
