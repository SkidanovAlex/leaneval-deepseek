/-
# `E4R3/N4C/rows/Hon` — the honest row context: projections of `CtxT`

`Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg` is the honest (§8-row) context of the
class-`C` route: the profile `g` carries `ClassC α g` (open-quadrant `C^∞`, `ℋ^7`-honesty,
`BdryTraces` up to order `6`) and the *open* coercivity class `CoerAdmO α g`, and the two
elliptic packages are the open-quadrant `StarPkgo2 α Cs Φs` and `EllPkgGo α Ce g Φg`.

This module collects the elementary projections which the honest versions of the §8 rows
consume, so that each row proof can start from the *same* list of facts:

* smoothness and honesty of `g` at every order `≤ 10` (`ClassC.mem/mem8/mem10` + monotonicity);
* the open classes `RegQo α k g`, `HQo α k g` and the ports `D_θ`, `D_z`
  (`StrongEps.EpsE4Thr.regQo_dth_dz`);
* the vanishing of the integration-by-parts boundary terms, the vanishing `L₁₂`-zero mode, the
  angular vanishing and the two axis values (`CoerAdmO`);
* the decay at `z = ∞`: `Work.Spaces.DecayAll 4 g`, derived in the sibling module
  `rows/decayAll4_of_classC`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Smoothness, honesty and the `ℋ^k`-norms of the profile -/

/-- `ClassC` gives open-quadrant `C^∞`. -/
theorem CtxT.hSmoothOpen {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn}
    (h : CtxT Cs Ce α₂ α g Φs Φg) : Work.FTS.EllipticEst.SmoothOpen g := h.hg.reg

/-- The `ℋ^k`-honesty of the profile, for every `k ≤ 10`. -/
theorem CtxT.hkMem {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    {k : ℕ} (hk : k ≤ 10) : Work.Spaces.HkMem α k g :=
  Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg k hk h.hg.mem10

theorem CtxT.hkMem4 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 4 g := h.hkMem (by norm_num)

theorem CtxT.hkMem5 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 5 g := h.hkMem (by norm_num)

theorem CtxT.hkMem6 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 6 g := h.hkMem (by norm_num)

theorem CtxT.hkMem7 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 7 g := h.hkMem (by norm_num)

/-- The honest `ℋ⁴`-class of the profile. -/
theorem CtxT.hqo {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    {k : ℕ} (hk : k ≤ 10) : Work.FTS.VocabO.HQo α k g := ⟨h.hSmoothOpen, h.hkMem hk⟩

theorem CtxT.hcoerAdmO {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g := h.hco

theorem CtxT.regQo5 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 g := h.hco.1

theorem CtxT.regQo4 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 g := h.hco.regQoFour

/-- `RegQo α (n+1) g` gives the ports `D_θ g` and `D_z g` in `RegQo α n` (hence in `ℋ^n`). -/
theorem CtxT.regQo_dth_dz {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Spaces.Dth g) ∧
      Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Spaces.Dz g) :=
  Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz h.hα h.regQo5

/-- The `D_θ`-slot of the profile is honest. -/
theorem CtxT.hkMemDth {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
  (h.regQo_dth_dz).1.2.1

/-- The `D_z`-slot of the profile is honest. -/
theorem CtxT.hkMemDz {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
  (h.regQo_dth_dz).2.2.1

theorem CtxT.hqoDth {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) :=
  ⟨(h.regQo_dth_dz).1.1, h.hkMemDth⟩

theorem CtxT.hvanish {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.VanishTheta g := h.hco.2.1

theorem CtxT.haxis {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 ∧ Work.Spaces.pz g 0 θ = 0 := h.hco.2.2.1

theorem CtxT.hL12 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Construction.L12 g 0 = 0 := h.hco.2.2.2

theorem CtxT.hbdry {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.Nonlin.BdryTraces α 6 g := h.hg.tr

/-! ## The two elliptic packages -/

theorem CtxT.hstar {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs := h.hs

end Work.FTS.StrongEps.E4R3.N4C
