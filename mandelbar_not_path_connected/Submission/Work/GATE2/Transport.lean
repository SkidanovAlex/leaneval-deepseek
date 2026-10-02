/-
# GATE2 — residual 2: TRANSPORT (the design's `G1`–`G3`)

The design's `G1`–`G3` transport the branch data and the base window from the root parameter `c₀`
to the parameters `e` of the two tongues, and this module fixes exactly *how much* of that is
still a residual.

## What is *not* a residual

* **the Böttcher coordinate of the tongue parameter.**  The parameter `e` of a tongue is *outside*
  the mandelbar (`e ∉ Mandelbar`: this is what `SEG` produces, and it is a hypothesis of the gate
  residual).  Böttcher's theorem on the critical domain
  (`Work.Bottcher.bottcherExists_crit` → `Work.Bottcher.exists_isCritBottcher`) then gives a
  critical Böttcher coordinate `φ` of `T_e` for **every** `e`, and the parameter Böttcher map is
  its value at the critical value, `Work.ParamRays.Phi e = φ e`
  (`Work.ParamRays.Phi_eq_of_isCritBottcher`).  So `Work.GATE.GateResidual.hPhi` is *proved*, not
  assumed: `nonempty_gateResidual_of` below turns the pair `(BranchData, BaseWindow)` into the gate
  residual.  (`DynB`/`IsDynBottcher` — the *global* dynamical Böttcher coordinate — is, in
  contrast, false off the mandelbar, see `Submission/Work/ParamRays/Bottcher.lean`; the tongue
  parameters are off the mandelbar, so no global ray tube exists there and the design's tube `D`
  must be an honest thin tube in the critical domain, exactly as §2.3 says.  This is why
  `TongueBranchResidual` below is stated with `IsCritBottcher`, not with `DynB`.)
* **the tube and the branch, *on the mandelbar*.**  Within the connectedness locus the tube of
  dynamical ray points is available (`branchData_rayWindow`: for `α` with `1024 α = α + m`,
  `1/8 < α < 7/8`, the Böttcher inverse branch on the tube of ray points of the `α`-window
  satisfies all four `BranchData` conditions — the generalisation of
  `Work.GATE.Gate.branchData_alpha1_of_rootParabolic` to arbitrary angles and parameters, used here
  for `α₁` (`m = 371`) and `α₂` (`m = 404`)).  This is what makes the *c₀*-side of the residual
  explicit; it does not extend to the tongue parameters.
* **the base window, given the nest region.**  Residual 1 (`Submission/Work/GATE2/Access.lean`,
  `Work.GATE2.basePointWindow_of_nest_mem`) turns the membership of the base point in the nest
  region off `K` into the window bound `BaseWindow.hwin`; so the *content* of `hwin` is a
  *geometric* statement about the base point.

## What *is* the residual

`TongueBranchResidual` below: for every tongue parameter `e` near `c₀`, off the mandelbar, there is
a critical Böttcher coordinate `φ` of `e` (which exists by Böttcher's theorem), and the two design
objects of §2.3:

* `bd : Work.GATE.BranchData φ α` — the `α`-Böttcher branch of the second return map `F_e` on the
  tube `D` of §2.3, **`G1`+`G2`**, whose risk is the choice of `D` (it must avoid the critical
  values of the iterates) and the agreement of the branch fixing `±a_e` with the `α`-branch along
  the critical orbit;
* `bw : Work.GATE.BaseWindow bd e` — **`G3`**, the connecting path `e = Λ^[m] p` with the base point
  `p` in the `α`-window.

`TongueBranchResidual.toTongueResidual` (with `nonempty_gateResidual_of`) produces the per-parameter
gate residual `Work.GATE.GateResidual`, i.e. the hypotheses `h₁`/`h₂` of
`Work.GATE.twoSided_of_residual`; and `Work.GATE.gate_window` (GATE, proved) then gives the angle
transport `G4`.
-/
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.branchData_rayWindow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The tube and the branch on the mandelbar: the two root directions -/

/-- **`1024 * α₁ = α₁ + 371`**: the integer by which the `α₁`-branch is shifted. -/
theorem alpha1_lift : 1024 * Work.EL.alpha1 = Work.EL.alpha1 + ((371 : ℤ) : ℝ) := by
  rw [Work.EL.alpha1]; norm_num

/-- **`1024 * α₂ = α₂ + 404`**. -/
theorem alpha2_lift : 1024 * Work.EL.alpha2 = Work.EL.alpha2 + ((404 : ℤ) : ℝ) := by
  rw [Work.EL.alpha2]; norm_num

/-- **The `α₁`-branch data within the connectedness locus.**  Compare
`Work.GATE.Gate.branchData_alpha1_of_rootParabolic`, which needs a *root-parabolic* parameter: the
construction only uses the dynamical Böttcher data `DynB c φ` and `IsDynBottcher c φ`, so it
applies at every parameter in `M*` carrying them — in particular at the root parameter `c₀` for
*both* root directions, which is what the `c₀`-side of `G1`/`G2` needs. -/
theorem branchData_alpha1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) :
    ∃ bd : Work.GATE.BranchData φ Work.EL.alpha1, bd.F = Work.EL.F c ∧
      ∀ (θ t : ℝ), 1 < t → Work.EL.alpha1 - 1 / 8 < θ → θ < Work.EL.alpha1 + 1 / 8 →
        Work.EL.rayPt hN θ t ∈ bd.S :=
  branchData_rayWindow hN hB Work.EL.alpha1 371 alpha1_lift (by rw [Work.EL.alpha1]; norm_num)
    (by rw [Work.EL.alpha1]; norm_num)

/-- **The `α₂`-branch data within the connectedness locus** (with the lifting integer `404`). -/
theorem branchData_alpha2 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) :
    ∃ bd : Work.GATE.BranchData φ Work.EL.alpha2, bd.F = Work.EL.F c ∧
      ∀ (θ t : ℝ), 1 < t → Work.EL.alpha2 - 1 / 8 < θ → θ < Work.EL.alpha2 + 1 / 8 →
        Work.EL.rayPt hN θ t ∈ bd.S :=
  branchData_rayWindow hN hB Work.EL.alpha2 404 alpha2_lift (by rw [Work.EL.alpha2]; norm_num)
    (by rw [Work.EL.alpha2]; norm_num)

/-! ## The residual, and its decomposition -/

/-- **The transport residual of the two tongues, with the Böttcher coordinate of the tongue
parameter made explicit.**  For every parameter `e` of the `b`-tongue (resp. `ι b`-tongue) near
`c₀`, off the mandelbar:

* a critical Böttcher coordinate `φ` of `T_e` (Böttcher's theorem, hence repairable), and
* the two design objects `BranchData φ α` (`G1`+`G2`) and `BaseWindow bd e` (`G3`).

The `DynB`/`IsDynBottcher` predicates are *not* used here: they are false off the mandelbar
(`Submission/Work/ParamRays/Bottcher.lean`), while `e ∉ Mandelbar` holds by hypothesis. -/
structure TongueBranchResidual (c₀ : ℂ) (Nm : Set ℂ) (TD : Work.GATE.TransitData c₀ Nm) where
  /-- the radius on which the transport holds. -/
  ρ : ℝ
  /-- ... which is positive. -/
  hρ : 0 < ρ
  /-- the `b`-tongue, direction `α₁`. -/
  b : ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e →
    e ∉ Mandelbar →
      ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher e φ ∧
        ∃ bd : Work.GATE.BranchData φ Work.EL.alpha1, bd.F = Work.EL.F e ∧
          Nonempty (Work.GATE.BaseWindow bd e)
  /-- the `ι b`-tongue, direction `α₂`. -/
  iota : ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e →
    e ∉ Mandelbar →
      ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher e φ ∧
        ∃ bd : Work.GATE.BranchData φ Work.EL.alpha2, bd.F = Work.EL.F e ∧
          Nonempty (Work.GATE.BaseWindow bd e)

/-- **The base window from the three pieces of `G3`.**  The `G3` data of the design is the triple
(the number `m` of gate iterations, the base point `p = F_e^[m] e` of the tube, and the branch
identity `e = Λ^[m] p`), together with the window bound on the base point.  This is the interface
on which residual 1's ACCESS acts: `hwin` is `BasePointWindow` (ACCESS) converted by the
`α`-window. -/
theorem nonempty_baseWindow_of {φ : ℂ → ℂ} {α : ℝ} (bd : Work.GATE.BranchData φ α) (e : ℂ)
    (m : ℕ) (p : ℂ) (hS : p ∈ bd.S) (hbase : e = bd.Λ^[m] p)
    (hwin : |Work.GATE.deviation φ α p| < Work.Final.windowEps) :
    Nonempty (Work.GATE.BaseWindow bd e) :=
  ⟨⟨m, p, hS, hbase, hwin⟩⟩

/-- **The gate residual from the two design objects.**  Off the mandelbar the Böttcher coordinate of
`GateResidual` is forced (`Work.ParamRays.Phi_eq_of_isCritBottcher`), so the whole content of the
gate residual is the pair `(BranchData, BaseWindow)` of §2.3. -/
theorem nonempty_gateResidual_of {e : ℂ} {α : ℝ} (hM : e ∉ Mandelbar) {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsCritBottcher e φ) (bd : Work.GATE.BranchData φ α)
    (bw : Work.GATE.BaseWindow bd e) : Nonempty (Work.GATE.GateResidual e α) :=
  ⟨⟨φ, bd, bw, Work.ParamRays.Phi_eq_of_isCritBottcher hM hφ⟩⟩

/-- **The residual in its purely per-parameter form produces the transport residual.**  The only
new ingredient is the identification `Work.ParamRays.Phi e = φ e` of the parameter Böttcher map
with the critical coordinate of `T_e` (Böttcher uniqueness off the mandelbar). -/
def TongueBranchResidual.toTongueResidual {c₀ : ℂ} {Nm : Set ℂ}
    {TD : Work.GATE.TransitData c₀ Nm} (TR : TongueBranchResidual c₀ Nm TD) :
    TongueResidual c₀ Nm TD where
  ρ := TR.ρ
  hρ := TR.hρ
  b := by
    intro e he ht hM
    obtain ⟨φ, hφ, bd, -, ⟨bw⟩⟩ := TR.b e he ht hM
    exact nonempty_gateResidual_of hM hφ bd bw
  iota := by
    intro e he ht hM
    obtain ⟨φ, hφ, bd, -, ⟨bw⟩⟩ := TR.iota e he ht hM
    exact nonempty_gateResidual_of hM hφ bd bw

/-- **The design's `G3` base window from residual 1 (ACCESS).**  If the base point `p` of the
connecting path lies in the nest region of the `z₁`-nest off the filled Julia set — the conclusion
of `Work.GATE2.basePointWindow_of_nest_mem` (residual 1) — then `p` satisfies the window bound on
which `G3` rests.  This is the sense in which the window input of the transport is *not* part of
residual 2. -/
theorem baseWindow_hwin_of_basePointWindow {φ : ℂ → ℂ} (z : ℂ) (h : BasePointWindow φ z) :
    |Work.GATE.deviation φ Work.EL.alpha1 z| < Work.Final.windowEps ∨
      |Work.GATE.deviation φ Work.EL.alpha2 z| < Work.Final.windowEps := h

/-- **The gate conclusion from the residual in the explicit `(m, p)` form.**  A critical Böttcher
coordinate `φ` of `e` (Böttcher's theorem), an `α`-branch `bd` on its tube, and an explicit gate
iteration count `m`, base point `p = F_e^[m] e` in the tube with `e = Λ^[m] p` and the `α`-window
bound, put the *external angle* of `e` in the `α`-window.  This is the `(m, p)`-form of the residual
on which a future stretch can work directly, with the conclusion `G4` already discharged. -/
theorem extAngle_window_of_orbitWindow {e : ℂ} {α : ℝ} (hα0 : 1 / 4 < α) (hα1 : α < 3 / 4)
    (hM : e ∉ Mandelbar) {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsCritBottcher e φ)
    (bd : Work.GATE.BranchData φ α) (m : ℕ) (p : ℂ) (hS : p ∈ bd.S)
    (hbase : e = bd.Λ^[m] p) (hwin : |Work.GATE.deviation φ α p| < Work.Final.windowEps) :
    |Work.ParamRays.extAngle e - α| < Work.Final.windowEps :=
  Work.GATE.gate_window bd ⟨m, p, hS, hbase, hwin⟩ hα0 hα1
    (Work.ParamRays.Phi_eq_of_isCritBottcher hM hφ)

/-- **The gate residual contains the two design objects**: this is the converse bookkeeping of
`nonempty_gateResidual_of`, recorded so that a caller can switch between the two forms. -/
theorem exists_branchData_of_gateResidual {e : ℂ} {α : ℝ} (G : Work.GATE.GateResidual e α) :
    ∃ bd : Work.GATE.BranchData G.φ α, Nonempty (Work.GATE.BaseWindow bd e) :=
  ⟨G.bd, ⟨G.bw⟩⟩


end Work.GATE2
