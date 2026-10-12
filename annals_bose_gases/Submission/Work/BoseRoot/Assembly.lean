import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.BoseAllGlue.Assembly
import Submission.Work.BoseAllGlue.RB4boxDomFSAllOfBridge
import Submission.Work.BoseB1Cube.nominalPerBoxRow
import Submission.Work.BoseBogFS.ZPLatticeRowHolds
import Submission.Work.BoseBogFS.honestBogOpBoundFSAll_final
import Submission.Work.BoseC3QAll.AllStatement
import Submission.Work.BoseFixB3.Node
import Submission.Work.BoseFixR.All.RB5FSAllKHonest
import Submission.Work.BoseGateAll.Interface
import Submission.Work.BoseGateAll.LMono
import Submission.Work.BoseRowQ2.rowQ2AllRegimeN_honest
import Submission.Work.BoseRowsL.Glue.rowIntOneRegime_of_interfaceL
import Submission.Work.BoseSWE.Final
import Submission.Work.BoseWireFix.exists_honestModes_family
import Submission.Work.BoseWireFix.hpres_of_LHYBoxBPos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseRoot.Assembly` — root assembly of `annals_bose_gases` (curric-46, 2026-10-08)

`LHYBoxBPos_holds` proves the box input `Work.BoseWireFix.LHYBoxBPos v` from the glue, and
`hpres_root` is the `hpres` block of `Submission.BoseGases.theorem_1_2` end to end (through
`Work.BoseWireFix.hpres_of_LHYBoxBPos`, which needs neither FS T1 nor T2).  `sorryAx` comes
**only** from these named leaves (reach scan over `Expr.getUsedConstants`, 2026-10-08, 18.221):

| leaf | where |
|---|---|
| `Work.BoseB1Cube.cubePerBox_holds` | `BoseB1Cube/cubePerBox_holds.lean` (L12440) |
| `Work.BoseB1Cube.cubeCrudeBand_holds` | `BoseB1Cube/cubeCrudeBand_holds.lean` (L12449) |
| `Work.BoseBoxFock.box_to_model` | via `RB4boxDomFSAll_of_bridge` (L4804) |
| `Work.BoseBogFS.cleanFun_tsum_le_integral` | via `ZPLatticeRowHolds` (L12076) |
| `Work.BoseRootAsm.rowQ2AllRegimeN_leaf` | this file: row 3 (`hrow3All`) = statement (E) `Work.BoseRowQ2.rowQ2AllRegimeN_honest` of the NH ruling |

**Why not `LHYBoxBInput_holds`.**  `Work.BoseRoot.LHYBoxBInput_holds : LHYBoxBInput v` bundles
`∃ h : ScatSol v` (FS T1) and needs `0 < a v` (T2); both are `sorry` in `Submission/ScatFacts.lean`.
So `theorem_1_2` is rewired to `hpres_root` (one line in `Submission.lean`), and
`LHYBoxBInput_holds` becomes unused.

**Prerequisite (import clash).**  The cone of `Work.BoseFixB3.nodeB3B_holds` (via
`BoseFixB1S/boxConstCalibB1`) and the cone of `Work.BoseB1Cube.cubePerBox_holds` (via
`BoseFixB1S/boxPairValue`) each declare a *different* `Work.BoseFixB1S.pairMass_eq_setIntegral`.
Rename the `boxConstCalibB1.lean:119` copy to `pairMass_eq_setIntegral_calib` and its single code
user `flatQLHSword_eq.lean:255`.

**Prerequisite (import cycle).**  This module must not import the root `Submission` (which will
import it).  Before the cut it does: `BoseBoxFock.Defs → BoseFixB1.HeadlineFull → … →
OneBodyTwoCut.Defs → ChiCarrierFix.All → ChiCarrierFix.Defs → UBB.All → UBB.PaperTheorem →
Submission`.  Cut it by removing `UBB.PaperTheorem` from `UBB/All.lean` and `ChiCarrierFix.Endgame`
from `ChiCarrierFix/All.lean` (+ import fix-ups); see `cbc/bose_root_install.md`.
-/

noncomputable section

open MeasureTheory Metric

namespace Work.BoseRootAsm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. A concrete low cut-off (every glue row is `∀ fc fu`; the frozen nodes do not
mention them, so any inhabitant works) -/

/-- `f s = 1 − smoothTransition (s − 1)`: `1` on `s ≤ 1`, `0` on `s ≥ 2`, smooth, antitone. -/
def stdCut : Work.BoseBoxFix.LowCut where
  f := fun s => 1 - Real.smoothTransition (s - 1)
  smooth := contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  anti := fun a b hab => by
    have h2 := Real.smoothTransition.monotone (show a - 1 ≤ b - 1 by linarith)
    linarith
  one := fun s hs => by
    rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num
  zero := fun s hs => by
    rw [Real.smoothTransition.one_of_one_le (by linarith)]; norm_num

/-! ## 1. The one NEW leaf: row 3 of the gate -/

/-- **LEAF (row 3, `hrow3All`)** — verbatim the statement (E) `Work.BoseRowQ2.rowQ2AllRegimeN_honest`
of the NH ruling (`cbc/bose_nh_ruling.md`, `BoseRowQ2/LEAD_RULING_NH_stmts.lean.txt`): row 3 is
TRUE at the frozen `NH`, proved by the `RowsN` core (`GchiAtN` + `ArithAt2` + `RowArith` +
`MainAtN`) assembled by `RowQ2AllRegimeN_of_coreN`.  (E) is not yet on disk; when it lands,
replace this `sorry` by `Work.BoseRowQ2.rowQ2AllRegimeN_honest R hR hav hv_nonneg hvrad hv_supp
εg hεg hεg1 hrég`. -/
theorem rowQ2AllRegimeN_leaf {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
      Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng R εg' :=
  Work.BoseRowQ2.rowQ2AllRegimeN_honest R hR hav hv_nonneg hvrad hv_supp εg hεg hεg1 hrég

/-! ## 2. The `All` gate (threshold promotion for row 3) -/

/-- **The `All` gate**, from the proved interface `exists_honestInterfaceL`, the proved row 2
`rowIntOneRegime_of_interfaceL`, and the row-3 leaf.  Row 3 arrives at its own `(Ng₃, ε₃)`, so
the thresholds are promoted (`promoteNg` + `mono`) and the interface is moved along
(`HonestInterfaceL.mono`) before row 2 is re-derived at the new bundle. -/
theorem exists_honestGateFSAll {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ Work.BoseBoxFock.HonestGateFSAll v h fc fu K₀ b₀ := by
  obtain ⟨hthr, ⟨H⟩⟩ := Work.BoseRowsL.exists_honestInterfaceL (h := h) (fc := fc) (fu := fu)
    R hR hav hv_nonneg hvrad hv_supp
  -- the régime row of (E) is the first and third `dil` row of the bundle (any honest family
  -- dominating `hthr.Ng` witnesses it; those two rows do not depend on the family)
  obtain ⟨HM₀, hHM₀⟩ := Work.BoseWireFix.exists_honestModes_family v hthr.Ng
  have hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := fun μ hμ hle =>
    ⟨(hthr.dil HM₀ hHM₀ μ hμ hle).1, (hthr.dil HM₀ hHM₀ μ hμ hle).2.2.1⟩
  obtain ⟨Ng₃, ε₃, hε₃, hε₃le, hrow3⟩ := rowQ2AllRegimeN_leaf (h := h) (fc := fc) (fu := fu)
    R hR hav hv_nonneg hvrad hv_supp hthr.εg hthr.pos hthr.le_one hrég
  let Ngp : ℝ → ℕ := fun μ => max (hthr.Ng μ) (Ng₃ μ)
  let hthr' : Work.BoseGateFS.GateThresholds v h fc fu R :=
    (hthr.promoteNg Ngp (fun μ => le_max_left _ _)).mono hε₃ hε₃le
  have hNg' : ∀ μ, hthr'.Ng μ = Ngp μ := fun μ => rfl
  have hεg' : hthr'.εg = ε₃ := rfl
  let H' : Work.BoseRowsL.HonestInterfaceL R hthr' :=
    H.mono (hthr' := hthr') (by rw [hεg']; exact hε₃le)
      (fun μ => max (hthr'.Ng μ) (H.Ng' μ)) (fun μ => le_max_left _ _)
      (fun μ => le_max_right _ _)
  have hrow3' : Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu)
      hthr'.Ng R hthr'.εg :=
    Work.BoseRowQ2.RowQ2AllRegimeN_mono hrow3
      (fun μ => by rw [hNg' μ]; exact le_max_right _ _) (by rw [hεg'])
  exact Work.BoseGateAll.exists_honestGateFSAll_of_honestInterfaceL R hR hav hv_nonneg hvrad
    hv_supp hthr' H'
    (Work.BoseRowsL.Glue.rowIntOneRegime_of_interfaceL R hR hav hv_nonneg hvrad hv_supp hthr' H')
    hrow3'

/-! ## 3. The `Ŵ₁` cut-off pin `hN` (a cube-size requirement, met by choice of `HM`) -/

/-- **`N_uv`**: a cube-size requirement function making the `Ŵ₁` cut-off row of
`viewFSAll_of_gateAll` hold at every `μ > 0`.  `uvRad ℓ N = 2πN/(4ℓ)` is linear in `N`. -/
theorem exists_Nuv (v : ℝ³ → ℝ) (hav : 0 < _root_.BoseGases.a v) :
    ∃ Nuv : ℝ → ℕ, ∀ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ,
      (∀ μ, Nuv μ ≤ (HM μ).N) → ∀ μ, 0 < μ →
        4 * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
            * Real.sqrt (μ * _root_.BoseGases.a v))
          ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N := by
  let T : ℝ → ℝ := fun μ =>
    4 * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
        * Real.sqrt (μ * _root_.BoseGases.a v))
  refine ⟨fun μ => ⌈T μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * 2 / Real.pi⌉₊,
    fun HM hHM μ hμ => ?_⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hπ : 0 < Real.pi := Real.pi_pos
  have hx : T μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * 2 / Real.pi ≤ ((HM μ).N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hHM μ)
  have hc : 0 ≤ 2 * Real.pi / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 4 := by positivity
  show T μ ≤ _
  calc T μ = (T μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * 2 / Real.pi)
          * (2 * Real.pi / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 4) := by
        field_simp; ring
    _ ≤ ((HM μ).N : ℝ) * (2 * Real.pi / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 4) :=
        mul_le_mul_of_nonneg_right hx hc
    _ = Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N := by
        unfold Work.BoseBoxFock.uvRad; ring

/-! ## 4. The root -/

/-- **The box input `LHYBoxBPos v`**, sorry-free modulo the five leaves of the module doc. -/
theorem LHYBoxBPos_holds (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_radial : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    Work.BoseWireFix.LHYBoxBPos v := by
  intro h hav
  have hvx : ∀ x : ℝ³, 0 ≤ v x := fun x => hv_nonneg x
  -- §5 node (FS `thm:smallbox`): the two cube leaves
  have hB1 : ∀ J : ℝ, Work.UBB.lhyC ≤ J → Work.BoseBoxFix.NodeB1B v h J := fun J hJ =>
    -- curric-46 10-12: via route R2 (cbc/bose_cube_endgame.md) — no cube leaf needed
    Work.BoseSWE.nodeB1B_final h hv_nonneg hv_memL1 hv_radial hR hv_supp hav J
  -- grading levels
  have hJJ : Work.UBB.lhyC < Work.UBB.lhyC + 1 := by linarith
  -- §6 node
  have hg : Work.BoseBoxFix.NodeB2gB v h Work.UBB.lhyC (Work.UBB.lhyC + 1) :=
    Work.BoseFixGlue.Ports.nodeB2gB_of_data hav le_rfl hJJ
      (Work.BoseFixB2.b2GradingDataB_holds hv_nonneg hv_memL1 hv_radial hR hv_supp hav le_rfl
        (hB1 _ le_rfl))
      (Work.BoseFixGlue.B2AprioriWindowB_of_NodeB1B hav (hB1 _ hJJ.le))
  -- §7–11 node: gate, §8 bridge, cube sizes
  obtain ⟨K₀, b₀, hK₀, hb₀, Ng, εg, hεg, hεg1, hgateF⟩ :=
    exists_honestGateFSAll h stdCut stdCut R hR hav hvx hv_radial hv_supp
  obtain ⟨Nmin, hNmin⟩ := Work.BoseBoxFock.RB4boxDomFSAll_of_bridge v h hv_nonneg hv_memL1
    hv_radial hR hv_supp hav stdCut stdCut (Work.UBB.lhyC + 1)
    (Work.BoseFixB3.nodeB3B_holds h hv_nonneg hv_memL1 hv_radial hR hv_supp hav stdCut)
  obtain ⟨Nuv, hNuv⟩ := exists_Nuv v hav
  obtain ⟨HM, hHM1, hHM2, hHM3⟩ := Work.BoseWireFix.exists_honestModes_family_max v Nmin Ng Nuv
  obtain ⟨η₀, hη₁, hη₂, C, hC, hr⟩ := Work.BoseAllGlue.nodeRestrictedB_of_AllRows (h := h)
    hv_nonneg hv_memL1 hv_radial hv_supp hav hR hJJ stdCut stdCut HM (hB1 _ hJJ.le)
    (hNmin HM hHM1) hb₀ hεg hεg1 (hgateF HM hHM2) (hNuv HM hHM3)
    (Work.BoseBoxFock.control3QFSAll K₀ b₀ hb₀)
    (Work.BoseBogFS.honestBogOpBoundFSAll_final hR hvx hv_memL1 hv_radial hv_supp hav
      (Work.BoseBogFS.ZPLatticeRowHolds v h hR hvx hv_radial hv_supp hav))
    (Work.BoseFixR.All.RB5FSAllKHonest h hv_nonneg hv_memL1 hv_radial hR hv_supp hav
      stdCut stdCut HM)
  refine ⟨η₀, C + 1, hη₁, by linarith, by linarith, ?_⟩
  exact Work.BoseFixGlue.Ports.LHYBoxB_of_grading le_rfl hav hC (by linarith) hη₂ hJJ hg hr

/-- The bundled form, available exactly when `0 < a v` (the `a v = 0` case needs FS T1). -/
theorem LHYBoxBInput_holds_of_av_pos (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_radial : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseWire.LHYBoxBInput v :=
  Work.BoseWireFix.LHYBoxBPos.toInput (LHYBoxBPos_holds v hv_nonneg hv_radial hv_memL1 hR hv_supp)
    (Work.BoseWireFix.exists_scatSol_of_av_pos hav) hav

/-- The `hpres` block of `Submission.BoseGases.theorem_1_2`, end to end. -/
theorem hpres_root (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_radial : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      Submission.BoseGases.lhyRhs (BoseGases.a v) 1 (1 / 2 + Work.BoseTop.etaBose) ρ ≤
        Submission.BoseGases.gcPressure v ρmax (8 * Real.pi * BoseGases.a v * ρ)
          + 8 * Real.pi * BoseGases.a v * ρ * ρ :=
  Work.BoseWireFix.hpres_of_LHYBoxBPos hv_nonneg hv_radial hv_memL1 hR hv_supp
    (LHYBoxBPos_holds v hv_nonneg hv_radial hv_memL1 hR hv_supp)

end Work.BoseRootAsm
