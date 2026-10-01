/-
# ZeroFreeTables — Main.lean

The end of the AREA 3 chain, re-pointed onto the **round-2 contract**
(`Submission/Work/LinnikContract2/`, frozen):

* the target is `Work.LinnikContract2.Area3 = Area1 → ZeroFreeCert` (the five clauses `Z1`–`Z5`,
  with `λ₁` the wide minimiser at height `50`); `Area1` (Burgess) is the bound variable of the
  `Area3`-lambda, exactly as the contract entitles this area to do;
* **`HBOffAxis` is now a theorem, not an input.**  `Work.ZeroFreeTables.hbOffAxis_of_rect`
  (`OffAxis/Main.lean`, the OA8 assembly of `OFFAXIS_ROUTE_LEAD.md`) derives
  `HBOffAxis = ZeroFreeCertOffAxis` from the two height-`L` certificates `RectCertC`, `RectCertS`
  and Jutila's family density estimate `Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2`.  The main
  theorems below therefore take `hC : Area1 → RectCertC`, `Work.ZeroFreeTables.OffAxis.RectCertS_proof : RectCertS`, `hJ : …` in place of
  `hOff : HBOffAxis`; the variant `linnikContract2_Area3_of_hbOffAxis` still takes `hOff` directly;
* **discharged inside this area**: HB Table 8 (all the rational certificates `Table8Cert*` and
  `HBTable8_printed`), `HBTheorem1` (`HBTheorem1_proof`), `HBTable4` (`HBTable4_proof`),
  `HBTable9` (from `Area1.1 = LBound13`, `HBTable9_of_burgess`), `HBLemma9_4`
  (`HBLemma9_4_proof`), `HBRepZeroC` (`HBRepZeroC_proof`) and `RectCertC`
  (`OffAxis/RectCertC_proof`);
* **the remaining inputs** are the paper's own statements `HBLemma9_1`, `XYLemma3_8`,
  `HB10_3_conclusion`, `HBTable7`, `HBLemma8_4`, `HBLemma8_8`, together with the off-axis
  certificate `RectCertS` and a density input — Jutila's `FamDensityEpsRange (4/5) 1 2` or the
  sharper non-principal `Work.ZeroDensity.LogFree.logFreeNP σ₀ c`.

Every theorem in this file is axiom-clean: `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.

The round-1 vocabulary is still present for continuity: `Work.LinnikContract.Area3` with the
narrow `IsMin1` and the (refuted) bridge `HBNumbering696` in `API.lean` are documented in
`README.md` §3 and `ENGINE_AUDIT_LEAD.md`; nothing in this file uses them.
-/
import Submission.Work.ZeroFreeTables.Assemble
import Submission.Work.ZeroFreeTables.Table8Cert
import Submission.Work.ZeroFreeTables.Table8CertExt
import Submission.Work.ZeroFreeTables.Lemma10_3Cert
import Submission.Work.ZeroFreeTables.Table8Printed
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_nonneg
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.HBTable9_proof
import Submission.Work.ZeroFreeTables.HBTable4_proof
import Submission.Work.ZeroFreeTables.HBLemma9_4_proof
import Submission.Work.ZeroFreeTables.OffAxis.Main
import Submission.Work.ZeroFreeTables.OffAxis.MainLogFree
import Submission.Work.ZeroFreeTables.OffAxis.RectCertC_proof
import Submission.Work.ZeroFreeTables.OffAxis.RectCertS_proof
import Submission.Work.ZeroFreeTables.HBTheorem1_proof
import Submission.Work.ZeroFreeTables.HBTable7_proof
import Submission.Work.ZeroFreeTables.HBLemma9_1_proof
import Submission.Work.ZeroFreeTables.XYLemma3_8_proof
import Submission.Work.ZeroFreeTables.HBLemma10_3_engine_proof
import Submission.Work.ZeroFreeTables.HB10_3_conclusion_of_engine_v2
import Submission.Work.ZeroFreeTables.HB10_3_Fcases_proof
import Submission.Work.ZeroFreeTables.HBRepZeroC_proof
import Submission.Work.ZeroFreeTables.HBLemma8_4_proof
import Submission.Work.ZeroFreeTables.HBLemma8_8_proof
import Submission.Work.ZeroDensity.LogFree.logFreeNPInstances

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **AREA 3 (round 2)**,  from `Area1` (Burgess, the bound variable of the `Area3`-lambda), a
density input, and the three remaining paper statements `HB10_3_Fcases`, `HBLemma8_4`,
`HBLemma8_8`.

Everything else is discharged inside this area: Table 8 (`Table8Cert*`), `HBTheorem1`
(`HBTheorem1_proof`), `HBLemma9_1` (`HBLemma9_1_proof`), `XYLemma3_8` (`XYLemma3_8_proof`),
`HBTable4` (`HBTable4_proof`), `HBLemma9_4` (`HBLemma9_4_proof`), `HBTable7` (`HBTable7_proof`),
`HBTable9` (from `Area1.1` via `HBTable9_of_burgess`), `HBRepZeroC` (`HBRepZeroC_proof`),
`HB10_3_conclusion` (`HB10_3_conclusion_of_engine_v2` from `HBLemma10_3_engine_proof` and the
certificate `Lemma10_3Cert`), `RectCertC`/`RectCertS` (`OffAxis/RectCert{C,S}_proof.lean`) — hence
`HBOffAxis` (`hbOffAxis_of_rect`). -/
theorem linnikContract2_Area3_of_engine
    :
    Work.LinnikContract2.Area3 :=
  fun h1 => linnikContract2_ZeroFreeCert_of_props (hbOffAxis_of_rect_logFreeNP Work.ZeroFreeTables.OffAxis.RectCertC_proof Work.ZeroFreeTables.OffAxis.RectCertS_proof (by norm_num) (by norm_num) Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four)
    HBLemma9_1_proof Table8Cert Table8CertExt HBTheorem1_proof XYLemma3_8_proof HBTable4_proof HBLemma9_4_proof
    (HBTable9_of_burgess h1.1) (HB10_3_conclusion_of_engine_v2 HBLemma10_3_engine_proof HB10_3_Fcases_proof Lemma10_3Cert) HBTable7_proof HBLemma8_4_proof HBLemma8_8_proof HBRepZeroC_proof

/-- The same, with the off-axis input `HBOffAxis` supplied directly (the interface of the
previous round; `hbOffAxis_of_rect` proves `HBOffAxis` from the height-`L` certificates). -/
theorem linnikContract2_Area3_of_hbOffAxis (hOff : HBOffAxis)
    :
    Work.LinnikContract2.Area3 :=
  fun h1 => linnikContract2_ZeroFreeCert_of_props hOff HBLemma9_1_proof Table8Cert Table8CertExt
    HBTheorem1_proof XYLemma3_8_proof HBTable4_proof HBLemma9_4_proof (HBTable9_of_burgess h1.1) (HB10_3_conclusion_of_engine_v2 HBLemma10_3_engine_proof HB10_3_Fcases_proof Lemma10_3Cert) HBTable7_proof HBLemma8_4_proof HBLemma8_8_proof HBRepZeroC_proof

/-- **AREA 3 (round 2)** with the **unified log-free non-principal zero-density estimate**
`Work.ZeroDensity.LogFree.logFreeNP σ₀ c` (`ZeroDensity/JUTILA_UNIFIED_LEAD.md`) in place of
Jutila's all-character `FamDensityEpsRange (4/5) 1 2`.  Area 3 only ever needs non-principal
characters, so this is the sharper hypothesis; the two theorems are otherwise identical. -/
theorem linnikContract2_Area3_of_logFreeNP
    {σ₀ c : ℝ} (hσ0 : σ₀ < 1) (hc : 0 < c)
    (hlog : Work.ZeroDensity.LogFree.logFreeNP σ₀ c)
    :
    Work.LinnikContract2.Area3 :=
  fun h1 => linnikContract2_ZeroFreeCert_of_props
    (hbOffAxis_of_rect_logFreeNP Work.ZeroFreeTables.OffAxis.RectCertC_proof Work.ZeroFreeTables.OffAxis.RectCertS_proof hσ0 hc hlog)
    HBLemma9_1_proof Table8Cert Table8CertExt HBTheorem1_proof XYLemma3_8_proof HBTable4_proof HBLemma9_4_proof
    (HBTable9_of_burgess h1.1) (HB10_3_conclusion_of_engine_v2 HBLemma10_3_engine_proof HB10_3_Fcases_proof Lemma10_3Cert) HBTable7_proof HBLemma8_4_proof HBLemma8_8_proof HBRepZeroC_proof

/-- The same, with the conclusion spelled as the round-2 `ZeroFreeCert` (with `Area1` explicit). -/
theorem linnikContract2_ZeroFreeCert_of_engine
    :
    Work.LinnikContract2.Area1 → Work.LinnikContract2.ZeroFreeCert :=
  fun h1 => linnikContract2_ZeroFreeCert_of_props (hbOffAxis_of_rect_logFreeNP Work.ZeroFreeTables.OffAxis.RectCertC_proof Work.ZeroFreeTables.OffAxis.RectCertS_proof (by norm_num) (by norm_num) Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four)
    HBLemma9_1_proof Table8Cert Table8CertExt HBTheorem1_proof XYLemma3_8_proof HBTable4_proof HBLemma9_4_proof
    (HBTable9_of_burgess h1.1) (HB10_3_conclusion_of_engine_v2 HBLemma10_3_engine_proof HB10_3_Fcases_proof Lemma10_3Cert) HBTable7_proof HBLemma8_4_proof HBLemma8_8_proof HBRepZeroC_proof

/-- The *on-axis* part alone, as this area states it (height-10 wide minimality), from
`Area1.1 = LBound13`. -/
theorem ZeroFreeCert_of_engine (h1 : Work.LinnikContract2.Area1)
    :
    ZeroFreeCert :=
  zeroFreeCert_of_props HBLemma9_1_proof Table8Cert Table8CertExt HBTheorem1_proof XYLemma3_8_proof HBTable4_proof HBLemma9_4_proof
    (HBTable9_of_burgess h1.1) (HB10_3_conclusion_of_engine_v2 HBLemma10_3_engine_proof HB10_3_Fcases_proof Lemma10_3Cert) HBTable7_proof HBLemma8_4_proof HBLemma8_8_proof HBRepZeroC_proof

/-- The same in the shape `Area1 → ZeroFreeCert` (this area's `Area3`). -/
theorem Area3_of_engine
    :
    Area3 Work.LinnikContract.Area1 :=
  fun h1 => ZeroFreeCert_of_engine h1

/-- **HB Table 8 as printed** (the paper's own `Prop`) from the `P₃` engine `HBLemma9_1` and the
certificates.  (The hypothesis of `HBTable8` is HB's §6 minimality, `IsMin1WideAt 10`.) -/
theorem HBTable8_printed : HBTable8 :=
  HBTable8_of_engine HBLemma9_1_proof Table8CertPrinted Table8CertExtPrinted HBRepZeroC_proof

end Work.ZeroFreeTables
