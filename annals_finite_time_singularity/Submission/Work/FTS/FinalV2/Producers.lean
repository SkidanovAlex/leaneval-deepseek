import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.Assembly
import Submission.Work.FTS.StrongEps.GlobalStrong2Prime
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.RegExportIface.Producers
import Submission.Work.FTS.StreamBdryIface.Producers
import Submission.Work.FTS_StreamBdry.hid9_of_parts_proved
import Submission.Work.FTS_FinalLeaves.All
import Submission.Work.FTS_MuLipC.Main
import Submission.Work.FTS_EllLimOK.MainHFinal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.Producers` — the OPEN producers of `Inputs'` (curric-46 lead install, 2026-10-10)

Every theorem here was installed `:= by sorry`: one named statement per open conjunct (or per
research-free feed), so the fleet can be dispatched on it. 2026-10-10: `kernel_exists`, `sup5'`,
`mu6'`, `psiCan_C3`, `merPsi_C3`, `sol_fire`, `profDerivData_min` are now closed by the
`Work.FTS_FinalLeaves.*_proved` deliveries (`FTS_FinalLeaves/All`). Statements from
`cbc/fts_final_redesign.lean` §Producers, plus the conjuncts the design left as `Inputs'` fields
only ((0), (1)+(1a′), (1c), (7′), (9′)). Conjunct (3) is the existing
`StrongEps.EpsUniform_of_data` (E4) and is not restated. The proved (8′) reduction is
`FinalV2.Mer8.mer8'`; the wire is `FinalV2.WireSkeleton`.

| conjunct | producer here | owner (design md) |
|---|---|---|
| (0) | `kernel_exists` | Final leaf, research none |
| (1)+(1a′) | `core1_1a3` | FTS_EllLimOK (order-3 `LocalBound`, small α, `ClosedUniq`) |
| (1c) | `muLipC_pExp` | FTS_MuLamOK |
| (4′) | `global_strong2'` — PROVED glue (10-11) from `StrongEps.exists_limG` (E5 leaf) | StrongEps |
| (5′) | `sup5'` ← `classC_sup_le` | Final leaves (`classC_sup_le` = shared RegExport sup lemma) |
| (6′) | `mu6'` | Final leaf |
| (7″) | `regPkg7'` — PROVED from `RegExportIface.regExport` + `mu6'` + `hES` (`ESlotBd`, from `FinalV2.ESlot` in the wire) | FTS_RegExport (`RegExportIface/Producers.lean`) |
| (8′) | `sol_fire`, `psiCan_C3`, `profDerivData_min` (feeds of `mer8'`) | Final leaves |
| (9″) | `hid9''` — PROVED from `StreamBdryIface.hid9''_of_parts` | BSIdent port + FTS_StreamBdry (`StreamBdryIface/Producers.lean`) |
| (10′) | `merPsi_C3` ← `psiCan_C3` | Final leaf |
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **(0) producer**: a smooth mollifier kernel (`ContDiffBump.normed` on `ℝ×ℝ`, outer radius
`≤ 1/√2` for the Euclidean support clause; REVIEW §5). Research none. -/
theorem kernel_exists : ∃ ρ : ℝ × ℝ → ℝ, Work.FTS.StrongEps.IsSmoothKernel ρ := by
  exact Work.FTS_FinalLeaves.kernel_exists_proved

/-- **(1)+(1a′) producer**: `FTS_EllLimOK.core1_1a_of_compact_uniq` with `EllLimOK` strengthened
to the order-3 `EllLimOK3` (`LocalBound` to order 4, `ClosedE` to order 3, `ClosedCompact`/
`ClosedUniq` restated at small α). Input: the class-C layer `ExistsEllSolC` (route (b):
`existsEllSolC_of_threshold` of A2). Owner FTS_EllLimOK. -/
theorem core1_1a3 (hb : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ g : Fn,
      Work.FTS.ClassC.ClassC α g → ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      EllLimOK3 (pExp α) E :=
  Work.FTS_EllLimOK.core1_1a3_proved hb  -- curric-46 lead 10-11: delivered by FTS_EllLimOK

/-- **(1c) producer**: the class-C Lipschitz bound of the modulation, in the shape of
`FTS_MuLamOK.MuLamOK_proved_pExp` (same estimates applied to `f - f'`; `ClassC` is a subspace and
`E` is linear). Owner FTS_MuLamOK. -/
theorem muLipC_pExp {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn →ₗ[ℝ] Fn},
      Work.FTS.VocabO2.StarPkgo2 (pExp α) Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC (pExp α) f →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce f (E f)) →
      MuLipC (pExp α) C₀ Φs E :=
  Work.FTS_MuLipC.muLipC_pExp (Ce := Ce) (Cs := Cs) hC₀  -- curric-46 lead 10-10: delivered by FTS_MuLipC


/-- (4′) producer: `global_strong2` with the enriched output (owner StrongEps).
curric-46 lead install 2026-10-11 (C1–C5 ruling, `cbc/fts_strongeps_c1c5_ruling.md` §7 item 6,
review F2/F5): hypothesis (1a) is now `EllLimOK3` itself (no `toEllLimOK` weakening), α₂ is chosen
after `C₀, Ce, Cs`, and the body is `StrongEps.global_strong2'_proved` = E6
(`global_strong2_of_limG`, proved) from the E5 leaf `StrongEps.exists_limG`. -/
theorem global_strong2' {C₀ Ce Cs : ℝ} : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ αG ∈ Set.Ioc 0 α₂,
    ∀ {K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC αG u →
      Work.FTS.VocabO.EllPkgGo αG Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK αG 6 Ce u (E u)) →
    EllLimOK3 αG E → StarPkgo2 αG Cs Φs →
    Work.FTS.StrongEps.MuLamOK αG C₀ Φs E →
    Work.FTS.StrongEps.EpsUniformMem αG ρ Φs E g₀ C₀ K →
      ∃ g : Fam, Sol αG Φs E g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧ DynOK' αG C₀ Φs E g :=
  Work.FTS.StrongEps.global_strong2'_proved

/-- (5′) feed: the interior `ℋ⁴ → sup` bound on the class C (port of `H2.mixed_supAbsO_le`
from `SmoothQuad` to `ClassC`). Owner: Final (new leaf), research-low. -/
theorem classC_sup_le (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ f : Fn, Work.FTS.ClassC.ClassC α f → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  sorry

/-- (5′) producer from `classC_sup_le` + `LimApprox` + `RegPkgMin.vanish` (+ `extG = 0` on `z ≤ 0`).
Research-none. -/
theorem sup5' (hα : 0 < α) (hα1 : α ≤ 1) {g : Fam} (hOK : DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |extG g z θ τ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
  exact Work.FTS_FinalLeaves.sup5'_proved hα hα1 hOK

/-- (6′) producer from (1b) `MuLamOK`, (1c) `MuLipC` and `LimApprox` (bound: `le_of_tendsto`;
Lipschitz in τ: `MuLipC` × the `ℋ⁴`-Lipschitz modulus, then the limit; Hölder from Lipschitz on
`[0,S]`). Research-none. -/
theorem mu6' (hα : 0 < α) (hα1 : α ≤ 1) (hML : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hLip : MuLipC α C₀ Φs E) {g : Fam} (hOK : DynOK' α C₀ Φs E g) :
    (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
    ContinuousOn (Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g) (Set.Ici 0) ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ τ ∈ Icc (0 : ℝ) S, ∀ τ' ∈ Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ β := by
  exact Work.FTS_FinalLeaves.mu6_proved hα hα1 hML hLip hOK

/-- (13′), internal: `C³` of the stream-function slices on `Qd`, from (1a′) `EllLimOK3`,
`StarPkgo2.smooth` and `LimApprox`. Research-none. Consumed by (8′) and (10′). -/
theorem psiCan_C3 (hEL : EllLimOK3 α E) (hStar : StarPkgo2 α Cs Φs) {g : Fam}
    (hOK : DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd := by
  exact Work.FTS_FinalLeaves.psiCan_C3_proved hEL hStar hOK

/-- (10′) producer: `C³` port of `BSIdent.Defs.contDiffAt_merPsi_slice` for the odd extension
(`psiFire` = `PsiCan` near every point with `θ > 0`, and `= -PsiCan(·,-θ)` near `θ < 0`).
Research-none. -/
theorem merPsi_C3 {g : Fam} {A B : ℝ → ℝ} {C : PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
        Work.FTS.MeridianDyn.merPsi α A B (psiFire Φs E g) C p.1 p.2 t) (r, z) := by
  exact Work.FTS_FinalLeaves.merPsi_C3_proved hC3 hB

/-- (8′) feed: the dynamics transported to `(psiFire, extG g)` — every term of `dynLin`/`dynRHS`/
`muDyn`/the law at a point of `Qd` depends on `Φ` and `g` only through their values on `Qd`
(pointwise derivatives at `Qd` points; integrals over `Iz ×ˢ Iθ`, which differ from `Qd` by a
null set). Research-none. -/
theorem sol_fire {g : Fam} (hSol : Sol α Φs E g) :
    IsDynGSolWith (IsBslSolPos α) α (psiFire Φs E g) (extG g) ∧
    ∀ τ : ℝ, 0 ≤ τ → Work.FTS.Galerkin.muDyn α (psiFire Φs E g) (extG g) τ
      = Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ := by
  exact Work.FTS_FinalLeaves.sol_fire_proved hSol

/-- (8′) feed: `ProfDerivData` from `RegPkgMin` + interior `C²` of `Φ` (port of
`MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed` from `Galerkin.RegPkg` to `RegPkgMin`).
Research-none. -/
theorem profDerivData_min {Φ g : Fam} (hmin : Work.FTS.StrongGlobal.RegPkgMin α g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd) :
    Work.FTS.MeridianDyn.ProfDerivData α Φ g := by
  exact Work.FTS_FinalLeaves.profDerivData_min_proved hmin hΦ

/-- **(7″) producer — PROVED (glue)** (RegExport REVIEW F1): `RegPkg'` of the extension of the
SANITISED right-Taylor τ-extension, given the datum `hdat`. It is `RegExportIface.regExport` (the
FTS_RegExport assembly item, whose research producers are in `RegExportIface/Producers.lean`), with
the clock facts from `mu6'` at Hölder exponent `a`, and (2026-10-11, `cbc/fts_hvop_design.md`) the
`V(E slice)` rate slot `hES` (`ESlotBd`, produced by `FinalV2.ESlot.eSlotBd_of_wire` in the wire). -/
theorem regPkg7' {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      EllPkgGo (pExp a) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : EllLimOK3 (pExp a) E) (hML : Work.FTS.StrongEps.MuLamOK (pExp a) C₀ Φs E)
    (hLip : MuLipC (pExp a) C₀ Φs E) (hStar : StarPkgo2 (pExp a) Cs Φs)
    (hES : ∀ g : Fam, DynOK' (pExp a) C₀ Φs E g → Work.FTS_RegExport.ESlotBd a Cs g ⇑E) :
    ∀ g : Fam, Sol (pExp a) Φs E g → DynOK' (pExp a) C₀ Φs E g →
      (∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp a) L β z θ) →
      ∀ S : ℝ, 0 < S →
        RegPkg' a S (ampA (maxMu (pExp a) (PsiCan Φs E g) g))
          (ampB (maxMu (pExp a) (PsiCan Φs E g) g)) (extG (gS a (tauExt g))) := by
  intro g hSol hOK hdat S hS
  have hαG : 0 < pExp a := Work.FTS.Regularity.pExp_pos ha
  have hαG1 : pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  obtain ⟨hb, hc, hh⟩ := mu6' hαG hαG1 hML hLip hOK
  exact Work.FTS.RegExportIface.regExport ha ha13 hEll hEL hStar hSol hOK hdat
    ⟨hb, hc, hh a ha (by linarith)⟩ (hES g hOK) S hS

/-- **(9″) producer — PROVED (glue)** (StreamBdry REVIEW FIX-A; replaces `hid9'`, false as stated:
no support datum). Biot–Savart identification for the firing pair `(extG g, psiFire)`, given the
firing family's `RegPkg'` (`hreg`, the adapter's `hRegG`) and `hG : G = g` on the open quadrant
(`G := gS a g` in the adapter). NO growth inputs. It is `StreamBdryIface.hid9''_of_parts` (the
assembly of the BSIdent port P1/P2 and the StreamBdry leaves SB0–SB6, `StreamBdryIface/Producers`). -/
theorem hid9'' {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      EllPkgGo (pExp a) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : EllLimOK3 (pExp a) E) (hStar : StarPkgo2 (pExp a) Cs Φs) :
    ∀ (g G : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      Sol (pExp a) Φs E g → DynOK' (pExp a) C₀ Φs E g →
      ClockData (pExp a) (PsiCan Φs E g) g A B C →
      (∀ S : ℝ, 0 < S → RegPkg' a S A B (extG G)) →
      (∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega a A B (extG g) C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (pExp a) A B (psiFire Φs E g) C r z t) x :=
  Work.FTS_StreamBdry.hid9''_of_parts_proved (C₀ := C₀) ha ha13 hEll hEL hStar

end Work.FTS.FinalV2
