import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.RegExportIface.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegExportIface.Defs` — the interface of FTS_RegExport (curric-46 lead install, 2026-10-10)

Design `cbc/fts_regexport_design.md`/`.lean`, corrected by `cbc/fts_regexport_design_REVIEW.md`
(F2, F3). NEW files only: `RegPkgGal` (frozen), `FireFix` and `FinalV2.Sanitize` are untouched.

* `psiQ`, `psiR` — **REVIEW F2.2/F2.3**: the stream function fed to R5/R7 (not to the firing).
  On `z > 0` it is the reflection of `PsiCan` that is ODD across `θ = 0` and ODD across `θ = π/2`
  (`psiR(π−θ) = −PsiCan(θ)`), so that `Φ̃ = psiR − Θ` is honestly `C¹` across the axis (`Θ` is odd
  about `π/2`); on `z ≤ 0` it is `Θ(F)` itself, so `Φ̃ ≡ 0` there (no Hamel junk at `z = 0`).
  Callers pass the right-Taylor family `G = tauExt g`, so `PsiCan Φs E G` is determined at `τ < 0`.
* `phiTil`, `Vz7`, `Vθ7`, `cs7` — **REVIEW F2.1**: the transport coefficients of `(E)` with the
  `Θ` part in CLOSED form (`2αG·Vop Θ = L12(F)·c2m`, `−2·Rop Θ = −L12(F)/αG + sin²θ·FK(F)`,
  identities on `cos θ ≠ 0`), so that they are continuous up to `θ = π/2` (Lean's `tan(π/2) = 0`
  and `x/cos(π/2) = 0` make the literal `Vop/Rop` of `Θ` jump there):
  `Vz7 = (1−μ) + L12(F)·c2m + 2αG·Vop Φ̃`, `Vθ7 = 2·Uop αG Φ`,
  `cs7 = (1+μ) − L12(F)/αG + sin²θ·FK(F) − 2·Rop αG Φ̃`, with `F = Ftau αG G τ`, `Φ̃ = Φ − Θ(F)`.
* `R1Block`, `R7Block`, `GalMin'` — the re-cut bundle (design §2, verbatim): `hRQ → hIS`.
* `edgeExt` (§4, 2026-10-11 repair `cbc/fts_velpkg_fix.md` + REVIEW) — the angular EDGE EXTENSION
  of a coefficient (`V` on `0 < θ < π/2`, its one-sided limits at `θ ≤ 0`, `θ ≥ π/2`). The R7 block
  is fed `edgeExt Vz7`, `Vθ7`, `edgeExt cs7`, so the frozen closed-box `R7Block.hVjoint/hcscont`
  follow from OPEN-quadrant data (`R7Block_edgeExt`, `R7Block_of_velPkgF`), with no axis value.
* `VelPkg` — RX-VP's package, with **REVIEW F3a** `vanish0` (O(z) vanishing of the `Φ̃`
  coefficients and of `FK(g)`, `L12(g)` at `z = 0`). REPAIRED 10-11: `bnd`/`vz0`/`cont` on the
  OPEN angular interval (= the area's `VelPkgOpen`), the former F2.2 axis clause `∂_θΦ̃(π/2) = 0`
  DROPPED (it is false for the construction: `∂_θΨ(z,π/2)` is the axial strain, and the slope
  condition (★) is generically false at `O(α)`), and the new clause `thLip`, RESTATED 10-11
  (`cbc/fts_thlip_o1_plans.md` ITEM A) as the Hölder clause `thHol` (§4C `ThHol`,
  `continuousOn_edgeExt_hol`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.RegExportIface

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG extG_of_nonpos extG_of_pos RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

/-! ## §1 The R5/R7 stream function `psiR` (REVIEW F2.2, F2.3) -/

/-- The quadrant reflection of `Ψ` that is odd across `θ = 0` and odd across `θ = π/2`
(on `(−π/2, π)`; `0` at `θ = 0, π/2` and outside `(−π/2, π)`). -/
def psiQ (Ψ : Fam) : Fam := fun z θ τ =>
  if 0 < θ ∧ θ < π / 2 then Ψ z θ τ
  else if π / 2 < θ ∧ θ < π then - Ψ z (π - θ) τ
  else if -(π / 2) < θ ∧ θ < 0 then - Ψ z (-θ) τ
  else 0

/-- **The stream function fed to `R5Parts`/R7** (REVIEW F2): odd/odd reflection of `PsiCan Φs E G`
on `z > 0`, and the singular part `Θ(F)` (`F = F_* + gS α G`) on `z ≤ 0`. -/
def psiR (α : ℝ) (Φs : Fn) (E : Fn → Fn) (G : Fam) : Fam := fun z θ τ =>
  if 0 < z then psiQ (PsiCan Φs E G) z θ τ
  else Work.Construction.Theta (pExp α) (Work.Construction.Ftau (pExp α) (gS α G) τ) z θ

theorem psiR_of_mem {α : ℝ} {Φs : Fn} {E : Fn → Fn} {G : Fam} {z θ τ : ℝ} (hz : 0 < z)
    (h0 : 0 < θ) (h1 : θ < π / 2) : psiR α Φs E G z θ τ = PsiCan Φs E G z θ τ := by
  simp [psiR, psiQ, hz, h0, h1]

theorem psiR_of_nonpos {α : ℝ} {Φs : Fn} {E : Fn → Fn} {G : Fam} {z θ τ : ℝ} (hz : z ≤ 0) :
    psiR α Φs E G z θ τ
      = Work.Construction.Theta (pExp α) (Work.Construction.Ftau (pExp α) (gS α G) τ) z θ := by
  simp [psiR, not_lt.mpr hz]

theorem psiR_zero {α : ℝ} {Φs : Fn} {E : Fn → Fn} {G : Fam} {z τ : ℝ} (hz : 0 < z) :
    psiR α Φs E G z 0 τ = 0 := by
  have h2 : ¬ (π / 2 < 0) := by linarith [Real.pi_pos]
  simp [psiR, psiQ, hz, h2]

theorem psiR_pi_div_two {α : ℝ} {Φs : Fn} {E : Fn → Fn} {G : Fam} {z τ : ℝ} (hz : 0 < z) :
    psiR α Φs E G z (π / 2) τ = 0 := by
  have h2 : ¬ (π / 2 < 0) := by linarith [Real.pi_pos]
  simp [psiR, psiQ, hz, h2]

/-! ## §2 The transport coefficients of `(E)` in closed form (REVIEW F2.1) -/

/-- `Φ̃(τ) = Φ(τ) − Θ(F(τ))`, `F(τ) = F_* + G(τ)`. -/
def phiTil (αG : ℝ) (G Φ : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil αG (Work.Construction.Ftau αG G τ) (slice Φ τ)

/-- `Vz7 = (1−μ) + L12(F)·c2m + 2αG·Vop Φ̃` (`= (1−μ) + 2αG·Vop Φ` on the open quadrant). -/
def Vz7 (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  (1 - μ τ) + Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ
    + 2 * αG * Work.Construction.Vop (phiTil αG G Φ τ) z θ

/-- `Vθ7 = 2·Uop αG Φ` (unchanged; `Uop Θ` has no `tan`/`1/cos`). -/
def Vθ7 (αG : ℝ) (Φ : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  2 * Work.Construction.Uop αG (slice Φ τ) z θ

/-- `cs7 = (1+μ) − L12(F)/αG + sin²θ·FK(F) − 2·Rop αG Φ̃` (`= (1+μ) − 2·Rop αG Φ` on the open
quadrant). -/
def cs7 (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  (1 + μ τ) - Work.Construction.L12 (Work.Construction.Ftau αG G τ) z / αG
    + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau αG G τ) z
    - 2 * Work.Construction.Rop αG (phiTil αG G Φ τ) z θ

/-- The weight of the `St1` class: `ω = z²Γ(θ)/(1+z)²`. -/
def ω (α z θ : ℝ) : ℝ := z ^ 2 * Work.FTS.Regularity.Gamma α θ / (1 + z) ^ 2

/-- **The clock hypothesis of the RX producers** (RXT leaf plan F-A, `cbc/fts_rxt_install.md`):
`|μ| ≤ 1/2` on `τ ≥ 0` (gives `hne : 1 + muDyn ≠ 0` of `MeridianDyn.DynEqF_of_isDynEqOn`, and the
`τ`-uniform bounds of `Vz7`/`cs7`) and continuity of `μ` on `[0,∞)` (the `τ`-continuity of the
coefficients: `VelPkg.cont`, `R7Block.hVjoint/hcscont`, and RX-T0's joint `C¹`). Neither follows
from `Sol ∧ DynOK'`; `regExport` gets it from its `hclock` (`ClockBd.of_clock`). -/
def ClockBd (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
    ContinuousOn (Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g) (Set.Ici 0)

/-- `regExport`'s clock hypothesis (bound ∧ continuity ∧ Hölder, from `mu6'`) supplies `ClockBd`. -/
theorem ClockBd.of_clock {α : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {P : Prop}
    (h : (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g) (Set.Ici 0) ∧ P) :
    ClockBd α Φs E g :=
  ⟨h.1, h.2.1⟩

/-! ## §3 The re-cut bundle (design §2, verbatim) -/

/-- The nine R1 fields of `GalMin`, verbatim (instantiated at `gS α (tauExt g)` they are
right-sided data of `g` at `τ = 0`; producer `r1Block`). -/
structure R1Block (α S : ℝ) (g : Fam) : Prop where
  hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  hd1z : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
    Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))

/-- The R7 transport fields of `GalMin`, verbatim (producer `r7Block`). -/
structure R7Block (α S : ℝ) (g : Fam) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ) (a b c Lz7 : ℝ) : Prop where
  hFjoint : ContDiffOn ℝ 1
    (fun p : ℝ × ℝ × ℝ => Work.FTS.Regularity.profFull α (extG g) p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
    (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
    (Set.prod (Set.Ioi Lz7) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
    HasDerivAt (fun s => Work.FTS.Regularity.profFull α (extG g) z θ s)
      (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG g) z θ τ) z θ
        + Vθ z θ τ * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α (extG g) z θ τ) z θ
        + cs z θ τ * Work.FTS.Regularity.profFull α (extG g) z θ τ)) τ
  hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ
  hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a
  hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b
  hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0
  hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0
  hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c
  hInit : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
    Work.FTS.Regularity.profFull α (extG g) z θ 0 = 0
  hLz7 : 0 ≤ Lz7
  ha : 0 ≤ a
  hb : 0 ≤ b
  hc : 0 ≤ c

/-- **THE RE-CUT BUNDLE.** `GalMin` with the unproducible `hRQ` (`SmoothQuad` = `C^∞` on `z > −1`)
replaced by `hIS`, the interior order-≤2 sup bound on the open quadrant (all that
`Der.sup_extG(_ext)`, `Der.sup2_extG(_ext)` extract from `RegQ`; `C⁴` on `Q0` is `hmin.c4`). The
angular endpoint continuity (old `Der.endpoint_cont` from `BdryTraces`) now comes from
`hSt1.hhθ`. Every other field is verbatim. -/
structure GalMin' (α S : ℝ) (g : Fam) (m : ℝ → ℝ) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ)
    (a b c Lz7 : ℝ) : Prop extends R1Block α S g, R7Block α S g Vz Vθ cs a b c Lz7 where
  hα : 0 < α
  hα13 : α ≤ 1 / 3
  hS : 0 < S
  hmin : Work.FTS.RegPkgGal.RegPkgMin (pExp α) g
  hm : ContinuousOn m (Set.Ioo (-1 : ℝ) (S + 1))
  hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |m τ| ≤ 1 / 2
  hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |m τ - m τ'| ≤ L * |τ - τ'| ^ α
  hSt1 : St1Class α S g
  /-- NEW (replaces `hRQ`): the interior order-≤2 sup bound -/
  hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
    0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M
  hHkn : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ ∈ Set.Icc 0 S,
    Work.Spaces.HkNorm (pExp α) 4 (Work.FTS.Regularity.gSlice g τ) ≤ C₀
  hsuppOut : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
    θ ∉ Work.Spaces.Iθ → Work.FTS.Regularity.profFull α (extG g) z θ τ = 0

/-! ## §4 The angular edge extension (repair 2026-10-11, `cbc/fts_velpkg_fix.md`) -/

/-! ### §4A `edgeExt` -/

/-- **Angular edge extension**: `V` on the open quadrant, its one-sided limits at the two edges. -/
def edgeExt (V : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  if θ ≤ 0 then limUnder (𝓝[>] (0:ℝ)) (fun t => V z t τ)
  else if π / 2 ≤ θ then limUnder (𝓝[<] (π / 2)) (fun t => V z t τ)
  else V z θ τ

theorem edgeExt_of_mem {V : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    edgeExt V z θ τ = V z θ τ := by
  simp [edgeExt, not_le.mpr h0, not_le.mpr h1]

theorem edgeExt_zero (V : ℝ → ℝ → ℝ → ℝ) (z τ : ℝ) :
    edgeExt V z 0 τ = limUnder (𝓝[>] (0:ℝ)) (fun t => V z t τ) := by
  simp [edgeExt]

theorem edgeExt_pi_div_two (V : ℝ → ℝ → ℝ → ℝ) (z τ : ℝ) :
    edgeExt V z (π / 2) τ = limUnder (𝓝[<] (π / 2)) (fun t => V z t τ) := by
  have h : ¬ (π / 2 ≤ 0) := by linarith [Real.pi_pos]
  simp [edgeExt, h]

/-! ### §4B the continuity lemmas -/



/-- the open and the closed angular boxes -/
abbrev Bo (S : ℝ) : Set (ℝ × ℝ × ℝ) := Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) (π / 2) ×ˢ Icc (0:ℝ) S
abbrev Bc (S : ℝ) : Set (ℝ × ℝ × ℝ) := Ioi (0:ℝ) ×ˢ Icc (0:ℝ) (π / 2) ×ˢ Icc (0:ℝ) S

/-- the open box is a relative neighbourhood (in the closed box) of each of its points -/
theorem Bo_mem_nhdsWithin {S : ℝ} {p : ℝ × ℝ × ℝ} (hp : p ∈ Bo S) : Bo S ∈ 𝓝[Bc S] p := by
  refine mem_nhdsWithin.mpr ⟨{q | q.2.1 ∈ Ioo (0:ℝ) (π / 2)}, ?_, hp.2.1, ?_⟩
  · exact isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)
  · intro q hq
    exact ⟨hq.2.1, hq.1, hq.2.2.2⟩

/-- coordinate bounds from a product distance -/
theorem dist3_le {p q : ℝ × ℝ × ℝ} :
    |q.1 - p.1| ≤ dist q p ∧ |q.2.1 - p.2.1| ≤ dist q p ∧ |q.2.2 - p.2.2| ≤ dist q p := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.dist_eq]; exact (le_max_left _ _).trans (le_of_eq (Prod.dist_eq).symm)
  · rw [← Real.dist_eq]
    exact ((le_max_left _ _).trans (le_of_eq (Prod.dist_eq).symm)).trans
      ((le_max_right _ _).trans (le_of_eq (Prod.dist_eq).symm))
  · rw [← Real.dist_eq]
    exact ((le_max_right _ _).trans (le_of_eq (Prod.dist_eq).symm)).trans
      ((le_max_right _ _).trans (le_of_eq (Prod.dist_eq).symm))

theorem dist3_mid_le {z z0 θ θ0 t τ τ0 : ℝ} :
    dist ((z, t, τ) : ℝ × ℝ × ℝ) (z0, t, τ0) ≤ dist ((z, θ, τ) : ℝ × ℝ × ℝ) (z0, θ0, τ0) := by
  simp only [Prod.dist_eq, dist_self]
  exact max_le_max le_rfl (max_le_max (dist_nonneg) le_rfl)


/-- **Vanishing-edge continuity** (for `Vθ7`): open-box continuity, `|V| ≤ M sin 2θ` and zero
values at `θ = 0, π/2` make `V` continuous on the CLOSED box. -/
theorem continuousOn_closed_of_sin {V : ℝ → ℝ → ℝ → ℝ} {S M : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ × ℝ => V p.1 p.2.1 p.2.2) (Bo S))
    (hM : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      |V z θ τ| ≤ M * Real.sin (2 * θ))
    (hend : ∀ z τ, 0 < z → τ ∈ Icc (0:ℝ) S → V z 0 τ = 0 ∧ V z (π / 2) τ = 0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => V p.1 p.2.1 p.2.2) (Bc S) := by
  have hpi : (0:ℝ) < π / 2 := by linarith [Real.pi_pos]
  -- a global bound on the closed box
  have hall : ∀ q ∈ Bc S, |V q.1 q.2.1 q.2.2| ≤ |M| * Real.sin (2 * q.2.1) := by
    rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩
    simp only [mem_Ioi] at hz
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    dsimp only at hθ hτ ⊢
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0; rw [(hend z τ hz hτ).1, abs_zero]; exact mul_nonneg (abs_nonneg _) hs
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1; rw [(hend z τ hz hτ).2, abs_zero]; exact mul_nonneg (abs_nonneg _) hs
    exact (hM z θ τ hz h0 h1 hτ).trans (mul_le_mul_of_nonneg_right (le_abs_self M) hs)
  rintro ⟨z0, θ0, τ0⟩ ⟨hz0, hθ0, hτ0⟩
  simp only [mem_Ioi] at hz0
  have hedge : ∀ e : ℝ, Real.sin (2 * e) = 0 → θ0 = e →
      ContinuousWithinAt (fun p : ℝ × ℝ × ℝ => V p.1 p.2.1 p.2.2) (Bc S) (z0, θ0, τ0) := by
    intro e hse he
    subst he
    have hv : V z0 θ0 τ0 = 0 := by
      have := hall (z0, θ0, τ0) ⟨hz0, hθ0, hτ0⟩
      simp only [hse, mul_zero] at this
      exact abs_nonpos_iff.mp this
    show Tendsto (fun p : ℝ × ℝ × ℝ => V p.1 p.2.1 p.2.2) (𝓝[Bc S] (z0, θ0, τ0))
      (𝓝 (V z0 θ0 τ0))
    rw [hv]
    have hb : Tendsto (fun q : ℝ × ℝ × ℝ => |M| * Real.sin (2 * q.2.1)) (𝓝[Bc S] (z0, θ0, τ0))
        (𝓝 0) := by
      have : Continuous (fun q : ℝ × ℝ × ℝ => |M| * Real.sin (2 * q.2.1)) := by fun_prop
      have h2 := (this.tendsto (z0, θ0, τ0)).mono_left (nhdsWithin_le_nhds (s := Bc S))
      simpa [hse] using h2
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [Real.norm_eq_abs]
    exact hall q hq
  rcases eq_or_lt_of_le hθ0.1 with h0 | h0
  · exact hedge 0 (by simp) h0.symm
  rcases eq_or_lt_of_le hθ0.2 with h1 | h1
  · exact hedge (π / 2) (by rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) h1
  have hmem : ((z0, θ0, τ0) : ℝ × ℝ × ℝ) ∈ Bo S := ⟨hz0, ⟨h0, h1⟩, hτ0⟩
  exact (hc _ hmem).mono_of_mem_nhdsWithin (Bo_mem_nhdsWithin hmem)

/-! ### §4C the Hölder edge extension (install 2026-10-11, `cbc/fts_thlip_o1_plans.md` ITEM A,
Part 0 of `cbc/fts_thlip_o1_plans.lean`, verbatim): `VelPkg.thHol` replaces `thLip`. -/

/-- small radius with `K r^β < ε` -/
theorem exists_small_rpow {K β ε : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ π / 4 ∧ K * r ^ β < ε := by
  set r : ℝ := min (π / 4) ((ε / (2 * (K + 1))) ^ (1 / β)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨r, hr0, min_le_left _ _, ?_⟩
  have hrβ : r ^ β ≤ ε / (2 * (K + 1)) := by
    calc r ^ β ≤ ((ε / (2 * (K + 1))) ^ (1 / β)) ^ β :=
          Real.rpow_le_rpow hr0.le (min_le_right _ _) hβ.le
      _ = ε / (2 * (K + 1)) := by
          rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one]
  calc K * r ^ β ≤ K * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hrβ hK
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- a `β`-Hölder function on `(0,π/2)` has a right limit at `0`, within `K t^β` -/
theorem hol_edge_left {f : ℝ → ℝ} {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hf : ∀ t ∈ Ioo (0:ℝ) (π / 2), ∀ s ∈ Ioo (0:ℝ) (π / 2), |f t - f s| ≤ K * |t - s| ^ β) :
    ∀ t ∈ Ioo (0:ℝ) (π / 2), |f t - limUnder (𝓝[>] (0:ℝ)) f| ≤ K * t ^ β := by
  have hpi : (0:ℝ) < π / 2 := by positivity
  have hc : Cauchy (map f (𝓝[>] (0:ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨r, hr0, hr1, hKr⟩ := exists_small_rpow hK hβ hε
    refine ⟨f '' Ioo 0 r, image_mem_map (Ioo_mem_nhdsGT hr0), ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq]
    have hxy : |x - y| ≤ r := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    calc |f x - f y| ≤ K * |x - y| ^ β :=
          hf x ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩ y ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
      _ ≤ K * r ^ β := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hxy hβ.le) hK
      _ < ε := hKr
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hc
  rw [hL.limUnder_eq]
  intro t ht
  have h1 : Tendsto (fun s => |f t - f s|) (𝓝[>] (0:ℝ)) (𝓝 |f t - L|) :=
    (tendsto_const_nhds.sub hL).abs
  refine le_of_tendsto h1 ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
  have hts : |t - s| ≤ t := by rw [abs_of_pos (by linarith [hs.2])]; linarith [hs.1]
  calc |f t - f s| ≤ K * |t - s| ^ β := hf t ht s ⟨hs.1, by linarith [hs.2, ht.2]⟩
    _ ≤ K * t ^ β := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) hts hβ.le) hK

/-- a `β`-Hölder function on `(0,π/2)` has a left limit at `π/2`, within `K (π/2 − t)^β` -/
theorem hol_edge_right {f : ℝ → ℝ} {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hf : ∀ t ∈ Ioo (0:ℝ) (π / 2), ∀ s ∈ Ioo (0:ℝ) (π / 2), |f t - f s| ≤ K * |t - s| ^ β) :
    ∀ t ∈ Ioo (0:ℝ) (π / 2), |f t - limUnder (𝓝[<] (π / 2)) f| ≤ K * (π / 2 - t) ^ β := by
  have hpi : (0:ℝ) < π / 2 := by positivity
  have hc : Cauchy (map f (𝓝[<] (π / 2))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨r, hr0, hr1, hKr⟩ := exists_small_rpow hK hβ hε
    refine ⟨f '' Ioo (π / 2 - r) (π / 2), image_mem_map (Ioo_mem_nhdsLT (by linarith)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq]
    have hxy : |x - y| ≤ r := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    calc |f x - f y| ≤ K * |x - y| ^ β :=
          hf x ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩ y ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩
      _ ≤ K * r ^ β := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hxy hβ.le) hK
      _ < ε := hKr
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hc
  rw [hL.limUnder_eq]
  intro t ht
  have h1 : Tendsto (fun s => |f t - f s|) (𝓝[<] (π / 2)) (𝓝 |f t - L|) :=
    (tendsto_const_nhds.sub hL).abs
  refine le_of_tendsto h1 ?_
  filter_upwards [Ioo_mem_nhdsLT ht.2] with s hs
  have hts : |t - s| ≤ π / 2 - t := by
    rw [abs_of_neg (by linarith [hs.1])]; linarith [hs.2]
  calc |f t - f s| ≤ K * |t - s| ^ β := hf t ht s ⟨by linarith [hs.1, ht.1], hs.2⟩
    _ ≤ K * (π / 2 - t) ^ β := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) hts hβ.le) hK

/-- the `θ`-Hölder clause (replaces the `θ`-Lipschitz clause of `continuousOn_edgeExt`) -/
def ThHol (V : ℝ → ℝ → ℝ → ℝ) (S β : ℝ) : Prop :=
  ∀ z₀ : ℝ, 0 < z₀ → ∃ K : ℝ, 0 ≤ K ∧ ∃ δ > 0, ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    |z - z₀| < δ → ∀ θ ∈ Ioo (0:ℝ) (π / 2), ∀ θ' ∈ Ioo (0:ℝ) (π / 2),
      |V z θ τ - V z θ' τ| ≤ K * |θ - θ'| ^ β

/-- **Hölder edge-extension continuity** (drop-in for `continuousOn_edgeExt`). -/
theorem continuousOn_edgeExt_hol {V : ℝ → ℝ → ℝ → ℝ} {S β : ℝ} (hβ : 0 < β)
    (hc : ContinuousOn (fun p : ℝ × ℝ × ℝ => V p.1 p.2.1 p.2.2) (Bo S))
    (hL : ThHol V S β) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => edgeExt V p.1 p.2.1 p.2.2) (Bc S) := by
  have hpi : (0:ℝ) < π / 2 := by linarith [Real.pi_pos]
  rintro ⟨z0, θ0, τ0⟩ ⟨hz0, hθ0, hτ0⟩
  simp only [mem_Ioi] at hz0
  rcases eq_or_lt_of_le hθ0.1 with h0 | h0
  · -- the edge `θ = 0`
    subst h0
    obtain ⟨K, hK0, δ, hδ, hK⟩ := hL z0 hz0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨t1, ht1pos, ht1le, hKt1⟩ := exists_small_rpow hK0 hβ (show 0 < ε / 3 by linarith)
    have ht1lt : t1 < π / 2 := by linarith [Real.pi_pos]
    have hmem1 : ((z0, t1, τ0) : ℝ × ℝ × ℝ) ∈ Bo S := ⟨hz0, ⟨ht1pos, ht1lt⟩, hτ0⟩
    obtain ⟨η1, hη1, hcη⟩ := Metric.continuousWithinAt_iff.mp (hc _ hmem1) (ε / 3) (by linarith)
    refine ⟨min η1 (min δ t1), lt_min hη1 (lt_min hδ ht1pos), ?_⟩
    rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩ hd
    simp only [mem_Ioi] at hz
    dsimp only at hθ hτ ⊢
    obtain ⟨d1, d2, _⟩ := dist3_le (p := ((z0, 0, τ0) : ℝ × ℝ × ℝ)) (q := (z, θ, τ))
    simp only at d1 d2
    have hzδ : |z - z0| < δ := lt_of_le_of_lt d1 (lt_of_lt_of_le hd
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hθt : θ < t1 := by
      have := lt_of_le_of_lt d2 (lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _)))
      rw [sub_zero, abs_of_nonneg hθ.1] at this; exact this
    have hLz := hK τ hτ z hz hzδ
    have hLz0 := hK τ0 hτ0 z0 hz0 (by simpa using hδ)
    have hq : |edgeExt V z θ τ - V z t1 τ| ≤ K * t1 ^ β := by
      rcases eq_or_lt_of_le hθ.1 with hθ0' | hθ0'
      · subst hθ0'
        rw [edgeExt_zero, abs_sub_comm]
        exact hol_edge_left hK0 hβ hLz t1 ⟨ht1pos, ht1lt⟩
      · rw [edgeExt_of_mem hθ0' (lt_trans hθt ht1lt)]
        have := hLz θ ⟨hθ0', lt_trans hθt ht1lt⟩ t1 ⟨ht1pos, ht1lt⟩
        have h5 : |θ - t1| ≤ t1 := by rw [abs_of_neg (by linarith)]; linarith
        exact this.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) h5 hβ.le) hK0)
    have hp : |edgeExt V z0 0 τ0 - V z0 t1 τ0| ≤ K * t1 ^ β := by
      rw [edgeExt_zero, abs_sub_comm]
      exact hol_edge_left hK0 hβ hLz0 t1 ⟨ht1pos, ht1lt⟩
    have hmid : dist (V z t1 τ) (V z0 t1 τ0) < ε / 3 := by
      refine hcη (show ((z, t1, τ) : ℝ × ℝ × ℝ) ∈ Bo S from ⟨hz, ⟨ht1pos, ht1lt⟩, hτ⟩) ?_
      exact lt_of_le_of_lt dist3_mid_le (lt_of_lt_of_le hd (min_le_left _ _))
    rw [Real.dist_eq] at hmid ⊢
    calc |edgeExt V z θ τ - edgeExt V z0 0 τ0|
        ≤ |edgeExt V z θ τ - V z t1 τ| + |V z t1 τ - V z0 t1 τ0|
          + |edgeExt V z0 0 τ0 - V z0 t1 τ0| := by
          have := abs_sub_le (edgeExt V z θ τ) (V z t1 τ) (V z0 t1 τ0)
          have h2 := abs_sub_le (edgeExt V z θ τ) (V z0 t1 τ0) (edgeExt V z0 0 τ0)
          rw [abs_sub_comm (V z0 t1 τ0)] at h2
          linarith
      _ < ε := by linarith
  rcases eq_or_lt_of_le hθ0.2 with h1 | h1
  · -- the edge `θ = π/2`
    subst h1
    obtain ⟨K, hK0, δ, hδ, hK⟩ := hL z0 hz0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨r, hrpos, hrle, hKr⟩ := exists_small_rpow hK0 hβ (show 0 < ε / 3 by linarith)
    have hrlt : r < π / 2 := by linarith [Real.pi_pos]
    set t1 : ℝ := π / 2 - r with ht1
    have ht1pos : 0 < t1 := by rw [ht1]; linarith
    have ht1lt : t1 < π / 2 := by rw [ht1]; linarith
    have hmem1 : ((z0, t1, τ0) : ℝ × ℝ × ℝ) ∈ Bo S := ⟨hz0, ⟨ht1pos, ht1lt⟩, hτ0⟩
    obtain ⟨η1, hη1, hcη⟩ := Metric.continuousWithinAt_iff.mp (hc _ hmem1) (ε / 3) (by linarith)
    refine ⟨min η1 (min δ r), lt_min hη1 (lt_min hδ hrpos), ?_⟩
    rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩ hd
    simp only [mem_Ioi] at hz
    dsimp only at hθ hτ ⊢
    obtain ⟨d1, d2, _⟩ := dist3_le (p := ((z0, π / 2, τ0) : ℝ × ℝ × ℝ)) (q := (z, θ, τ))
    simp only at d1 d2
    have hzδ : |z - z0| < δ := lt_of_le_of_lt d1 (lt_of_lt_of_le hd
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hθt : t1 < θ := by
      have := lt_of_le_of_lt d2 (lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _)))
      rw [abs_of_nonpos (by linarith [hθ.2])] at this
      rw [ht1]; linarith
    have hLz := hK τ hτ z hz hzδ
    have hLz0 := hK τ0 hτ0 z0 hz0 (by simpa using hδ)
    have hq : |edgeExt V z θ τ - V z t1 τ| ≤ K * r ^ β := by
      rcases eq_or_lt_of_le hθ.2 with hθ1' | hθ1'
      · subst hθ1'
        rw [edgeExt_pi_div_two, abs_sub_comm]
        have := hol_edge_right hK0 hβ hLz t1 ⟨ht1pos, ht1lt⟩
        rwa [show π / 2 - t1 = r by rw [ht1]; ring] at this
      · rw [edgeExt_of_mem (lt_trans ht1pos hθt) hθ1']
        have := hLz θ ⟨lt_trans ht1pos hθt, hθ1'⟩ t1 ⟨ht1pos, ht1lt⟩
        have h5 : |θ - t1| ≤ r := by
          rw [abs_of_pos (by linarith)]; rw [ht1]; linarith
        exact this.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) h5 hβ.le) hK0)
    have hp : |edgeExt V z0 (π / 2) τ0 - V z0 t1 τ0| ≤ K * r ^ β := by
      rw [edgeExt_pi_div_two, abs_sub_comm]
      have := hol_edge_right hK0 hβ hLz0 t1 ⟨ht1pos, ht1lt⟩
      rwa [show π / 2 - t1 = r by rw [ht1]; ring] at this
    have hmid : dist (V z t1 τ) (V z0 t1 τ0) < ε / 3 := by
      refine hcη (show ((z, t1, τ) : ℝ × ℝ × ℝ) ∈ Bo S from ⟨hz, ⟨ht1pos, ht1lt⟩, hτ⟩) ?_
      exact lt_of_le_of_lt dist3_mid_le (lt_of_lt_of_le hd (min_le_left _ _))
    rw [Real.dist_eq] at hmid ⊢
    calc |edgeExt V z θ τ - edgeExt V z0 (π / 2) τ0|
        ≤ |edgeExt V z θ τ - V z t1 τ| + |V z t1 τ - V z0 t1 τ0|
          + |edgeExt V z0 (π / 2) τ0 - V z0 t1 τ0| := by
          have := abs_sub_le (edgeExt V z θ τ) (V z t1 τ) (V z0 t1 τ0)
          have h2 := abs_sub_le (edgeExt V z θ τ) (V z0 t1 τ0) (edgeExt V z0 (π / 2) τ0)
          rw [abs_sub_comm (V z0 t1 τ0)] at h2
          linarith
      _ < ε := by linarith
  · have hmem : ((z0, θ0, τ0) : ℝ × ℝ × ℝ) ∈ Bo S := ⟨hz0, ⟨h0, h1⟩, hτ0⟩
    refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ (Bo_mem_nhdsWithin hmem)
    refine (hc _ hmem).congr (fun q hq => ?_) ?_
    · exact edgeExt_of_mem hq.2.1.1 hq.2.1.2
    · exact edgeExt_of_mem h0 h1


/-! ## §5 RX-VP's velocity package (design + REVIEW F3; REPAIRED 2026-10-11) -/

/-- **RX-VP's package** (repaired 10-11, `cbc/fts_velpkg_fix.md` + REVIEW): the velocity of `(E)`
at `(G, Φ)`. `bnd`/`vz0`/`cont` on the OPEN angular interval `0 < θ < π/2` (the area's
`VelPkgOpen`; the old closed-interval versions held at `θ = π/2` only under the false axis-slope
condition (★)), the former F2.2 `axis` clause DROPPED, and the new clause `thHol` (`θ`-Hölder
of `Vz7`, `cs7` up to both edges; was the Lipschitz `thLip` until the 10-11 restatement), which with
`cont` gives closed-box continuity of `edgeExt Vz7`, `edgeExt cs7` (`continuousOn_edgeExt_hol`); `Vθ7` gets it from `bnd` + `vth_ends`
(`continuousOn_closed_of_sin`). Coefficients in closed form (F2.1); `vanish0` (F3a: the `Φ̃`
coefficients `Rop Φ̃`, `Vop Φ̃`, `Uop Φ̃/s2` and their `D_z`, `D_θ`, and `FK(G)`, `L12(G)` vanish
at rate `O(min(z,1))` at `z = 0`). -/
structure VelPkg (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  bnd : ∃ M : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ →
    |Vz7 αG μ G Φ z θ τ| ≤ M ∧ |Vθ7 αG Φ z θ τ| ≤ M * Real.sin (2 * θ) ∧
      |cs7 αG μ G Φ z θ τ| ≤ M
  vz0 : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ → 0 ≤ Vz7 αG μ G Φ z θ τ
  vth_ends : ∀ z τ, 0 < z → 0 ≤ τ → Vθ7 αG Φ z 0 τ = 0 ∧ Vθ7 αG Φ z (π / 2) τ = 0
  c2 : ∀ τ ∈ Icc (0:ℝ) S, ContDiffOn ℝ 2 (Function.uncurry (slice Φ τ)) Work.FTS.EllipticEst.Q0
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Vθ7 αG Φ z θ τ / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Vz7 αG μ G Φ p.1 p.2.1 p.2.2, Vθ7 αG Φ p.1 p.2.1 p.2.2, cs7 αG μ G Φ p.1 p.2.1 p.2.2))
    (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S)
  /-- RESTATED 10-11 (`cbc/fts_thlip_o1_plans.md` ITEM A; was `thLip`): a `θ`-HÖLDER modulus
  (some exponent `β ∈ (0,1]`) of `Vz7` and `cs7` on `(0, π/2)`, uniform in `τ ∈ [0,S]`, locally
  uniform in `z > 0` (`ThHol`); with `cont` it gives the edge limits used by `edgeExt`
  (`continuousOn_edgeExt_hol`). The former Lipschitz clause implies it (`thHol_of_lip`); its `cs7`
  half was research-level, the Hölder modulus follows from the weighted angular part of the
  `ℋ⁴`/`𝒲^{4,∞}` norms (producer `RXVP.thHol_proved`, leaves `FTS_RegExport/THL/Leaves.lean`). -/
  thHol : ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ThHol (Vz7 αG μ G Φ) S β ∧ ThHol (cs7 αG μ G Φ) S β
  vanish0 : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ∀ Q ∈ ({(Work.Construction.Rop αG (phiTil αG G Φ τ)), Work.Construction.Vop (phiTil αG G Φ τ),
        fun z θ => Work.Construction.Uop αG (phiTil αG G Φ τ) z θ / Real.sin (2 * θ)} :
          Set (ℝ → ℝ → ℝ)),
      |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dz Q z θ| ≤ M * min z 1 ∧
        |Work.Spaces.Dth Q z θ| ≤ M * min z 1
  vanishK : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    |Work.Construction.FK (slice G τ) z| + |Work.Construction.L12 (slice G τ) z| ≤ M * min z 1

/-! ## §6 The R7 block from open-quadrant data -/

/-- **`R7Block` for the edge-extended coefficients.**  Every hypothesis lives on the OPEN angular
interval (plus the two `Vθ` end values); the conclusion is the frozen `R7Block` (closed-box
`hVjoint`/`hcscont`) for `(edgeExt Vz, Vθ, edgeExt cs)`. -/
theorem R7Block_edgeExt {α S : ℝ} {g : Fam} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c Lz7 M : ℝ}
    (hFjoint : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.FTS.Regularity.profFull α (extG g) p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hVo : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2)) (Bo S))
    (hcso : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2) (Bo S))
    (hthHol : ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ThHol Vz S β ∧ ThHol cs S β)
    (hVθsin : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ))
    (hVθend : ∀ z τ, 0 < z → τ ∈ Icc (0:ℝ) S → Vθ z 0 τ = 0 ∧ Vθ z (π / 2) τ = 0)
    (hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.prod (Set.Ioi Lz7) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α (extG g) z θ s)
        (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG g) z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth
              (fun z θ => Work.FTS.Regularity.profFull α (extG g) z θ τ) z θ
          + cs z θ τ * Work.FTS.Regularity.profFull α (extG g) z θ τ)) τ)
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b)
    (hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c)
    (hInit : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Regularity.profFull α (extG g) z θ 0 = 0)
    (hLz7 : 0 ≤ Lz7) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    R7Block α S g (edgeExt Vz) Vθ (edgeExt cs) a b c Lz7 := by
  obtain ⟨β, hβ, _, hHz, hHc⟩ := hthHol
  have hVzc : ContinuousOn (fun p : ℝ × ℝ × ℝ => edgeExt Vz p.1 p.2.1 p.2.2) (Bc S) :=
    continuousOn_edgeExt_hol hβ (continuous_fst.comp_continuousOn hVo) hHz
  have hcsc' : ContinuousOn (fun p : ℝ × ℝ × ℝ => edgeExt cs p.1 p.2.1 p.2.2) (Bc S) :=
    continuousOn_edgeExt_hol hβ hcso hHc
  have hVθc : ContinuousOn (fun p : ℝ × ℝ × ℝ => Vθ p.1 p.2.1 p.2.2) (Bc S) :=
    continuousOn_closed_of_sin (continuous_snd.comp_continuousOn hVo) hVθsin hVθend
  refine
    { hFjoint := hFjoint
      hVjoint := hVzc.prodMk hVθc
      hVlipU := ?_
      hcscont := hcsc'
      hEq := ?_
      hVz0 := ?_
      hVza := ?_
      hVθb := hVθb
      hVθ0 := fun z τ hz hτ hτS => (hVθend z τ hz ⟨hτ.le, hτS⟩).1
      hVθπ := fun z τ hz hτ hτS => (hVθend z τ hz ⟨hτ.le, hτS⟩).2
      hcsc := ?_
      hInit := hInit
      hLz7 := hLz7
      ha := ha
      hb := hb
      hc := hc }
  · obtain ⟨K, hK⟩ := hVlipU
    refine ⟨K, fun τ hτ => ?_⟩
    intro p hp q hq
    show edist (edgeExt Vz p.1 p.2 τ, Vθ p.1 p.2 τ) (edgeExt Vz q.1 q.2 τ, Vθ q.1 q.2 τ)
      ≤ K * edist p q
    rw [edgeExt_of_mem hp.2.1 hp.2.2, edgeExt_of_mem hq.2.1 hq.2.2]
    exact hK τ hτ hp hq
  · intro z θ τ hz h0 h1 hτ hτS
    rw [edgeExt_of_mem h0 h1, edgeExt_of_mem h0 h1]
    exact hEq z θ τ hz h0 h1 hτ hτS
  · intro z θ τ hz h0 h1 hτ hτS
    rw [edgeExt_of_mem h0 h1]; exact hVz0 z θ τ hz h0 h1 hτ hτS
  · intro z θ τ hz h0 h1 hτ hτS
    rw [edgeExt_of_mem h0 h1]; exact hVza z θ τ hz h0 h1 hτ hτS
  · intro z θ τ hz h0 h1 hτ hτS
    rw [edgeExt_of_mem h0 h1]; exact hcsc z θ τ hz h0 h1 hτ hτS


end Work.FTS.RegExportIface
end
end
-- ===== merged: Submission.Work.FTS.RegExportIface.RXT.LeafAux.loc_sup4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.loc_sup4` — leaf port (module `LeafAux.loc_sup4`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false


theorem loc_sup4 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < π / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 4 →
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| ≤ C := by
  -- the exponent `β = pExp α = 3α` is a positive exponent `≤ 1`
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the class-`C` interior `L^∞`–`ℋ⁶` trade-off
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  have hC₁nn : 0 ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) :=
    div_nonneg hC₁pos.le (Real.sqrt_nonneg _)
  -- the approximating class-C families, the uniform `ℋ⁶`-bound `B`, and the jet convergence
  obtain ⟨gn, B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (T + 1) (by linarith)
  have hBnn : 0 ≤ B := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨le_rfl, by linarith⟩
    have hx : 0 ≤ Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn 0) 0) := Work.Spaces.HkNorm_nonneg _ 6 _
    linarith [(h1 0 0 h0).2.2]
  refine ⟨C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B,
    mul_nonneg hC₁nn hBnn, ?_⟩
  intro τ hτ j i hji z hz θ hθ
  -- the box sits inside the open quadrant, and `τ` inside the horizon `T + 1`
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hθpos : 0 < θ := lt_of_lt_of_le hc hθ.1
  have hθlt : θ < π / 2 := lt_of_le_of_lt hθ.2 hd
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hzpos, hθpos, hθlt⟩
  have hτT : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  -- every approximant satisfies the class-C bound at `(z,θ)`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B := by
    intro n
    have hcn : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := (h1 n τ hτT).1
    have hx6 : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) ≤ B := (h1 n τ hτT).2.2
    have hb := hC₁ (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ hcn j i (by omega) hzθ
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) := hb
      _ ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B :=
          mul_le_mul_of_nonneg_left hx6 hC₁nn
  -- pass to the limit along the jets of order `≤ 4`
  exact le_of_tendsto (h3 τ hτT j i hji z θ hzθ).abs (Filter.Eventually.of_forall hbound)


end Work.FTS.RegExportIface.RXT
end
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.psiCan_C3_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

theorem psiCan_C3_proved {α C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEL : Work.FTS.FinalV2.EllLimOK3 α E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ)
        Work.Construction.Qd := by
  intro τ hτ
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hOK.2 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hE3 : ContDiffOn ℝ 3
      (Function.uncurry (E (Work.FTS.Galerkin.slice g τ))) Work.Construction.Qd :=
    (hEL (fun n => Work.FTS.Galerkin.slice (gn n) τ)
        (Work.FTS.Galerkin.slice g τ) B
        (fun n => (hC n τ hτT).1)
        (fun n => (hC n τ hτT).2.2)
        (hOK.1.1.c4 τ hτ)
        (fun j i hji z θ hzθ => hjet τ hτT j i hji z θ hzθ)).2.1
  have hΦs : ContDiffOn ℝ 3 (Function.uncurry Φs) Work.Construction.Qd :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φs).mp hStar.smooth 3
  have h := hΦs.add hE3
  refine h.congr ?_
  intro q hq
  simp only [Function.uncurry, Work.FTS.Nonlin.PsiCan]

end Work.FTS_FinalLeaves
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.l12_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The majorant weight `√s/(1+s)²` is integrable on `(0,∞)` -/

theorem integrableOn_sqrt_div_sq :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 0) := by
  have hfcont : ContinuousOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div Real.continuous_sqrt.continuousOn
      ((continuous_const.add continuous_id).continuousOn.pow 2) ?_
    intro s hs
    have h0 : (0:ℝ) < s := hs
    positivity
  -- `√s/(1+s)² ≤ 1` on `(0,1]`
  have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioc 0 1) := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Ioc (0:ℝ) 1) (C := (1:ℝ)) measure_Ioc_lt_top.ne) ?_ ?_
    · exact (hfcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro s hs
      have hs0 : (0:ℝ) < s := hs.1
      have hpos : (0:ℝ) < (1 + s) ^ 2 := by positivity
      have hle : Real.sqrt s ≤ (1 + s) ^ 2 := by
        have h1s : (1:ℝ) + s ≤ (1 + s) ^ 2 := by nlinarith
        have h2s : Real.sqrt s ≤ 1 + s := by
          rw [Real.sqrt_le_iff]
          exact ⟨by nlinarith, by linarith⟩
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one hpos).mpr hle
  -- `√s/(1+s)² ≤ s^{-3/2}` on `(1,∞)`
  have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 1) := by
    refine MeasureTheory.Integrable.mono'
      ((integrableOn_Ioi_rpow_iff (s := -(3/2:ℝ)) (t := (1:ℝ))
        (by norm_num)).mpr (by norm_num)) ?_ ?_
    · exact (hfcont.mono (fun s hs => lt_trans (by norm_num) hs)).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro s hs
      have hs1 : (1:ℝ) < s := hs
      have hs0 : (0:ℝ) < s := lt_trans (by norm_num) hs1
      have hpos : (0:ℝ) < (1 + s) ^ 2 := by positivity
      have hs2 : (0:ℝ) < s ^ 2 := by positivity
      have hle : Real.sqrt s / (1 + s) ^ 2 ≤ s ^ (-(3/2:ℝ)) := by
        have hsq : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
        calc Real.sqrt s / (1 + s) ^ 2 ≤ Real.sqrt s / s ^ 2 :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg s) hs2 hsq
          _ = s ^ (-(3/2:ℝ)) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast s 2, ← Real.rpow_sub hs0]
              norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hle
  have hunion : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, _⟩ | h1) <;> linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hunion]
  exact h1.union h2


/-! ## The two analytic inputs, as predicates -/

/-- **The interior `L^∞`–`ℋ⁴` bound** (Elgindi's Corollary `SecondDerivativesBounded`): for a
datum which is `C^∞` on the open quadrant, honestly in `ℋ⁴` and with vanishing boundary traces,
the pointwise value is controlled by the `ℋ⁴`-size. -/
def SupBnd (α C : ℝ) : Prop :=
  ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.Nonlin.BdryTraces α 4 f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 4 f

/-- **The weighted bound on the zero mode of `L₁₂`**: the density `L₁₂dens f s` is dominated by
the (integrable on `(0,∞)`) weight `√s/(1+s)²` times the `ℋ⁴`-norm of `f`. -/
def DensBnd (α C : ℝ) : Prop :=
  ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.Nonlin.BdryTraces α 4 f →
    ∀ s : ℝ, 0 < s →
      |Work.Construction.L12dens f s|
        ≤ C * (Real.sqrt s / (1 + s) ^ 2) * Work.Spaces.HkNorm α 4 f

/-! ## The angular dominated convergence of the `L₁₂`-density -/

theorem continuous_K : Continuous Work.Spaces.K :=
  show Continuous (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) from by fun_prop

/-- **Convergence of the `L₁₂`-density of a converging sequence.**  If the profiles `fn n` carry
the interior class data with a uniform `ℋ⁴`-bound `Λ` and the *sup bound* `SupBnd α C`, and if
`fn n → F` pointwise on the open quadrant, then `L₁₂dens (fn n) s → L₁₂dens F s` at every
`s > 0` (dominated convergence in the angular variable). -/
theorem tendsto_L12dens_of_sup_bound {α C Λ : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 < C)
    (hsup : SupBnd α C) {fn : ℕ → Work.FTS.Galerkin.Fn} {F : Work.FTS.Galerkin.Fn}
    (hcls : ∀ n, Work.FTS.EllipticEst.SmoothOpen (fn n) ∧ Work.Spaces.HkMem α 4 (fn n) ∧
      Work.FTS.Nonlin.BdryTraces α 4 (fn n))
    (hN : ∀ n, Work.Spaces.HkNorm α 4 (fn n) ≤ Λ)
    (hjet : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n => fn n s θ) atTop (𝓝 (F s θ)))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => Work.FM.L12dens Work.Spaces.K (fn n) s) atTop
      (𝓝 (Work.FM.L12dens Work.Spaces.K F s)) := by
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)] with θ h
    exact fun hmem => h.mpr hmem
  -- the uniform pointwise bound on the slices
  have hpt : ∀ (n : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |fn n s θ| ≤ Real.sqrt C * Λ := by
    intro n θ hθ
    have hs2 : (fn n s θ) ^ 2 ≤ C * Work.Spaces.HkSq α 4 (fn n) :=
      hsup (fn n) (hcls n).1 (hcls n).2.1 (hcls n).2.2 s θ hs hθ.1 hθ.2
    have hsq : Work.Spaces.HkSq α 4 (fn n) = (Work.Spaces.HkNorm α 4 (fn n)) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 (fn n))]
    have hle : Work.Spaces.HkSq α 4 (fn n) ≤ Λ ^ 2 := by
      rw [hsq]
      exact sq_le_sq' (by linarith [Work.Spaces.HkNorm_nonneg α 4 (fn n), hN n]) (hN n)
    have habs : |fn n s θ| = Real.sqrt ((fn n s θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    rw [habs]
    calc Real.sqrt ((fn n s θ) ^ 2) ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 (fn n)) :=
          Real.sqrt_le_sqrt hs2
      _ ≤ Real.sqrt (C * Λ ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hC.le)
      _ = Real.sqrt C * Λ := by
          rw [Real.sqrt_mul hC.le, Real.sqrt_sq hΛ]
  have hbound : ∀ n, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * fn n s θ / s‖ ≤ Real.sqrt C * Λ / s * |Work.Spaces.K θ| := by
    intro n
    filter_upwards [haeθ] with θ hθ
    have h1 : |fn n s θ| ≤ Real.sqrt C * Λ := hpt n θ hθ
    have h3 : |fn n s θ| / s ≤ Real.sqrt C * Λ / s := div_le_div_of_nonneg_right h1 hs.le
    rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg hs.le]
    calc |Work.Spaces.K θ| * |fn n s θ| / s
        = |Work.Spaces.K θ| * (|fn n s θ| / s) := by ring
      _ ≤ |Work.Spaces.K θ| * (Real.sqrt C * Λ / s) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = Real.sqrt C * Λ / s * |Work.Spaces.K θ| := by ring
  have hmeas : ∀ n, AEStronglyMeasurable (fun θ => Work.Spaces.K θ * fn n s θ / s)
      (volume.restrict Work.Spaces.Iθ) := by
    intro n
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * fn n p.1 p.2 / s) ?_ hs
    refine ContinuousOn.div ?_ continuousOn_const ?_
    · exact ((continuous_K.comp continuous_snd).continuousOn).mul
        ((hcls n).1.forall 1).continuousOn
    · intro p _
      exact ne_of_gt hs
  have hint : Integrable (fun θ => Real.sqrt C * Λ / s * |Work.Spaces.K θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have h := ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      ((continuous_abs.comp continuous_K).continuousOn (s := Work.Spaces.Iθ))
    exact h.const_mul _
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n => Work.Spaces.K θ * fn n s θ / s) atTop
        (𝓝 (Work.Spaces.K θ * F s θ / s)) := by
    filter_upwards [haeθ] with θ hθ
    exact (((hjet s θ hs hθ.1 hθ.2).const_mul (Work.Spaces.K θ))).div_const s
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun n θ => Work.Spaces.K θ * fn n s θ / s)
    (f := fun θ => Work.Spaces.K θ * F s θ / s)
    (fun θ => Real.sqrt C * Λ / s * |Work.Spaces.K θ|) hmeas hint hbound hlim
  simpa only [Work.FM.L12dens, Work.Spaces.Iθ] using hmain


/-! ## The main assembly -/

/-- **`RX-B`: the zero mode of `L₁₂` passes to the limit.**  Given the two analytic inputs
`SupBnd` (interior `L^∞`–`ℋ⁴` bound) and `DensBnd` (weighted bound on the zero mode) at every
`α > 0`, every `τ ≥ 0` has `L₁₂(slice g τ)(0) = 0` for a family `g` which is the pointwise limit
of class-C approximants with a uniform `ℋ⁴`-bound (`LimApprox`). -/
theorem l12_zero_lim_of_bounds {αG C₀ : ℝ} (hα : 0 < αG) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsupAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ SupBnd α C)
    (hdenAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ DensBnd α C)
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by
  intro τ hτ
  obtain ⟨Csup, hCsup, hsup⟩ := hsupAll αG hα
  obtain ⟨Cden, hCden, hden⟩ := hdenAll αG hα
  obtain ⟨gn, B, L, hcls, hlip, hjet, hmu⟩ := hA (max τ 1 + 1) (by
    have := le_max_right τ 1
    linarith)
  have hτT : τ ∈ Set.Icc (0:ℝ) (max τ 1 + 1) := by
    refine ⟨hτ, ?_⟩
    have := le_max_left τ 1
    linarith
  -- the class data of the approximants
  have hclass : ∀ n, Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n => (hcls n τ hτT).1
  have hN : ∀ n, Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
    fun n => (hcls n τ hτT).2.1
  have hΛ : 0 ≤ C₀ * αG ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg αG 4 _) (hN 0)
  have hcls' : ∀ n, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := fun n =>
    ⟨(hclass n).reg,
     Work.FTS.OpenPkg.HkMem_mono_open (hclass n).reg 4 (by norm_num) (hclass n).mem,
     Work.FTS.ClassC.bdryTraces_mono (by norm_num) (hclass n).tr⟩
  have hjet' : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ s θ) atTop
        (𝓝 (Work.FTS.Galerkin.slice g τ s θ)) := by
    intro s θ hs hθ hθ'
    have h := hjet τ hτT 0 0 (by norm_num) s θ ⟨hs, hθ, hθ'⟩
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
      Work.Spaces.DzIter_zero] using h
  have hzero : ∀ n, Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0 = 0 :=
    fun n => (hclass n).l12_zero
  -- the `L¹(ds)` majorant
  set M : ℝ → ℝ := fun s => Cden * (Real.sqrt s / (1 + s) ^ 2) * (C₀ * αG ^ 2) with hMdef
  have hMint : MeasureTheory.IntegrableOn M (Set.Ioi 0) := by
    have h : MeasureTheory.IntegrableOn
        (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) (Set.Ioi 0) :=
      integrableOn_sqrt_div_sq.const_mul (Cden * (C₀ * αG ^ 2))
    have hfun : (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) = M := by
      funext s
      simp only [hMdef]
      ring
    rwa [hfun] at h
  -- the dominated convergence theorem in the radial variable
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable (fun z hz => ?_) measurableSet_Ioi
    exact (Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk
      (hcls' n).1 (hcls' n).2.1 hz).continuousWithinAt
  have hconv : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
        atTop (𝓝 (Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) s)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs =>
      tendsto_L12dens_of_sup_bound hΛ hCsup hsup hcls' hN hjet' hs)
  have hbdd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), ∀ n,
      ‖Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s‖ ≤ M s := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs n => ?_)
    have h1 : |Work.Construction.L12dens (Work.FTS.Galerkin.slice (gn n) τ) s|
        ≤ Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      hden _ (hcls' n).1 (hcls' n).2.1 (hcls' n).2.2 s hs
    have h2 : Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ M s := by
      rw [hMdef]
      exact mul_le_mul_of_nonneg_left (hN n)
        (by positivity)
    rw [Real.norm_eq_abs]
    exact le_trans h1 h2
  have hlim := Work.FTS.StrongEps.L12_tendsto_of_dominated
    (f := fun n => Work.FTS.Galerkin.slice (gn n) τ) (g := Work.FTS.Galerkin.slice g τ)
    (M := M) (ρ := 0) hmeas hconv hbdd hMint
  have h0 : Tendsto (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
      atTop (𝓝 (0:ℝ)) := by
    have hfun : (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
        = fun _ => (0:ℝ) := funext hzero
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

end Work.FTS_RegExport.RXB
end
end
