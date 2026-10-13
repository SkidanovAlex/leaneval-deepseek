import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.Vz7Eslot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegExportIface.Producers` — the OPEN producers of FTS_RegExport (curric-46, 2026-10-10)

One named `theorem … := by sorry` per research item of `cbc/fts_regexport_design.md` §5 as corrected
by `cbc/fts_regexport_design_REVIEW.md` (F2: closed-form coefficients, odd/odd `psiR`, `Θ` on
`z ≤ 0`; F3: `vanish0` in `VelPkg`, RX-A1w, RX-T0). REPAIR 10-11 (`cbc/fts_velpkg_fix.md` + REVIEW):
`VelPkg` is open-θ + `thLip` (axis clause dropped; `thLip` → Hölder `thHol` 10-11, ITEM A of
`cbc/fts_thlip_o1_plans.md`), `r7Block` is fed `edgeExt Vz7`, `Vθ7`,
`edgeExt cs7`; RX-R5 is routed through `Der.R5Parts_of_pieces_F` (product slots,
`FTS_RegExport/RXR5/R5PiecesF.lean`). The deliverable `regExport` (7″) is the
assembly item; `FinalV2.Producers.regPkg7'` is PROVED from it (+ `mu6'` for the clock).

| item | theorem | needs |
|---|---|---|
| RX-A1  | `abs_mixed_le_HkNorm_C4` | — (shared with Final `classC_sup_le`) |
| RX-A1w | `abs_mixed_le_HkNorm_C4_w` | — (same proof, weight kept) |
| RX-A2  | `lim_mixed_bounds` | RX-A1 |
| RX-A2w | `lim_mixed_weighted` | RX-A1w |
| RX-B   | `l12_zero_lim` | — |
| RX-T0  | `dtau_mixed` | — |
| RX-T   | `transport_weighted` | — |
| RX-St1 | `st1Export` | leaf plan `RXT/Leaves.lean` (T1–T5c, S1–S10, X1, S4); RX-B, RX-VP |
| RX-VP  | `velPkg` | RX-A1(w), RX-A2(w); split `velPkgOpen_proved` + `thHol_proved` |
| RX-R7  | `r7Block` | RX-VP |
| RX-Supp| `suppExport` | — (factor of `GalMinConv`'s `hsupp` block) |
| RX-R1  | `r1Block` | RX-A2, RX-St1, RX-R5 |
| RX-R5  | `r5Parts` | RX-St1, RX-A2, RX-VP |
| RX0    | `forall_regPkg_of_parts'` | — (re-proof of `GalMinConv`'s 4 `hRQ` consumers) |
| top    | `regExport` | all of the above + `hsuppOut_gS` + clock |
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.RegExportIface

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **RX-A1 (write once; shared with Final `classC_sup_le`)**: the interior `L^∞`–`ℋ⁴` trade-off
of `Der.abs_mixed_le_HkNorm_RegQ` with `SmoothQuad` replaced by `C⁴` on the open quadrant. -/
theorem abs_mixed_le_HkNorm_C4 {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : Fn}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam β - 1) *
      Work.Spaces.HkNorm β 4 f := by
  exact Work.FTS_RegExport.abs_mixed_le_HkNorm_C4_proved hβ hβ1 h4 hmem htr b a hab hz hθ hθ'

/-- **RX-A1w (REVIEW F3a)**: RX-A1 with the radial weight kept: in `s = log z` the `ℋ⁴` integrand
is `|f·w|²·z ds`, so `H¹(ℝ_s) ⊂ L^∞` gives `|mixed f| ≲ z^{3/2}/(1+z)²·‖f‖_{ℋ⁴}`. -/
theorem abs_mixed_le_HkNorm_C4_w {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fn,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm β 4 f := by
  exact Work.FTS_RegExport.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1

/-- **RX-A2** the limit transfer: the order-≤2 sup bound (value) and its `τ`-Lipschitz modulus
for the strong solution, by RX-A1 on the class-C approximants (and their differences) + pointwise
jet convergence. Feeds `hIS`, R1 (joint continuity up to `τ = 0`), the Jets' `τ`-part, and
Final's `sup5'`. (Check `HkNorm 4 ≤ Xn` for the stated constant.) -/
theorem lim_mixed_bounds {αG : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1) {g : Fam}
    (hA : LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a (slice g τ) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (C₀ * αG ^ 2) ∧
        |Work.Spaces.mixed b a (slice g τ) z θ - Work.Spaces.mixed b a (slice g τ') z θ|
            ≤ L * |τ - τ'| := by
  exact Work.FTS_RegExport.lim_mixed_bounds_proved hα hα1 hA T hT

/-- **RX-A2w (REVIEW F3a)**: RX-A1w passed to the limit like RX-A2: the `z^{3/2}/(1+z)²`-weighted
order-≤2 bound of the strong solution, uniform on `[0,T]`. -/
theorem lim_mixed_weighted {αG : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1) {g : Fam}
    (hA : LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a (slice g τ) z θ| ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  exact Work.FTS_RegExport.lim_mixed_weighted_proved hα hα1 hA T hT

/-- **RX-B** the zero mode passes to the limit (DCT with the `z^{3/2}` majorant from `Xn`). It is
what makes the `O(z)` coefficient of the `F_*`-forcing vanish (St1.0 gate: `∂_zΣ(0,θ) =
−(2/c)·L12(g)(0)·Γ(θ)`). -/
theorem l12_zero_lim {αG : ℝ} (hα : 0 < αG) {g : Fam} (hA : LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (slice g τ) 0 = 0 := by
  exact Work.FTS_RegExport.l12_zero_lim_proved hα hA

/-- **RX-T0 (REVIEW F3b)**: the differentiated `(E)` holds classically: the order-≤2 mixed
derivatives of the strong solution are jointly `C¹` on the slab up to `τ = 0`, and their
`τ`-derivative is the mixed derivative of `∂_τg` (`= RHS`). Route: `g(τ) = g(τ₀) + ∫RHS`,
differentiated under the integral using joint continuity of the order-3 jets (`Xn6` + Lipschitz
interpolation). This is what lets RX-T run on `(D_zg, D_z²g, D_θg, D_θD_zg)`.
RESTATED 10-10 (`cbc/fts_rxt_install.md`, F-A): `+ hμ : ClockBd` (`hne` of `DynEqF_of_isDynEqOn`
and the `τ`-continuity of `μ`). OFF the RX-St1 path in the leaf plan (`RXT/Leaves.lean`). -/
theorem dtau_mixed (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, ∀ b a : ℕ, a + b ≤ 2 →
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed b a (slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S) ∧
      ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
        HasDerivAt (fun s => Work.Spaces.mixed b a (slice g s) z θ)
          (Work.Spaces.mixed b a (Work.FTS.Galerkin.gdot g τ) z θ) τ := by
  exact Work.FTS_RegExport.dtau_mixed_proved hα hα13 hEll hEL3 hStar hSol hOK hμ

/-- **RX-T (research medium)** the weighted characteristic estimate for the transport operator
of `(E)`: `∂_τu + Vz·D_zu + Vθ·∂_θu + cs·u = σ` on `Qd × (0,S]`, with `Vz ≥ 0` bounded and
Lipschitz, `|Vθ| ≤ M sin 2θ`, `|cs| ≤ M`, gives `|u| ≤ e^{KS}(K₀ + S·Kσ)·ω`. Used componentwise
(with Gronwall over the finite system) for `(g, D_zg, D_z²g, D_θg, D_θD_zg)`. The R7e
characteristic flow (`support_strip_zL`) is the template. -/
theorem transport_weighted {S M K₀ Kσ : ℝ} (hα : 0 < α) (hS : 0 < S)
    {u Vz Vθ cs σ : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hEq : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => u z θ s)
        (σ z θ τ - (Vz z θ τ * Work.Spaces.Dz (fun z θ => u z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => u z θ τ) z θ + cs z θ τ * u z θ τ)) τ)
    (hVz : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → 0 ≤ Vz z θ τ ∧ Vz z θ τ ≤ M)
    (hVθ : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ))
    (hlip : ∀ τ ∈ Icc 0 S, ∀ L₁ > 0, ∃ K : NNReal, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ)) (Set.Ioi L₁ ×ˢ Set.Ioo (0:ℝ) (π / 2)))
    (hcs : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → |cs z θ τ| ≤ M)
    (hσ : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → |σ z θ τ| ≤ Kσ * ω α z θ)
    (h0 : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |u z θ 0| ≤ K₀ * ω α z θ) :
    ∃ K : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S →
      |u z θ τ| ≤ Real.exp (K * S) * (K₀ + S * Kσ) * ω α z θ := by
  exact Work.FTS_RegExport.transport_weighted_proved hα hS hu hEq hVz hVθ hlip hcs hσ h0

/-- **RX-St1 (the research core, medium–high)**: the `St1`-class export. Route: RX-T0 + RX-T on
the system `(g, D_zg, D_z²g, D_θg, D_θD_zg)` of the transport form of the `g`-equation,
coefficients `Vz7/Vθ7/cs7` at `psiR` (RX-VP, incl. `vanish0`); the `F_*`-forcing is `O(ω)` by
RX-B (St1.0 gate PASSED); datum bound from `locG6`; `hhθ/hhθp` by integrating
`|∂_θ| ≤ |D_θ|/sin 2θ ≲ z²θ^{α−1}` on `z ≤ L` and the support (RX-Supp) beyond.
RESTATED 10-10 (`cbc/fts_rxt_install.md`, F-A): `+ hμ : ClockBd`. Leaf plan: `RXT/Leaves.lean`
(`st1Export'` = S9 ∘ S8, the vector integrated cone principle T4/T5c; NOT via RX-T0/RX-T). -/
theorem st1Export (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, St1Class α S (gS α (tauExt g)) := by
  exact Work.FTS_RegExport.st1Export_proved hα hα13 hEll hEL3 hStar hSol hOK hdat hμ

/-- **RX-VP (research medium–high; = R-b's elliptic slots + the explicit `Θ` part; one owner
shared with StreamBdry's `hΦsm`/`hΦaxis`)**: the velocity package of `(E)` at
`(gS α (tauExt g), psiR)`, closed-form coefficients (F2.1), with `vanish0`/`vanishK` (F3a).
REPAIRED 10-11 (statement unchanged, `VelPkg` changed in `Defs`): `bnd`/`vz0`/`cont` on the open
angular interval, the false F2.2 axis clause dropped, new clause `thLip` (`Vz7` half from `dbnd` +
`c2`; `cs7` half research-level: `∂²_θ(z∂_zΦ̃)` bounded up to both edges). Split:
`RXVP3.velPkgOpen_proved` + `RXVP.thHol_proved` (10-11: `thLip` restated as the Hölder `thHol`). RESTATED 10-10 (`cbc/fts_rxt_install.md`, F-A): `+ hμ : ClockBd` (`bnd`/`vz0`
need `|μ| ≤ 1/2` for all `τ ≥ 0`, `cont` needs `μ` continuous). -/
theorem velPkg (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g)
    (hcl : Work.FTS_RegExport.ESlotBd α Cs g ⇑E) :
    ∀ S > 0, VelPkg (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S := by
  exact Work.FTS_RegExport.velPkg_of_ESlotBd hα hα13 hEll hEL3 hStar hSol hOK hμ hcl

/-- **RX-R7 (research low given RX-VP)**: the R7 block at the sanitised family, with the
closed-form coefficients, EDGE-EXTENDED (10-11): `edgeExt Vz7`, `Vθ7`, `edgeExt cs7`, so that the
closed-box `hVjoint`/`hcscont` follow from open-quadrant data + `VelPkg.thHol`
(`R7Block_of_velPkgF`). (`hEq`: the `(E)`-form of `IsDynEqOn`, MeridianDyn's passage
`DynEqF_of_isDynEqOn`, + the closed-form identities on the open quadrant; `hInit`: `locG6`.)
RESTATED 10-10 (`cbc/fts_rxt_install.md`, F-A): `+ hμ : ClockBd` (`hne : 1 + muDyn ≠ 0`). -/
theorem r7Block (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hVP : ∀ S > 0, VelPkg (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S) :
    ∃ a b c Lz7 : ℝ, ∀ S > 0, R7Block α S (gS α (tauExt g))
      (edgeExt (Vz7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))))
      (Vθ7 (pExp α) (psiR α Φs E (tauExt g)))
      (edgeExt (cs7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))))
      a b c Lz7 := by
  exact Work.FTS_RegExport.r7Block_proved hα hα13 hSol hOK hdat hμ hVP

/-- **RX-Supp (for StreamBdry; research-free given RX-R7)**: compact `z`-support of the full
profile, per horizon, from `R7e.support_strip_zL` + `RegPkgMin.vanish` (the `hsupp` block of
`GalMinConv`, factored out). -/
theorem suppExport {S a b c Lz7 : ℝ} {g : Fam} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} (hS : 0 < S)
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (pExp α) g) (hα : 0 < α)
    (H : R7Block α S g Vz Vθ cs a b c Lz7) :
    ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → θ ∈ Work.Spaces.Iθ →
      Work.FTS.Regularity.profFull α (extG g) z θ τ = 0 := by
  exact Work.FTS_RegExport.suppExport_proved hS hmin hα H

/-- **RX-R1 (research low)**: the R1 block at the sanitised right-Taylor family, from RX-A2
(joint continuity of `g, D_zg` up to `τ = 0`), `St1Class.quad` at `S+1`, the R5 jets + `hRz0`
(for `∂_τg → 0` at `z → 0`) and the `τ = 0` data (`∂_τ⁺g(·,0) = RHS(locG6)`, smooth). -/
theorem r1Block (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (H5 : ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g))) :
    ∀ S > 0, R1Block α S (gS α (tauExt g)) := by
  exact Work.FTS_RegExport.r1Block_proved hα hα13 hSol hOK hdat hSt1 H5

/-- **RX-R5 (research medium; = R-b)**: the primitive R5 data at `(gS α (tauExt g), psiR)`, via
the proved `Der.R5Parts_of_pieces_F` (10-11, `FTS_RegExport/RXR5/R5PiecesF.lean`; NOT the old
`Der.R5Parts_of_pieces`, whose closed-`Iθ` `C1Jet`s of `Rop Φ̃`/`Vop Φ̃` alone jump at `θ = π/2`
unless the false (★)): class-data `C1Jet`s (from RX-St1 + RX-A2), the elliptic slots as PRODUCT
`C1Jet`s `Rop Φ̃·F`, `Uop Φ̃·∂_θF`, `Vop Φ̃·D_zF` and `FK(F)` (from `EllPkgK 6` on the approximants
+ RX-VP; the products vanish at the axis with `F`, no axis clause needed), `N_*`/`mubar` (proved producers), `h0` (two-sided derivative of the
right-Taylor extension), boundary values (`hRz0`, `hRθ0`, `hRθπ`: algebra, clean with F2.3).
RESTATED 10-11 (`cbc/fts_thlip_o1_plans.md` ITEM B, O1): `+ hdat`, `+ hμ : ClockBd` — the
z-uniform angular modulus of `D_zg̃`, `D_θg̃` (`hDzg`/`hDthg`) comes from S8 `RXT.weighted_system`,
which needs both (leaves B1–B6 in `FTS_RegExport/THL/Leaves.lean`); `regExport` supplies `hdat`
directly and `ClockBd.of_clock hclock`. -/
theorem r5Parts (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hcl : Work.FTS_RegExport.ESlotBd α Cs g ⇑E) :
    ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g)) := by
  exact Work.FTS_RegExport.r5Parts_of_ESlotBd hα hα13 hEll hEL3 hStar hSol hOK hSt1 hdat hμ hcl

/-- **RX0 (re-proof, research-free).** `GalMinConv` with the four `hRQ` consumers re-proved from
`hIS` + `hmin.c4` (`sup_extG_ext`, `sup2_extG_ext`, `hzmodp_ext`) and from `hSt1.hhθ` (endpoint
continuity); `GalMinAssembly`/`PartsAssembly` re-pointed (new files only). Same output as
`RegPkgGal.forall_regPkg_of_parts`. -/
theorem forall_regPkg_of_parts' {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, R5Parts α S g Φ) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  exact Work.FTS_RegExport.forall_regPkg_of_parts'_proved H H5

/-- **(7″) THE DELIVERABLE OF FTS_RegExport (assembly item).** Route: `forall_regPkg_of_parts'`
at `g := gS α (tauExt g)`, `Φ := psiR α Φs E (tauExt g)`, `m := maxMu …`, with `GalMin'` from
`r1Block`, `r7Block` (∘ `velPkg`; coefficients `edgeExt Vz7`, `Vθ7`, `edgeExt cs7` — the assembly
is generic in `Vz Vθ cs`, statement unchanged 10-11), `st1Export`, `hIS` from `lim_mixed_bounds` (+ congruence on the
open quadrant), `hHkn` (`HkNorm 4 ≤ Xn`, a.e.-congruence), `hsuppOut_gS`, `RegPkgMin` of the
sanitised family (congruence + `vanish`), the clock (`hclock` + `maxExt`); `R5Parts` from
`r5Parts` (10-11: called with `hdat` and `ClockBd.of_clock hclock`). The producers `velPkg`,
`r7Block`, `st1Export`, `dtau_mixed`, `r5Parts` take `hμ : ClockBd α Φs E g`, supplied here by
`ClockBd.of_clock hclock` (statement unchanged 10-10, 10-11). -/
theorem regExport (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hclock : (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc (0 : ℝ) S, ∀ τ' ∈ Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α))
    (hcl : Work.FTS_RegExport.ESlotBd α Cs g ⇑E) :
    ∀ S > 0, RegPkg' α S (Avort (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g))
      (Bdyn (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)) (extG (gS α (tauExt g))) := by
  exact Work.FTS_RegExport.regExport_of_ESlotBd hα hα13 hEll hEL3 hStar hSol hOK hdat hclock hcl

end Work.FTS.RegExportIface
