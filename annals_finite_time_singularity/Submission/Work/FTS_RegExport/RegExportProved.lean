/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_RegExport.RegExportProved` — the PROVED producers of FTS_RegExport

This is the export module of the area `Submission/Work/FTS_RegExport/`.  Every declaration below
is the frozen producer of `Submission/Work/FTS/RegExportIface/Producers.lean` with the
**identical type** (the statement is copied verbatim from the frozen file, under the same `open`s
and the same `variable` block), named `<name>_proved`, and proved.

| item | theorem | proved in |
|---|---|---|
| RX-A1  | `abs_mixed_le_HkNorm_C4_proved` | `FTS_RegExport/RXA1/…` |
| RX-A1w | `abs_mixed_le_HkNorm_C4_w_proved` | `FTS_RegExport/RXA1w/…` |
| RX-A2  | `lim_mixed_bounds_proved` | `FTS_RegExport/RXA2/…` |
| RX-A2w | `lim_mixed_weighted_proved` | `FTS_RegExport/RXA2w/…` |
| RX-B   | `l12_zero_lim_proved` | `FTS_RegExport/RXB/…` |
| RX-T   | `transport_weighted_proved` | `FTS_RegExport/RXT/transport_weighted_proved.lean` |
| RX-St1 | `st1Export_proved` | `FTS_RegExport/RXT/weighted_system.lean` + `…/st1_of_weighted.lean` |
| RX-Supp| `suppExport_proved` | `FTS_RegExport/Supp.lean` |
| RX-R1  | `r1Block_proved` | `FTS_RegExport/RXR1/…` |
| RX0    | `forall_regPkg_of_parts'_proved` | `FTS_RegExport/RX0/…` |

The items **not** in this file are RX-VP (`velPkg`), RX-R5 (`r5Parts`) and the assembly
`regExport`; they are declared under the deliverable names `Work.FTS_RegExport.velPkg_proved`,
`r5Parts_proved`, `regExport_proved` in **`Submission.Work.FTS_RegExport.RegExportProved2`**,
each with the single extra binder `hVop` (`= VelPkg.vz0`, see `NOTES_FINAL.md` §2/§7) — the
underlying proofs are `RXVP.velPkg_proved_noHdat`, `RXR5.r5Parts_hVP` and
`r1Block.regExport_hVop`.  RX-R7 (`r7Block`) and RX-T0 (`dtau_mixed`) *are* in this file, at the
frozen type.  See `NOTES_FINAL.md`, `NOTES_area_state2.md`, `NOTES_superseded.md`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXA1.abs_mixed_le_HkNorm_C4_proved
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXT.transport_weighted_proved
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.RXT.st1_of_weighted
import Submission.Work.FTS_RegExport.Supp
import Submission.Work.FTS_RegExport.RXR1.r1Block_proved
import Submission.Work.FTS_RegExport.RXR7.r7Block_proved
import Submission.Work.FTS_RegExport.RXT0.dtau_mixed_proved
import Submission.Work.FTS_RegExport.RX0.forallRegPkgOfParts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **RX-A1 (write once; shared with Final `classC_sup_le`)**: the interior `L^∞`–`ℋ⁴` trade-off
of `Der.abs_mixed_le_HkNorm_RegQ` with `SmoothQuad` replaced by `C⁴` on the open quadrant. -/
theorem abs_mixed_le_HkNorm_C4_proved {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : Fn}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam β - 1) *
      Work.Spaces.HkNorm β 4 f :=
  RXA1.abs_mixed_le_HkNorm_C4_proved hβ hβ1 h4 hmem htr b a hab hz hθ hθ'

/-- **RX-A1w (REVIEW F3a)**: RX-A1 with the radial weight kept: in `s = log z` the `ℋ⁴` integrand
is `|f·w|²·z ds`, so `H¹(ℝ_s) ⊂ L^∞` gives `|mixed f| ≲ z^{3/2}/(1+z)²·‖f‖_{ℋ⁴}`. -/
theorem abs_mixed_le_HkNorm_C4_w_proved {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fn,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm β 4 f :=
  RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1

/-- **RX-A2** the limit transfer: the order-≤2 sup bound (value) and its `τ`-Lipschitz modulus
for the strong solution, by RX-A1 on the class-C approximants (and their differences) + pointwise
jet convergence. -/
theorem lim_mixed_bounds_proved {αG : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1) {g : Fam}
    (hA : LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a (slice g τ) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (C₀ * αG ^ 2) ∧
        |Work.Spaces.mixed b a (slice g τ) z θ - Work.Spaces.mixed b a (slice g τ') z θ|
            ≤ L * |τ - τ'| :=
  RXA2.lim_mixed_bounds_proved hα hα1 hA T hT

/-- **RX-A2w (REVIEW F3a)**: RX-A1w passed to the limit like RX-A2: the `z^{3/2}/(1+z)²`-weighted
order-≤2 bound of the strong solution, uniform on `[0,T]`. -/
theorem lim_mixed_weighted_proved {αG : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1) {g : Fam}
    (hA : LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a (slice g τ) z θ| ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  RXA2w.lim_mixed_weighted_proved hα hα1 hA T hT

/-- **RX-B** the zero mode passes to the limit (DCT with the `z^{3/2}` majorant from `Xn`). It is
what makes the `O(z)` coefficient of the `F_*`-forcing vanish (St1.0 gate: `∂_zΣ(0,θ) =
−(2/c)·L12(g)(0)·Γ(θ)`). -/
theorem l12_zero_lim_proved {αG : ℝ} (hα : 0 < αG) {g : Fam} (hA : LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (slice g τ) 0 = 0 :=
  RXB.l12_zero_lim_proved hα hA

/-- **RX-T (research medium)** the weighted characteristic estimate for the transport operator
of `(E)`. -/
theorem transport_weighted_proved {S M K₀ Kσ : ℝ} (hα : 0 < α) (hS : 0 < S)
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
      |u z θ τ| ≤ Real.exp (K * S) * (K₀ + S * Kσ) * ω α z θ :=
  RXT.transport_weighted_proved hα hS hu hEq hVz hVθ hlip hcs hσ h0

/-- **RX-St1 (the research core, medium–high)**: the `St1`-class export; `S10 = S9 ∘ S8` of the
leaf plan `RegExportIface/RXT/Leaves.lean`, exactly as the frozen `st1Export'` does it. -/
theorem st1Export_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, St1Class α S (gS α (tauExt g)) := by
  intro S hS
  obtain ⟨K, hK⟩ :=
    RXT.weighted_system (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  exact RXT.st1_of_weighted hα hα13 hOK.1.1 hS hK

/-- **RX-R1 (research low)**: the R1 block at the sanitised right-Taylor family. -/
theorem r1Block_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (H5 : ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g))) :
    ∀ S > 0, R1Block α S (gS α (tauExt g)) :=
  RXR1.r1Block_proved hα hα13 hSol hOK hdat hSt1 H5

/-- **RX-T0 (REVIEW F3b)**: the differentiated `(E)` holds classically: the order-≤2 mixed
derivatives of the strong solution are jointly `C¹` on the slab up to `τ = 0`, and their
`τ`-derivative is the mixed derivative of `∂_τg` (`= RHS`). -/
theorem dtau_mixed_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
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
          (Work.Spaces.mixed b a (Work.FTS.Galerkin.gdot g τ) z θ) τ :=
  RXT0.dtau_mixed_proved hα hα13 hEll hEL3 hStar hSol hOK hμ

/-- **RX-R7 (research low given RX-VP)**: the R7 block at the sanitised family, with the
closed-form coefficients edge-extended (`edgeExt Vz7`, `Vθ7`, `edgeExt cs7`) and the repaired
`VelPkg` (open-θ + `thLip`, no axis clause; lead install 2026-10-11, `cbc/fts_velpkg_fix.md`).
The hypothesis no longer involves the (false) axis-slope condition (★). -/
theorem r7Block_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
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
      a b c Lz7 :=
  RXR7.r7Block_proved hα hα13 hSol hOK hdat hμ hVP

/-- **RX0 (re-proof, research-free).** `GalMinConv` with the four `hRQ` consumers re-proved from
`hIS` + `hmin.c4` and from `hSt1.hhθ`; `GalMinAssembly`/`PartsAssembly` re-pointed. -/
theorem forall_regPkg_of_parts'_proved {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, R5Parts α S g Φ) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) :=
  RX0.forallRegPkgOfParts H H5

end Work.FTS_RegExport
