import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.Vz7Wire
import Submission.Work.FTS_RegExport.RXVP.NoHdat.vz0_of_vopLower_noHdat
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved_noHdat
import Submission.Work.FTS_RegExport.RXR5.r5Parts_hVP
import Submission.Work.FTS_RegExport.r1Block.regExport_hVop
import Submission.Work.FTS_RegExport.RXT.C2Psi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.Vz7Eslot` — the producers from ONE quantitative clause instead of `hVop`

`Vz7Split.lean` shows that the frozen field `VelPkg.vz0` is *equivalent* to the axial-strain sign
bound `hVop` (i.e. assuming `hVop` assumes the conclusion).  This file replaces that assumption by
a clause that is **strictly weaker** and **satisfiable by the construction**:

    ESlotBd α Cs g E  :  ∃ CE,
      (∀ τ z θ, 0 ≤ τ → quadrant → |V(E (slice g τ)) z θ| ≤ CE·pExp α)      -- the elliptic slot
      ∧ 4·pExp α + 2·Cs·(pExp α)² + 2·CE·(pExp α)² ≤ 1/2                    -- the tie

where `Cs` is the constant of the frozen `hStar`.  The first conjunct is the elliptic `V`-slot of
`EllPkgK` (`HkNorm αG 6 (V(ΦTil u (Eu))) ≤ Ce·HkNorm αG 6 u`) with the `pExp α` factor *kept*
(so at the wire's `pExp α ≤ 2.4·10⁻⁸` any explicitly bounded constant satisfies it), and the second
is pure arithmetic on the wire's numbers.

Main results:

* `Work.FTS_RegExport.hVop_of_ESlotBd` — **`hVop` from `ESlotBd`** (so the sign bound is *derived*,
  not assumed), via `vz7_nonneg_wire_of_star` (star slot discharged from `hStar.VW`, elliptic slot
  from the clause, arithmetic from the tie) and the closed form of `Vz7`;
* `Work.FTS_RegExport.velPkg_of_ESlotBd`, `…r5Parts_of_ESlotBd`, `…regExport_of_ESlotBd` — the three
  producers of `RegExportIface/Producers.lean` at the frozen binder list with `ESlotBd` as the
  **single** extra hypothesis, obtained by feeding `hVop_of_ESlotBd` into the already proved
  `velPkg_proved_noHdat` / `r5Parts_hVP` / `regExport_hVop`.

Consequently the whole remaining content of `RX-VP` is the existence of a uniform `αG`-rate bound
on `V(E (slice g τ))` with a modest constant — a *single* elliptic estimate, uniform in `τ`, and
not a positivity assumption.  See `NOTES_FINAL.md` §20.
-/

set_option linter.unusedVariables false

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The single quantitative clause that replaces `hVop`.**  `ESlotBd α Cs g E` says: the elliptic
`V`-slot `V(E (slice g τ))` is uniformly `O(pExp α)` (first conjunct) and the resulting arithmetic
criterion (second conjunct, with the star constant `Cs`) holds. -/
def ESlotBd (α Cs : ℝ) (g : Fam) (E : Fn → Fn) : Prop :=
  ∃ CE : ℝ, (∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (E (slice g τ)) z θ| ≤ CE * Work.FTS.Regularity.pExp α)
    ∧ 4 * Work.FTS.Regularity.pExp α
        + 2 * Cs * (Work.FTS.Regularity.pExp α) ^ 2
        + 2 * CE * (Work.FTS.Regularity.pExp α) ^ 2 ≤ 1 / 2

/-- **`hVop` from `ESlotBd`.**  The pointwise axial-strain lower bound of the producer `velPkg`
follows from the clause, with no positivity assumption. -/
theorem hVop_of_ESlotBd {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hcl : ESlotBd α Cs g ⇑E) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        ≤ 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ := by
  obtain ⟨CE, hVeu, htie⟩ := hcl
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the pointwise slice identity on the quadrant
  have hslice : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ
        = Φs z θ + E (slice g τ) z θ := by
    intro τ a b hτ' ha hb hb2
    have h1 := Work.FTS_RegExport.RXT.slice_PhiR_eq (α := α) (Φs := Φs) (E := E) (g := g)
      hτ' ha hb hb2
    show slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ a b = Φs a b + E (slice g τ) a b
    rw [h1]
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.FinalV2.slice_tauExt g hτ']
  -- smoothness of the whole slice and of its two summands
  have hsmΦs : ContDiffOn ℝ 3 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φs).mp hStar.smooth 3
  have hsmEu : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (E (slice g τ))) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ'
    have hsm : ContDiffOn ℝ 3 (Function.uncurry (slice
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) Work.FTS.EllipticEst.Q0 :=
      Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
        (Φs := Φs) (E := E) (g := g) hEL3 hStar hOK τ hτ'
    exact (hsm.sub hsmΦs).congr (fun p hp =>
      (show E (slice g τ) p.1 p.2 = slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ p.1 p.2
          - Φs p.1 p.2 by
        have h1 := hslice τ p.1 p.2 hτ' hp.1 hp.2.1 hp.2.2
        show E (slice g τ) p.1 p.2 = slice (Work.FTS.RegExportIface.psiR α Φs E
          (Work.FTS.FinalV2.tauExt g)) τ p.1 p.2 - Φs p.1 p.2
        rw [h1]; ring))
  -- differentiability of the three `θ`-slices at every point of the quadrant
  have hdΦ : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => slice
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ') θ := by
    intro τ a b hτ' ha hb hb2
    exact Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice
      (f := slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)
      (Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
        (Φs := Φs) (E := E) (g := g) hEL3 hStar hOK τ hτ') ha hb hb2
  have hdΦs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => Φs z θ') θ := fun a b ha hb hb2 =>
    Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice hsmΦs ha hb hb2
  have hdu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => E (slice g τ) z θ') θ := fun τ a b hτ' ha hb hb2 =>
    Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice (hsmEu τ hτ') ha hb hb2
  -- the clock bound, in the `maxMu` form of the producer
  have hmu : ∀ τ : ℝ, 0 ≤ τ →
      |Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2 := by
    intro s hs
    have h : Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E g) g s
        = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g s := by
      simp only [Work.FTS.Final.maxMu, max_eq_left hs]
    rw [h]
    exact hμ.1 s hs
  -- the star slot, from the frozen `hStar.VW`
  have hVstar := starVop_pointwise_le (α := Work.FTS.Regularity.pExp α) (Cs := Cs)
    (Φs := Φs) hStar.VW.1 hStar.VW.2
  -- `vz0` at every point, from the sharp split and the criterion
  have hvz0 := vz7_nonneg_wire_of_star (αG := Work.FTS.Regularity.pExp α) (Cs := Cs) (CE := CE)
    (μ := Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
      (Work.FTS.Nonlin.PsiCan Φs E g) g)
    (G := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
    (Φ := Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
    (Φs := Φs) (u := fun τ => E (slice g τ))
    hαG hαG1 hStar.VW.1 hStar.VW.2 hmu hslice hdΦ hdΦs hdu hVeu htie
  -- the closed form turns it into the lower bound on `V`
  intro z θ τ hz hθ hθ2 hτ
  have hcf := Work.FTS_RegExport.RXVP.NoHdat.vz7_eq_of_vop
    (αG := Work.FTS.Regularity.pExp α) hαG
    (μ := Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
    (G := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
    (Φ := Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
    (z := z) (θ := θ) (τ := τ) hθ hθ2 (hdΦ τ z θ hτ hz hθ hθ2)
  have h0 := hvz0 τ z θ hτ hz hθ hθ2
  linarith [hcf, h0]

/-- **`velPkg` (RX-VP) from `ESlotBd`**: the frozen binder list plus the single clause. -/
theorem velPkg_of_ESlotBd {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hcl : ESlotBd α Cs g ⇑E) :
    ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S :=
  Work.FTS_RegExport.RXVP.velPkg_proved_noHdat (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ
    (hVop_of_ESlotBd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ hcl)

/-- **`r5Parts` (RX-R5) from `ESlotBd`**: the frozen binder list plus the single clause. -/
theorem r5Parts_of_ESlotBd {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hSt1 : ∀ S > 0, Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hcl : ESlotBd α Cs g ⇑E) :
    ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) :=
  Work.FTS_RegExport.RXR5.r5Parts_hVP (α := α) (Ce := Ce) (C₀ := C₀) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hSt1 hdat hμ
    (velPkg_of_ESlotBd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ hcl)

/-- **`regExport` (the assembly item, (7″)) from `ESlotBd`**: the frozen binder list plus the
single clause. -/
theorem regExport_of_ESlotBd {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hclock : (∀ τ : ℝ, 0 ≤ τ →
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α))
    (hcl : ESlotBd α Cs g ⇑E) :
    ∀ S > 0, Work.FTS.RegPkgGal.RegPkg' α S
      (Work.FTS.RegPkgGal.Avort (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.Bdyn (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.extG (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :=
  Work.FTS_RegExport.r1Block.regExport_hVop (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hclock
    (hVop_of_ESlotBd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK (Work.FTS.RegExportIface.ClockBd.of_clock hclock) hcl)

end Work.FTS_RegExport
