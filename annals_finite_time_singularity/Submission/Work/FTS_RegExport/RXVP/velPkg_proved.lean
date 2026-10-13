import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.RXVPMain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.velPkg_proved` — RX-VP, up to the one missing hypothesis `hVop`

`VelPkg` (frozen `RegExportIface`) = `VelPkgOpen` (the repaired package: open-`θ`
`bnd`/`vz0`/`cont`, no `axis`; seven of eight fields PROVED in `RXVP3/`) plus the `thHol` clause
(PROVED here as `RXVP.thHol_proved`, the A8 assembly of the THL leaves A1a–A7).

The single remaining input is `hVop`, the pointwise **lower bound on the `V`-slot of the stream
function**: on the open quadrant

    `2 * pExp α * Vop (slice (psiR α Φs E (tauExt g)) τ) z θ ≥ -(1 - maxMu α (PsiCan Φs E g) g τ)`.

By the proved closed form (`RXVP3.vz0_of_vopLower.vz7_eq_of_vop`) this is *equivalent* to the
field `VelPkg.vz0`; it is the pointwise form in which the constraint is geometric (a lower bound
on the axial strain of the stream function), and it is what the frozen interface needs to add —
see `NOTES_session_gaps.md` §2 (G3).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

namespace Work.FTS_RegExport.RXVP

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

theorem velPkg_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g τ)
        ≤ 2 * pExp α * Work.Construction.Vop
            (slice (psiR α Φs E (tauExt g)) τ) z θ) :
    ∀ S > 0, VelPkg (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S := by
  intro S hS
  exact Work.FTS_RegExport.VelPkg_of_open
    (Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVop S hS)
    (thHol_proved (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS)

end Work.FTS_RegExport.RXVP
