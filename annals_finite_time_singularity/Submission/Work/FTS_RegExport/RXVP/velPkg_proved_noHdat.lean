import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP.NoHdat.cont_open_noHdat
import Submission.Work.FTS_RegExport.RXVP.NoHdat.vz0_of_vopLower_noHdat
import Submission.Work.FTS_RegExport.RXVP.NoHdat.bnd_open_noHdat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.velPkg_proved_noHdat` — RX-VP **without** the datum hypothesis

`RXVP.velPkg_proved` proves the frozen `RegExportIface.VelPkg` for the constructed family from
`hα, hα13, hEll, hEL3, hStar, hSol, hOK, hdat, hμ, hVop`.  The extra hypothesis there is the
**datum clause**

  `hdat : ∃ L β, 1 ≤ L ∧ ∀ z θ, g z θ 0 = locG6 (pExp α) L β z θ`,

i.e. the assertion that the initial datum of the family is the localized datum of the strong
route.  It is not a consequence of `hSol`/`hDynOK'` (the strong route produces solutions from
*arbitrary* admissible data, `FinalV2.Inputs'.4'`), but it is **unused by the proof**: in each of
the four RX-VP ingredients that carried it —

* `Work.FTS_RegExport.RXVP3.velPkgEasy` (the `vanishK`, `c2`, `vth_ends` clauses),
* `Work.FTS_RegExport.RXVP3.bnd_open` (the `bnd` clause),
* `Work.FTS_RegExport.RXVP3.cont_open` (the `cont` clause),
* `Work.FTS_RegExport.RXVP3.vz0_of_vopLower` (the `vz0` clause),

— the binder `hdat` does not occur anywhere in the proof term (`#print` shows the proof as a
lambda whose `hdat`-slot is invisible to the body).  Hence the same proofs establish the four
results with `hdat` deleted, and the RX-VP package follows for an *arbitrary* family satisfying
`Sol ∧ DynOK' ∧ ClockBd`.

The hdat-free ingredients are proved in `Submission/Work/FTS_RegExport/RXVP/NoHdat/`:

* `NoHdat.velPkgEasy_noHdat`, `NoHdat.cont_open_noHdat`, `NoHdat.vz0_of_vopLower_noHdat`
  (verbatim copies of the sources, minus the unused binder);
* `NoHdat.bnd_open_noHdat`;

together with the *already* hdat-free `RXT.velVanish2` (`vanish0`), `RXT.Sys.coeff_dbnd` (`dbnd`)
and `RXVP.thHol_proved` (`thHol`).  The assembly below is the exact analogue of
`RXVP3.velPkgOpen_of_vopLower` with the four hdat-free calls, glued to the frozen `VelPkg` by
`VelPkg_of_open`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

namespace Work.FTS_RegExport.RXVP

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- **`VelPkgOpen` for the constructed family, with no datum hypothesis**: the same conclusion and
the same hypotheses as `RXVP3.velPkgOpen_of_vopLower`, minus `hdat`. -/
theorem velPkgOpen_noHdat (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g)
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g τ)
        ≤ 2 * pExp α * Work.Construction.Vop
            (slice (psiR α Φs E (tauExt g)) τ) z θ) :
    ∀ S > 0, Work.FTS_RegExport.VelPkgOpen (pExp α)
      (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S := by
  intro S hS
  -- the three clauses of `velPkgEasy`, uniformly in `τ` (no `hdat`)
  obtain ⟨hE1, hE2, hE3⟩ := Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
    (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEll hEL3 hStar hSol hOK hμ
  -- the slots of `Φ̃` (order `≤ 2`)
  obtain ⟨Mv, hMv⟩ := Work.FTS_RegExport.RXT.velVanish2 (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  -- the coefficient jets
  obtain ⟨Md, hMd⟩ := Work.FTS_RegExport.RXT.Sys.coeff_dbnd (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  -- the τ-uniform sup bound (no `hdat`)
  obtain ⟨M, hM⟩ := Work.FTS_RegExport.RXVP.NoHdat.bnd_open_noHdat
    (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEll hEL3 hStar hSol hOK hμ
  -- joint continuity (no `hdat`)
  have hCont := Work.FTS_RegExport.RXVP.NoHdat.cont_open_noHdat
    (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  -- the pointwise lower bound on the `V`-slot, in the form of `vz0` (no `hdat`)
  have hVz0 := Work.FTS_RegExport.RXVP.NoHdat.vz0_of_vopLower_noHdat
    (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEll hEL3 hStar hSol hOK hμ hVop
  refine ⟨⟨M, hM⟩, hVz0, ?_, ?_, ?_, hCont, ?_, ?_⟩
  · -- `vth_ends`
    intro z τ hz hτ
    exact hE3 (max τ 1) (lt_of_lt_of_le zero_lt_one (le_max_right τ 1))
      τ ⟨hτ, le_max_left τ 1⟩ z hz
  · -- `c2`
    intro τ hτ
    exact hE2 (max S 1) (lt_of_lt_of_le zero_lt_one (le_max_right S 1))
      τ ⟨hτ.1, le_trans hτ.2 (le_max_left S 1)⟩
  · -- `dbnd`
    refine ⟨Md, ?_⟩
    intro τ hτ j i hji z θ hz hθ hθ2
    exact hMd τ hτ j i hji z θ hz hθ hθ2
  · -- `vanish0`
    refine ⟨Mv, ?_⟩
    intro τ hτ z θ hz hθ hθ2 Q hQ
    have h00 := hMv τ hτ z θ hz hθ hθ2 Q hQ 0 0 (by norm_num)
    have h10 := hMv τ hτ z θ hz hθ hθ2 Q hQ 1 0 (by norm_num)
    have h01 := hMv τ hτ z θ hz hθ hθ2 Q hQ 0 1 (by norm_num)
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] at h00 h10 h01
    exact ⟨h00, h10, h01⟩
  · -- `vanishK`
    exact hE1 S hS

theorem velPkg_proved_noHdat {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        ≤ 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ) :
    ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S := by
  intro S hS
  exact Work.FTS_RegExport.VelPkg_of_open
    (velPkgOpen_noHdat (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ hVop S hS)
    (thHol_proved (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS)

end Work.FTS_RegExport.RXVP
