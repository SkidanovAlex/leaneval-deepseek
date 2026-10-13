/-
# `Work.FTS.Final.MeridianRed` — the meridian conjunct of `Inputs` from the dynamics

The bundle `Work.FTS.Final.Inputs` takes the meridian equation of the reconstruction as one of its
open conjuncts (conjunct (8)).  This module *reduces* that conjunct to the inputs of the
`RegPkgMin`-version of the dynamic meridian bridge:

  `Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin`

(proved in `FTS/Final/MeridianMin/`, the `RegPkgMin` generalisation of
`Work.FTS.MeridianDyn.meridianEq_of_dynEq`), namely

* the fake-time equation `IsDynEqOn (pExp α) Φ g` — supplied by the dynamics (`hSol.2`, since
  `IsDynGSolWith Law α Φ g = Law ∧ IsDynEqOn α Φ g`; the elliptic law is *not* used by the bridge);
* the package `RegPkgMin (pExp α) g` — supplied by `hDyn`;
* the interior `C²`-regularity of `Φ` on the quadrant, its oddness in `θ`, and the static
  derivation data `ProfDerivData (pExp α) Φ g`;
* the clock data `ClockData` — verified in the assembly for the clock `physClockOf` of the dynamic
  modulation.

So the caller may instantiate the assembly with the meridian conjunct discharged by
`hMer_of_dyn` below, leaving `hΦ`, `hΦodd` and `hD` as the (much smaller) meridian inputs.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Final.Assembly
import Submission.Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith IsDynEqOn)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)

set_option autoImplicit false

/-- **The meridian equation of the reconstruction from the dynamics.**

The fake-time equation of the strong route (`hSol.2`) together with the regularity package
`RegPkgMin`, the interior regularity and oddness of the stream function, the static derivation data
and the clock data produce the meridian scalar equation on `(0, C.T)` for the meridian pair
`(merProfile α A B g C, merPsi (pExp α) A B Φ C)` of the physical reconstruction.

This is `Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin` with the two interfaces of
the assembly (`IsDynGSolWith`, `ClockData`) unpacked. -/
theorem hMer_of_dyn {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g Φ : Fam} {A B : ℝ → ℝ} {C : PhysClock}
    (hSol : IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
      Φ g)
    (hRegMin : RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd)
    (hΦodd : ∀ τ : ℝ, 0 < τ → ∀ Z Θ : ℝ, Φ Z (-Θ) τ = -Φ Z Θ τ)
    (hD : Work.FTS.MeridianDyn.ProfDerivData (Work.FTS.Regularity.pExp α) Φ g)
    (hClock : ClockData (Work.FTS.Regularity.pExp α) Φ g A B C) :
    MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C) C.T :=
  Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin hα hα13 hSol.2 hRegMin hΦ hΦodd hD
    hClock.2.1 hClock.2.2.1 hClock.2.2.2.1 hClock.2.2.2.2 hClock.1

/-- **The meridian *conjunct* of `Inputs` from the three meridian providers.**  This is
`Work.FTS.Final.Inputs.core`'s conjunct (8) in exactly its shape, produced from the (much smaller)
meridian inputs `hPhiC` (interior `C²` of the stream function on the quadrant), `hPhiOdd` (its
oddness in `θ`) and `hProfD` (the static derivation data `ProfDerivData`) by
`hMer_of_dyn` / `meridianEq_of_dynEq_of_regPkgMin`.

A caller of `exists_blowupAt_of_inputs` may therefore supply conjunct (8) by this lemma, leaving
`hPhiC`, `hPhiOdd`, `hProfD` as the meridian inputs of the bundle. -/
theorem merConj_of_phi {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {C₀ Ce Cs : ℝ}
    {ρ : ℝ × ℝ → ℝ} {E : Fn →ₗ[ℝ] Fn} {Φs : Fn}
    (hPhiC : ∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g → ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hPhiOdd : ∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g → ∀ τ : ℝ, 0 < τ →
      ∀ Z Θ : ℝ, PsiCan Φs E g Z (-Θ) τ = - PsiCan Φs E g Z Θ τ)
    (hProfD : ∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      Work.FTS.MeridianDyn.ProfDerivData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g) :
    ∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
        (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B (PsiCan Φs E g) C) C.T :=
  fun g A B C hSol hOK hClock =>
    hMer_of_dyn hα hα13 hSol hOK.1 (hPhiC g hSol hOK) (hPhiOdd g hSol hOK) (hProfD g hSol hOK) hClock

end Work.FTS.Final
