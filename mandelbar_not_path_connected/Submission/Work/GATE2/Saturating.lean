/-
# GATE2 — the drives with PL's basin and half-plane inputs discharged

`Work.GATE2.twoSided_of_PARIMPL_PL_EXL` (AssemblyPLEXL) and `Work.GATE2.twoSided` (Final) take
PL's three inputs

* `hK : fl.Pa ⊆ K c₀` — the basin fact of the `c₀`-flower,
* `hHalf : ∃ X, ∀ w, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w` — the half-plane saturation of the
  attracting Fatou coordinate on the invariant sub-petal,
* `hv` — the real Écalle height of the entry point.

This module removes the first two from the hypothesis list:

* `hK` is **not a hypothesis at all**: it is `Work.ELRig.Pa_subset_K fl` (the petal of the
  parabolic flower lies in the filled Julia set, because its `F`-orbit converges to the parabolic
  point).  Every drive below passes it explicitly.
* `hHalf` is the **output** of `Work.GATE2.PL.exists_flowerFix_saturating`: from the single
  numeric condition `Re ((2/3)·F'''/F''²) < 1` at the parabolic point (the Abel invariant of the
  germ) the area produces a Leau–Fatou flower `fl` together with a `FlowerFix` `FF` satisfying
  `FF.Pg = fl.Pg` **and** the saturation.  The drives below take the saturation as a *certificate*
  (`Work.GATE2.SaturatedFlower`, produced by `exists_flowerFix_saturating`) rather than as an
  assumption about an arbitrary flower.

See `Submission/Work/GATE2/NOTES.md` for the exact hypothesis list of each drive.
-/
import Submission.Work.GATE2.Final
import Submission.Work.GATE2.AssemblyPLEXL
import Submission.Work.GATE2.PL.principal_param
import Submission.Work.GATE2.PL.exists_flowerFix_saturating
import Submission.Work.ELRig.Pa_subset_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The saturation certificate of a flower** — verbatim PL's `hHalf`: the attracting Fatou
coordinate of the flower maps the invariant sub-petal `FF.Pg` onto a right half-plane.

`Work.GATE2.PL.exists_flowerFix_saturating` produces a flower and a fix satisfying this from the
single numeric condition `Re ((2/3)·F'''/F''²) < 1` at the parabolic point. -/
abbrev SaturatedFlower {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa) : Prop :=
  ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w

/-- **The saturation is a theorem, from the numeric condition at the parabolic point.**  This is
`Work.GATE2.PL.exists_flowerFix_saturating` restated at the certificate: the flower it produces
satisfies `Work.GATE2.SaturatedFlower`. -/
theorem saturatedFlower_of_numeric {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (ha1 : ((2 / 3 : ℝ) * iteratedDeriv 3 (Work.PARIMPL.Ft c₀) d.z₁
      / (iteratedDeriv 2 (Work.PARIMPL.Ft c₀) d.z₁) ^ 2).re < 1) :
    ∃ fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁,
      ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
        SaturatedFlower fl FF := by
  obtain ⟨fl, FF, -, hX⟩ := Work.GATE2.PL.exists_flowerFix_saturating d ha1
  exact ⟨fl, FF, hX⟩

/-- **The `twoSided` field of `Work.Final.FinalInputs` with PL's basin fact and half-plane
saturation discharged.**

The hypotheses are PARIMPL's `ParNormal`/`MatchData`/`TransitData`/`LeakData`, the flower facts,
the identification of PARIMPL's coordinates with the flower's, the saturation certificate
`hSat` (a *theorem* of `Work.GATE2.PL.exists_flowerFix_saturating`, under one numeric condition),
the real Écalle height `hv` of the entry point, the floored UT, and the two exit loops.  `hK` is
not a hypothesis (`Work.ELRig.Pa_subset_K`). -/
theorem twoSided_of_saturating {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) =
        ((((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) + N : ℝ) : ℂ))
    (hUT : ∀ X : ℝ, TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hEXL₁ : ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨hPL⟩ := Work.GATE2.PL.principal_param fl FF (Work.ELRig.Pa_subset_K fl) hSat
    ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) hv
  exact twoSided_of_PARIMPL_PL_EXL FF hOpen hfront hPaeq hφa_eq hΨeq hentry₀ hcrit
    hPL hEXL₁ hEXL₂ (hUT hPL.X)

/-- **The same, from PARIMPL's bundled input.**  The analogue of
`Work.GATE2.twoSided_of_ParImplInputs` with `hHalf` replaced by the saturation certificate `hSat`
(whose flower is again the one produced by `Work.GATE2.PL.exists_flowerFix_saturating`, under the
numeric condition `ha1`). -/
theorem twoSided_of_ParImplInputs_saturating (H : Work.PARIMPL.ParImplInputs)
    {fl : Work.EL.ParabolicFlower (Work.EL.F H.c₀) ((Tantibar H.c₀)^[5]) H.d.z₁}
    (hPaeq : H.Pa = fl.Pa) (hφa_eq : H.φa = fl.φa) (hΨeq : H.Ψ = fl.Ψ)
    (hSat : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ H.fix.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F H.c₀)^[N] H.c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F H.c₀)^[N] H.c₀) =
        ((((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)) + N : ℝ) : ℂ))
    (hUT : ∀ X : ℝ, TransitLockstepAbove H.c₀ H.P.Nm (Work.PARIMPL.transU H.P H.M.nIn) H.M.nIn
      (fun c z => Work.PARIMPL.Ft c z) H.Pa H.φa H.Ψ (X + 1)
      ((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)))
    (hEXL₁ : ExitLoop H.c₀ fl.Ψ (H.L.xstar - (H.L.j₀ : ℝ)) H.L.r₀
      ((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop H.c₀ fl.Ψ ((H.L.xstar - (H.L.j₀ : ℝ)) + 1 / 2) H.L.r₀
      ((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided H.c₀ H.P.Nm := by
  set FF : Work.PARIMPL.FlowerFix H.d (Work.EL.F H.c₀) ((Tantibar H.c₀)^[5]) H.d.z₁ fl.Pa fl.φa :=
    { shift := fun z hz => by rw [← hφa_eq]; exact H.fix.shift z (hPaeq.symm ▸ hz)
      Pg := H.fix.Pg
      Pg_sub := fun z hz => hPaeq ▸ H.fix.Pg_sub hz
      isOpen_Pg := H.fix.isOpen_Pg
      mapsTo_F_Pg := H.fix.mapsTo_F_Pg
      mapsTo_G_Pg := H.fix.mapsTo_G_Pg } with hFFdef
  exact twoSided_of_saturating (d := H.d) (fl := fl) FF H.isOpen_Nm H.mem_frontier_Nm
    hPaeq hφa_eq hΨeq H.entry_mem H.critHeight_zero hSat hv hUT hEXL₁ hEXL₂

end Work.GATE2
