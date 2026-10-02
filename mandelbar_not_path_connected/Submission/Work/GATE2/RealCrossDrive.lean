/-
# GATE2 — case (i) of the dichotomy, end to end

The design's residual-1 dichotomy (`Work.GATE2.EXL.exists_real_crossing_or_htail`) has two
branches.  On the **first** branch the ray lift `gamma_1` meets the real axis, and then
`Work.GATE2.EXL.exists_exitLoop_of_realCrossing` (*unconditionally*, by choosing the crossing that
minimises the `1`-periodic shape function `s ↦ Re (gamma_1 s) - s`) produces a real leak point
`y_0` with both exit-loop families at `y_0` and `y_0 + 1/2`.

Combined with `Work.GATE2.twoSided_of_deepLeak` this closes case (i) **completely**: the theorem
below concludes `Work.GATE.TwoSided c₀ P.Nm` with no lift hypothesis beyond the existence of a real
crossing.  (Numerically, at the actual `c₀` the lift stays `~0.4` above the real axis, so this
branch does not occur — see `NOTES_LEAD_mandelbar_gaps3.md` §2.0; case (ii) is the load-bearing
one.)
-/
import Submission.Work.GATE2.DeepLeak

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

/-- **Case (i) of the design's dichotomy, end to end.**  From a real crossing of the ray lift
`gamma_1`, `Work.GATE.TwoSided c₀ P.Nm`.  Hypotheses are those of
`Work.GATE2.twoSided_of_deepLeak`; the leak centre, the `DeepLeak` datum and the two exit-loop
families are all produced by `Work.GATE2.EXL.exists_exitLoop_of_realCrossing`. -/
theorem twoSided_of_realCrossing {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (Lray : Work.ELRig.RayCylLift d fl)
    (h0 : ∃ s : ℝ, (Lray.γ₁ s).im = 0) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨y₀, hy₀deep, hleak, hE₁, hE₂⟩ :=
    Work.GATE2.EXL.exists_exitLoop_of_realCrossing fl Lray h0
  exact twoSided_of_deepLeak (d := d) (T := T) FF trans hOpen hfront hPaeq hφa_eq hΨeq
    hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG
    (deepLeak_of_leak (fl := fl) hy₀deep hleak) hE₁ hE₂

end Work.GATE2
