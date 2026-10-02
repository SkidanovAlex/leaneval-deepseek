import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.Main
import Submission.Work.GATE2.PL.eq_c0_of_good

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open Classical
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **PL — the principal Fatou parametrisation of the `c₀`-flower passes through the critical
value** (the design's §4.1, `NOTES_LEAD_mandelbar_gate2transport.md`).  v2: the phase hypothesis
`hv` now requires the evaluation point to lie **inside** the petal (the previous version evaluated
`fl.φa` at `F^N c₀` for an arbitrary `N`, where `φa` is a junk extension, and was refuted: the
conclusion forces `v = fl.φa (F^m c₀) − m` with `m` the entry time of the critical orbit into the
petal).

`F₀ = Work.EL.F c₀ = (T_{c₀})^{10}`, `g₀ = (T_{c₀})^5` its antiholomorphic square root.  Given the
Leau–Fatou flower `fl` of `F₀` at `d.z₁`, the `FatouCoord` fix `FF`, the basin fact `fl.Pa ⊆ K c₀`,
and the half-plane surjectivity of `fl.φa` on the invariant sub-petal `FF.Pg`, there is a
**principal Fatou parametrisation** `ψ` of the slit plane `Ω_v = ℂ \ (−∞, v − 1/2]` which is
continuous and maps `v` to `c₀`, intertwines `F₀` with the shift `w ↦ w + 1` and `g₀` with the
`ι`-symmetry `w ↦ w̄ + 1/2`, and far to the right is the inverse of the Fatou coordinate on `Pg`.

Construction (design §4.1): base on `{Re w > X}` by inverting `fl.φa` on `Pg`; then half-step lifts
through `g₀` over `ℂ \ CV`, `CV = {T^j c₀ : j ≤ 4}` the critical values of `g₀` (no obstruction:
`ψ w' = c₀` forces `w' = v` which is not in the slit plane, and `ψ w' = T^j c₀` is impossible because
`F`-orbits in `Pa` tend to `d.z₁` while `T^j d.z₁ ≠ d.z₁` by the exact period `5`); if in the
contrary case there were no obstruction at all, `ψ` would extend to a bounded entire function
(Liouville), a contradiction — so `ψ v = c₀`. -/
theorem principal_param {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
      ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁)
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀)
      ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    (hK : fl.Pa ⊆ Work.EL.K c₀)
    (hHalf : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (v : ℝ)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ)) :
    Nonempty (Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa v) := by
  obtain ⟨X₀, hHalf₀⟩ := hHalf
  set X : ℝ := max X₀ (v + 1) with hXdef
  have hHalf' : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w := by
    intro w hw
    refine hHalf₀ w ?_
    have : X₀ ≤ X := le_max_left _ _
    linarith
  have hX : v - 1 / 2 ≤ X := by
    have : v + 1 ≤ X := le_max_right _ _
    linarith
  have hcont : ContinuousOn (Psi fl FF hHalf' hv hX) (Work.GATE2.slitAt v) :=
    Psi_cont fl FF hHalf' hv hX
  have hψv : Psi fl FF hHalf' hv hX (v : ℂ) = c₀ :=
    eq_c0_of_good hK hX hv
      (fun w hw => Psi_anti fl FF hHalf' hv hX (w := w) hw)
      (fun w hw => Psi_far fl FF hHalf' hv hX (w := w) hw)
      (Psi_cont fl FF hHalf' hv hX)
  refine ⟨⟨Psi fl FF hHalf' hv hX, X, hcont, hψv, ?_, ?_, ?_⟩⟩
  · intro w hw
    exact Psi_shift fl FF hHalf' hv hX (w := w) hw
  · intro w hw
    exact Psi_anti fl FF hHalf' hv hX (w := w) hw
  · intro w hw
    exact Psi_far fl FF hHalf' hv hX (w := w) hw

end

end Work.GATE2.PL
