import Mathlib
import Submission.Work.GATE2.CaseII
import Submission.Work.GATE2.EXL.deviation_anti_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

/-- **The reflected (iota) leg of the `α₂`-deviation along an exit arc.**

Let `A` be a continuous curve of the `Ψ`-plane whose two legs `A r` and `A r - 1` avoid the filled
Julia set `K c` (so that both lie in the critical domain of `T_c`) and on which the `α₁`-deviation is
very small (`< 1/524288`).  The antiholomorphic square root `g = (T_c)^5` of the flower satisfies
`fl.Ψ (star w + 1/2) = g (fl.Ψ w)`, and along `g` the `α₂`-deviation is `−32` times the
`α₁`-deviation (`deviation_anti_eq`).  Hence the reflected points `fl.Ψ (star (A r) + 1/2)` and
`fl.Ψ (star (A r - 1) + 1/2)` have `α₂`-deviation smaller than `32 · (1/524288) = 1/16384`. -/
theorem deviation_arc_iota {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (A : C(unitInterval, ℂ))
    (hK : ∀ r : unitInterval, fl.Ψ (A r) ∉ Work.EL.K c)
    (hK1 : ∀ r : unitInterval, fl.Ψ (A r - 1) ∉ Work.EL.K c)
    (hdev : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))| < 1 / 524288)
    (hdev1 : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))| <
        1 / 524288) :
    (∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (A r) + 1 / 2))| < 1 / 16384) ∧
    (∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (A r - 1) + 1 / 2))| < 1 / 16384) := by
  -- both legs of the arc lie in the critical domain because they avoid the filled Julia set
  have hcrit : ∀ r : unitInterval, fl.Ψ (A r) ∈ Work.ParamRays.critDomain c :=
    fun r => Work.GATE2.D1.mem_critDomain_of_notMem_K d (hK r)
  have hcrit1 : ∀ r : unitInterval, fl.Ψ (A r - 1) ∈ Work.ParamRays.critDomain c :=
    fun r => Work.GATE2.D1.mem_critDomain_of_notMem_K d (hK1 r)
  constructor
  · intro r
    have hs : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))|
        < 1 / 64 := by linarith [hdev r]
    have heq := deviation_anti_eq (fl := fl) (hcrit r) hs
    rw [heq, abs_mul]
    rw [show |(-(32 : ℝ))| = 32 by norm_num]
    linarith [hdev r]
  · intro r
    have hs : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))|
        < 1 / 64 := by linarith [hdev1 r]
    have heq := deviation_anti_eq (fl := fl) (hcrit1 r) hs
    rw [heq, abs_mul]
    rw [show |(-(32 : ℝ))| = 32 by norm_num]
    linarith [hdev1 r]

end Work.GATE2.EXL
