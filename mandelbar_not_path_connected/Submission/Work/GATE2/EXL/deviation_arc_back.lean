import Mathlib
import Submission.Work.GATE2.CaseII
import Submission.Work.GATE2.EXL.deviation_shift_eq
import Submission.Work.GATE2.EXL.deviation_shift_window

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

/-- **The backwards leg of the `α₁`-deviation along the exit arc.**

Along a continuous curve `A` of the `Ψ`-plane whose two legs `A r` and `A r - 1` avoid the filled
Julia set (so that both lie in the critical domain) and on which the front deviation is small
(`< 1/16384`) and vanishes only at `r = 1` (where both legs have zero deviation), the deviation
of the *back* leg is exactly the deviation of the front leg divided by `1024`:

    deviation (Ψ (A r)) = 1024 · deviation (Ψ (A r - 1)).

The proof chains the two halves of the `1024`-fold Böttcher branch: `deviation_shift_window`
supplies the window `|deviation (Ψ (A r - 1))| < 1/2048` on the back leg, and then the forward
one-step relation `deviation_shift_eq` — applied to `z = Ψ (A r - 1)`, whose image under the high
return map is `fl.Ψ (A r)` by the equivariance `Ψ (w + 1) = F (Ψ w)` — converts that window into
the exact equality. -/
theorem deviation_arc_back {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (A : C(unitInterval, ℂ))
    (hK : ∀ r : unitInterval, fl.Ψ (A r) ∉ Work.EL.K c)
    (hK1 : ∀ r : unitInterval, fl.Ψ (A r - 1) ∉ Work.EL.K c)
    (hdev : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))| < 1 / 16384)
    (hzero : ∀ r : unitInterval,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r)) = 0 → r = 1)
    (hbase : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A 1 - 1)) = 0)
    (hbase1 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A 1)) = 0) :
    ∀ r : unitInterval,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r)) =
        1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1)) := by
  -- both legs lie in the critical domain because they avoid the filled Julia set
  have hcrit : ∀ r : unitInterval, fl.Ψ (A r - 1) ∈ Work.ParamRays.critDomain c :=
    fun r => Work.GATE2.D1.mem_critDomain_of_notMem_K d (hK1 r)
  have hcrit1 : ∀ r : unitInterval, fl.Ψ (A r) ∈ Work.ParamRays.critDomain c :=
    fun r => Work.GATE2.D1.mem_critDomain_of_notMem_K d (hK r)
  -- the root angle `1023 · α₁ = 371 ∈ ℤ`
  have hα : ∃ s : ℤ, 1023 * Work.EL.alpha1 = (s : ℝ) := by
    exact ⟨371, by norm_num [Work.EL.alpha1]⟩
  -- the window on the back leg, from the backwards reading of the shift
  have hwin : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))|
        < 1 / 2048 :=
    Work.GATE2.EXL.deviation_shift_window (c := c) (d := d) fl hα A hcrit hcrit1 hdev hzero hbase hbase1
  intro r
  -- the equivariance `Ψ (w + 1) = F (Ψ w)` identifies `fl.Ψ (A r - 1)'s image with `fl.Ψ (A r)`
  have hsh : fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)) := by
    have h := fl.Ψ_shift (A r - 1)
    rwa [sub_add_cancel] at h
  have hFz : Work.EL.F c (fl.Ψ (A r - 1)) ∈ Work.ParamRays.critDomain c := by
    rw [← hsh]; exact hcrit1 r
  -- the forward one-step relation, in the window of the back leg
  have hstep := Work.GATE2.EXL.deviation_shift_eq (c := c) (d := d) fl hα (hcrit r) hFz (hwin r)
  simpa [hsh] using hstep

end Work.GATE2.EXL
