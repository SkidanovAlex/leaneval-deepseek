import ChallengeDeps
import Submission.Work.BoseBogFS.ZPE1E2Row
import Submission.Work.BoseBogFS.ZPLatticeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ZPE1E2Corrected` — the `E₁`–`E₂` row in the `W1At`/`W1ωAt` spelling

`Work.BoseBogFS.ZPE1E2Corrected` is the requested `ZPE1E2Compare` **with the integral
parenthesised**, i.e. the row the mass step of `Work.BoseBogFS.ZPLatticeRow` needs:

```
| (2π)⁻³ ℓ³ * (∫ p, Ŵ₁(p)²/(2‖p‖²)) - ℓ³ * Ŵ₁ω(0) | ≤ C * ℓ² * (∫W₁)² .
```

The statement requested under the name `ZPE1E2Compare` (kept byte-identical, with its `sorry`, in
`ZPE1E2Compare.lean`) is written with the `- ℓ³ * Ŵ₁ω(0)` clause on the line *after* the integral
body, and Lean's `∫ p, …` swallows it: see `FINDING_ZPE1E2Compare_misparsed.md` for the parse, the
machine checks, and the proof that the formalised version is vacuous.

This file is only the vocabulary change: its proof is `simpa only [Work.BoseBogFS.W1At,
Work.BoseBogFS.W1ωAt] using Work.BoseBogFS.ZPE1E2Row` (`ZPE1E2Row.lean`, which states and proves
the row in the raw `W1fun v h (ell v μ)` / `W1omegaFun v h (ell v μ)` vocabulary and depends on no
chapter file).

**To repair the requested node**: restate `ZPE1E2Compare` with the parentheses above — it is then
`exact Work.BoseBogFS.ZPE1E2Corrected` (or, without this file,
`simpa only [Work.BoseBogFS.W1At, Work.BoseBogFS.W1ωAt] using Work.BoseBogFS.ZPE1E2Row`).
-/

noncomputable section
open MeasureTheory Metric
open scoped Real

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

theorem ZPE1E2Corrected :
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v → tsupport v ⊆ Metric.ball 0 R →
      0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ ρ : ℝ, Work.BoseBoxFock.CloseCondFS v μ ρ →
          |((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
              * (∫ p : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ) p) ^ 2 / (2 * ‖p‖ ^ 2))
            - (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.chat (Work.BoseBogFS.W1ωAt v h μ) 0|
          ≤ C * (Work.BoseFixR.ell v μ) ^ 2
              * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.W1At v h μ x) ^ 2 :=
  ZPE1E2Row

end Work.BoseBogFS
