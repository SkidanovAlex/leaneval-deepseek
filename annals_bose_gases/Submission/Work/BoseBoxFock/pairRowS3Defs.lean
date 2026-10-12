import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.pairRowHonestRed
import Submission.Work.BoseBoxFock.pairRowS3Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS3Defs` — the pinned target of step (S3) of the `Q₂` row

`cIPn_potPairRows_eq` (`pairRowHonestRed`) writes the node's left-hand side *exactly* as

    rowPairSubC (ℓ³)⁻¹ Θ (pinCond v μ c) KI KII + B3

with `KI = K1exp (k1cfun fu W₁ W₁ω)`, `KII = K1exp (k1cfun fu W₁ 0)`.  Step (S2)
(`pairRowS2Bound`) replaces `K1exp` by its limit `K1lim` at a cost of `½·errKafz·normB`.  The
**remaining content** of the node is therefore the *limit-kernel comparison*

    (S3)   (rowPairSubC (ℓ³)⁻¹ Θ (pinCond v μ c) (pairRowNice ℓ W₁') (pairRowNice ℓ W₂')
              + pairRowB3 v h μ N c Θ).re
             ≤ q2word ℓ μ (wLoc ℓ (g₀ v h) 0) (wLoc ℓ (g₂ v h) 0) Φ + ½·errKafz v R μ C·normB

where

* `pairRowNice ℓ W := chiChiPart ℓ W + thetaPart ℓ W` — the `K1lim ℓ W` with its lattice images
  stripped: `K1lim ℓ W = pairRowNice ℓ W + chiChiImages ℓ W` (`K1lim_eq_parts`).  The first summand
  is `wLoc ℓ W 0` when `W = wScaled ℓ h` (the word's kernel), the second supplies the `Q`'s of
  FS `eq:DefQ2`;
* `pairRowB3` is the block-III term of `cIPn_potPairRows_eq` at the honest coefficients
  (`E.W1 0 = Ŵ₁(0)`, `E.W1omega0 = Ŵ₁ω(0)`; `pairRow_E_W1_zero`, `pairRow_E_W1omega_zero`);
* `W₁' = W1fun + W1omegaFun = wScaled ℓ (g₂ v h)` (block I's weight, FS's `w₂`),
  `W₂' = W1fun = wScaled ℓ (g₀ v h)` (blocks II's weight, FS's `w₁`) — `W1fun_add_W1omegaFun`.

**FS correspondence** (`FSsrc/final_v2.tex`, `lm:potsplit`/`lm:2ndQuand`): block I ↔ T1
(`Σ_{i≠j}P_iQ_jw₂P_jQ_i`), block II ↔ T4 (the anomalous `½(P_iP_jw₁Q_jQ_i + h.c.)`), block III ↔ T3
(`−μΣ_iQ_i(∫w₁)Q_i`), and T2 (`Σ_{i≠j}P_iQ_jw₂Q_jP_i`) is *free slack* on the right-hand side.
**VERDICT: TRUE — do not `declare_false`.**

The statement is `sorry`-free except for the (S3) theorem itself, which is stated for the record;
nothing imports this module.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The lattice-image-free part of the limit pair kernel: `chiChiPart + thetaPart`
(`K1lim ℓ W = pairRowNice ℓ W + chiChiImages ℓ W` for `W` supported in `ball 0 R`). -/
noncomputable def pairRowNice (ℓ : ℝ) (W : E3 → ℝ) : E3 → E3 → ℂ :=
  fun w y => chiChiPart ℓ W w y + thetaPart ℓ W w y

/-- **The block-III term of the `Q₂` row at the honest coefficients** (the two `K1exp(1)` slot sums
of `cIPn_potPairRows_eq` with `E.ell = ellH v μ`, `E.mu = μ`, `E.W1 0 = Ŵ₁(0)`,
`E.W1omega0 = Ŵ₁ω(0)`).  It is the counterpart of FS's T3 (`−μΣ_iQ_i(∫w₁)Q_i`) — see
`FINDING_PotPairRows_exists.md` §13.2/§13.4. -/
noncomputable def pairRowB3 {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (N : ℕ)
    (c : ℂ) (Θ : Work.BoseDict.Xn n → ℂ) : ℂ :=
  (((ellH v μ) ^ 3)⁻¹ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0
        + ((ellH v μ) ^ 3)⁻¹ * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (ellH v μ)) 0)
      • (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * pinCond v μ c (x p.1) * star (pinCond v μ c y)
              * K1exp v μ N (fun _ : Lab N => (1 : ℝ)) (x p.2) u
              * Θ (Function.update (Function.update x p.1 y) p.2 u))
    - (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0)
      • (∑ j : Fin n,
          ∫ x : Work.BoseDict.Xn n, ∫ y : E3,
            star (Θ x) * K1exp v μ N (fun _ : Lab N => (1 : ℝ)) (x j) y
              * Θ (Function.update x j y))

/-- `errKafz` is linear in its constant.  (A public restatement of the `private` twins in
`PotGroupAssembly.lean`/`frkCore.lean`; the copy in `RB4boxDomFS_of_bridge.lean` is outside the
target's cone — importing it would create an import cycle through `box_to_model`.) -/
lemma pairRow_errKafz_add (v : ℝ³ → ℝ) (R μ C₁ C₂ : ℝ) :
    Work.BoseFixR.errKafz v R μ (C₁ + C₂)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂ := by
  simp only [Work.BoseFixR.errKafz]
  ring

end Work.BoseBoxFock
