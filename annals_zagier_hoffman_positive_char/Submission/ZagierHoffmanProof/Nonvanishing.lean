import Submission.ZagierHoffmanProof.StepL196
import Submission.ZagierHoffmanProof.StepL197
import Submission.ZagierHoffmanProof.StepL198
import Submission.ZagierHoffmanProof.StepL199
import Submission.ZagierHoffmanProof.StepL200
import Submission.ZagierHoffmanProof.StepL201
import Submission.ZagierHoffmanProof.StepL202
import Submission.ZagierHoffmanProof.StepL203
import Submission.ZagierHoffmanProof.StepL204
import Submission.ZagierHoffmanProof.CardTwoRegression
import Submission.ZagierHoffmanProof.StepL204Regression

/-!
# Index module: the non-vanishing thread (Steps L195–L204) and the `F₂` results

These modules are leaf modules (nothing else in the development imports them), so they are not
built by `lake build Submission` unless they are imported from the main chain.  This index
module keeps them in the verified build: `import Submission.ZagierHoffmanProof.Nonvanishing`
(or `lake build Submission.ZagierHoffmanProof.Nonvanishing`) builds and kernel-checks

* StepL196 (`ζ_A(1) ≠ 0`, `𝒵 F 1 ≠ ⊥`, the non-vanishing principle `val_tsum_eq_one_of`),
* StepL197 (Theorems B/D at weight `1`),
* StepL198 (`v (P_d(q))`, `ζ_A(q) ≠ 0`),
* StepL199 (★★★ `ζ_A(𝔰) ≠ 0` for all entries `≤ q`),
* StepL200 (corollaries: all-ones, all-`q`, `𝒵 F 2 ≠ ⊥`),
* StepL201 (Thakur's Frobenius relation `ζ_A(q·𝔰) = (ζ_A 𝔰)^q`),
* StepL202 (★★★ per-entry Frobenius scaling: `ζ_A(𝔰) ≠ 0` for `𝔰_j = q^{k_j}·m_j`, `m_j ≤ q`),
* StepL203 (★★★ **Theorems B and D over `F₂`**; `T_ne_zero`, `Z_ne_bot`, `rank_Z_pos`),
* StepL204 (`d F w > 0`; `𝒯 F w`/`𝒯0 F w` nonempty, finite, `ncard ≥ 1`),
* CardTwoRegression / StepL204Regression (the concrete instantiations at `ZMod 2`/`ZMod 3`,
  including the three challenge statements verbatim at `F = ZMod 2`).
-/
