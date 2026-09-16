import Submission.ZagierHoffmanProof.ThakurDeg1
import Submission.ZagierHoffmanProof.ThakurDeg2
import Submission.ZagierHoffmanProof.ThakurDeg3
import Submission.ZagierHoffmanProof.ThakurDeg4
import Submission.ZagierHoffmanProof.DepthTwo

/-!
# The power-sum degree theory (Thakur) — index module

* `ThakurDeg1` : the power sums over `F` and the binomial coefficients `binF`.
* `ThakurDeg2` : the coercions into the completion and the truncated binomial expansion
  (`trunc_expansion`).
* `ThakurDeg3` : `jMin`, the valuation of the truncated series, and **Thakur 3.1**
  (`val_P_one`): `v (P_1(k)) = exp (−(k + j_min(k)))`.
* `ThakurDeg4` : **Thakur 2.2.5** (`v_P_le`): `v (P_d(k)) ≤ exp (−d (k + j_min(k)))`.
* `DepthTwo` : **non-vanishing of every depth-two MZV** (`zeta_pair_ne_zero`).
-/
