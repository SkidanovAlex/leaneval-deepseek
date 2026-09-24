import Mathlib
import Submission.Work.GM.S3.Base

/-!
# Auxiliary definitions for the GM (7.1) tail estimate

`phiMaj L Az D` is the two-piece majorant for `‖ĥ_t(mN)‖` used in `Work.GM.S3.s3_tail`:
it equals the uniform bound `Az = ∫w²` when `|m| ≤ L` and the decay bound `D/m²` when `|m| > L`.
With `L = T/N` (so that `L = N^{1/5}`) the sum over `m ∈ ℤ` is `O(L)`: the small-`m` part
contributes `O(L·Az)` and the large-`m` part contributes `O(D/L)`.
-/

namespace Work.GM.S3

/-- The two-piece majorant for `‖ĥ_t(mN)‖`: `Az` for `|m| ≤ L` and `D/m²` for `|m| > L`. -/
noncomputable def phiMaj (L Az D : ℝ) (m : ℤ) : ℝ :=
  if |(m : ℝ)| ≤ L then Az else D / (m : ℝ) ^ 2

end Work.GM.S3
