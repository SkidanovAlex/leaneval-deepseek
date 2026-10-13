/-
# Coercivity of the `H^k`-norm: `|f|²_{H^{k+1}} ≤ |f|²_{H^k} + |D_θf|²_{H^k} + |D_zf|²_{H^k}`

For a function `f` which is smooth on a neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd f`) and lies in `ℋ^{k+1}` (`Work.Spaces.HkMem α (k+1) f`), the
squared `H^{k+1}`-norm is dominated by the squared `H^k`-norms of `f`, `D_θ f` and `D_z f`:

  `HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (Dth f) + HkSq α k (Dz f)`

for `k ≥ 1`, with **no** restriction on `α`.

The proof is the same as `Work.Coercivity.HkSq_succ_le_of_smooth` (which additionally
assumes `0 < α`): combine the pointwise integrand comparison `HkIntegrand_succ_le_sum`
with the integration lemma `HkSq_le_sum_of_integrand_le`.  The only difference is that the
membership `HkMem α k (Dθ f)` is supplied by the hypothesis-free
`Work.Coercivity.HkMem_dth_free` instead of the `0 < α`-restricted `HkMem_dth`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkSq_succ_le_of_smooth
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.Coercivity.HkIntegrand_succ_le_sum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The `D_z` half of `HkMem` transfer, with no restriction on `α`. -/
theorem HkMem_dz_free (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkMem α k (Spaces.Dz f) :=
  HkMem_of_HkIntegrand_le α k hsm.Dz h (fun z hz θ hθ =>
    HkIntegrand_Dz_le α k hsm z θ hz hθ)

/-- **Coercivity of the `H^k`-norm.**  For `SmoothNbhd f` and `k ≥ 1`,
`HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (Dθ f) + HkSq α k (Dz f)`. -/
theorem HkSq_succ_le (α : ℝ) (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkSq α (k + 1) f
      ≤ Spaces.HkSq α k f + Spaces.HkSq α k (Spaces.Dth f) + Spaces.HkSq α k (Spaces.Dz f) := by
  have hf : Spaces.HkMem α k f := HkMem_mono α k hsm h
  have hdth : Spaces.HkMem α k (Spaces.Dth f) := (HkMem_dth α hα k hsm h).1
  have hdz : Spaces.HkMem α k (Spaces.Dz f) := HkMem_dz_free α k hsm h
  refine HkSq_le_sum_of_integrand_le (α := α) (m := k + 1) (k := k) (f := f) (g₁ := f)
    (g₂ := Spaces.Dth f) (g₃ := Spaces.Dz f) h hf hdth hdz ?_
  intro z hz θ hθ
  exact HkIntegrand_succ_le_sum α k hk hsm hz hθ

end Work.Coercivity
