import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.GalBasis.GalDense.Xmb
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.DzIter_eq_sum_scoef_of_contDiffOn_order

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

/-- **`|D_z^b f| ≤ 1000 |f|_{𝒲^{6,∞}}` in the `C⁶`-class on the open quadrant.**

For `f` of class `C⁶` on the open quadrant `(0,∞) × (0,π/2)` and of class `𝒲^{6,∞}`, the
iterated radial operator `D_z = z ∂_z` is bounded by `1000 |f|_𝒲` at every interior point,
for `b ≤ 6`.

The proof expands `D_z^b` with the Stirling numbers of the second kind
(`D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k`, which needs only `C^b ⊆ C⁶` on the open quadrant —
see `DzIter_eq_sum_scoef_of_contDiffOn_order`), bounds each term `|z^k ∂_z^k f|` by
`|f|_{𝒲^{6,∞}}` (`N6Trans.zpz_le_WlInf6`), and sums the (nonnegative) coefficients with
`Work.Spaces.abs_sum_scoef_mul_le` and the Bell number bound `bell b ≤ 203 ≤ 1000`
(`N6Trans.bell_le_six`). -/
theorem dzIter_le_WlInf6_cd6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfm : Work.Spaces.WlInfMem α 6 f) {b : ℕ} (hb : b ≤ 6) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨hz, hθ.1, hθ.2⟩
  -- the finite-order hypothesis at the level actually needed
  have hsm : ContDiffOn ℝ ((b : ℕ) : WithTop ℕ∞) (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 := hf.of_le (by exact_mod_cast hb)
  -- the Stirling expansion of `D_z^b`
  have hDz : Work.Spaces.DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) *
          (z ^ k * Work.Spaces.pzIter k f z θ) :=
    DzIter_eq_sum_scoef_of_contDiffOn_order Work.FTS.EllipticEst.isOpen_Q0 b hsm z θ hzθ
  -- the individual terms are bounded by the `𝒲^{6,∞}`-norm
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 6 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => Work.FTS.StrongPersist.N6Trans.zpz_le_WlInf6 hfm (le_trans hk hb) hzI hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by
    exact_mod_cast Work.FTS.StrongPersist.N6Trans.bell_le_six b hb
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  calc |Work.Spaces.DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) *
          (z ^ k * Work.Spaces.pzIter k f z θ)| := by rw [hDz]
    _ ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 6 f := hsum
    _ ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_le_mul_of_nonneg_right hbell hW

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
