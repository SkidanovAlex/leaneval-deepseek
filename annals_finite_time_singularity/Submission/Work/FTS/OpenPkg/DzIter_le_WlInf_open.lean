import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.Spaces.WProductRule

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `|D_z^b f| ≤ 100 |f|_{𝒲^{4,∞}}` in the open-quadrant class

For a function `f` which is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` (the class
`Work.FTS.EllipticEst.SmoothOpen`) and of class `𝒲^{4,∞}`, the iterated radial operator
`D_z = z ∂_z` is bounded by `100 |f|_{𝒲}` at every *interior* point `(z,θ)`, `z > 0`,
`0 < θ < π/2`, for `b ≤ 4`.

The proof is the open-quadrant instance of `Work.FTS.H2.WPQ.DzIter_le_WlInf`: expand
`D_z^b` with the Stirling numbers of the second kind via the half-line version
`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open` (`|z^j ∂_z^j f| ≤ |f|_𝒲` supplies the
coefficients), sum the (nonnegative) coefficients with `abs_sum_scoef_mul_le`, and use
the Bell number bound `bell b ≤ 100`.  The open-quadrant expansion is what makes the
argument available with only interior smoothness: the `z`-slices of a `SmoothOpen`
function are `C^∞` on `(0,∞)` only, which is exactly the input of the Stirling
expansion there.
-/

open scoped Real

namespace Work.FTS.OpenPkg

theorem DzIter_le_WlInf_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {b : ℕ} (hb : b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  -- the Stirling expansion of `D_z^b` on the open half-line
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi 0) :=
    smoothOpen_slice_z hf hθ
  have hDz : Work.Spaces.DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ) :=
    DzIter_eq_sum_scoef_open hslice b z hz'
  -- the coefficients: `|z^k ∂_z^k f| ≤ |f|_𝒲` for `k ≤ b ≤ 4`
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 4 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => Work.Spaces.zpz_le_WlInf hfm (le_trans hk hb) hzI hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le b hb
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hfm)
      (Work.Spaces.wlThSum_nonneg α 4 f hfm)
  calc |Work.Spaces.DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ)| := by rw [hDz]
    _ ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 4 f := hsum
    _ ≤ 100 * Work.Spaces.WlInf α 4 f := mul_le_mul_of_nonneg_right hbell hW

end Work.FTS.OpenPkg
