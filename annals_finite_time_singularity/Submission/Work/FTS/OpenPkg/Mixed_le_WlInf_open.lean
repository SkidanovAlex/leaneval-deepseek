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

/-!
# `Mixed_le_WlInf_open`

Pointwise control of every mixed derivative `D_z^b D_θ^a f` (`1 ≤ a`, `a + b ≤ 4`) inside the
*open* quadrant by the `𝒲^{4,∞}`-norm, for `f` of class `SmoothOpen` (i.e. merely `C^∞` on the
open quadrant `(0,∞) × (0,π/2)`).

The angular summands of the `𝒲^{4,∞}`-norm control `(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5} /
(α + sin 2θ)`; `Work.Spaces.pz_Dth_sup_bound` turns this into the unweighted pointwise bound

`|z^k ∂_z^k D_θ^j f| ≤ |f|_𝒲 · (z+1)^{-k} (α + sin 2θ) sin(2θ)^{α/5}`   (`1 ≤ j`, `k + j ≤ 4`).

Combining this with the Stirling expansion of `D_z^b` in the genuine smooth order on the open
half-line (`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`, which is exactly the open-quadrant form
of the expansion) and `Work.Spaces.abs_sum_scoef_mul_le` (the total coefficient mass is the Bell
number `bell b ≤ 100` for `b ≤ 4`) gives the stated bound with constant `100`.
-/

open scoped Real

namespace Work.FTS.OpenPkg

theorem Mixed_le_WlInf_open {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 4) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 100 * (Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb4 : b ≤ 4 := by omega
  -- the angular factor is nonnegative, and so is the whole bound
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hfm)
      (Work.Spaces.wlThSum_nonneg α 4 f hfm)
  have hM : 0 ≤ Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := mul_nonneg hW hY
  -- the pointwise bound for the individual `z^k ∂_z^k (D_θ^a f)`-terms
  have hbound : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ|
      ≤ Work.Spaces.WlInf α 4 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k hk => Work.Spaces.zpz_Dth_le_WlInf hα hfm ha (by omega) hzI hθI
  -- the Stirling expansion of `D_z^b` in the genuine smooth order on `(0,∞)`
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter a f z' θ) (Set.Ioi 0) :=
    smoothOpen_DthIter_slice_z hf a hθ
  rw [Work.Spaces.mixed,
    DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter a f) hsmooth b z hz]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
    (Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) hbound
  refine le_trans hsum ?_
  calc (Work.Spaces.bell b : ℝ)
        * (Work.Spaces.WlInf α 4 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      ≤ 100 * (Work.Spaces.WlInf α 4 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Work.Spaces.bell_le b hb4) hM

end Work.FTS.OpenPkg
