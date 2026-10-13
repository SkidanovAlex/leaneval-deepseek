import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.WProductRule
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `mixed_le_WlInf6`

Pointwise control of every mixed derivative `D_z^b D_θ^a f` inside the open quadrant by the
`𝒲^{6,∞}`-norm, for `f` of class `SmoothOpen` (`C^∞` on the open quadrant only) — the order-6
companion of `Work.FTS.OpenPkg.Mixed_le_WlInf_open` (which is the order-4 statement, constant
`100`).

The angular summands of the `𝒲^{6,∞}`-norm control
`(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α + sin 2θ)`; `Work.Spaces.pz_Dth_sup_bound` turns this
into the unweighted pointwise bound

`|z^k ∂_z^k D_θ^j f| ≤ |f|_𝒲 · (z+1)^{-k} (α + sin 2θ) sin(2θ)^{α/5}`   (`1 ≤ j`, `k + j ≤ 6`).

Combining this with the Stirling expansion of `D_z^b` in the genuine smooth order on the open
half-line (`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`) and
`Work.Spaces.abs_sum_scoef_mul_le` (the total coefficient mass is the Bell number
`bell b ≤ 203 ≤ 1000` for `b ≤ 6`) gives the stated bound with constant `1000`.
-/

open scoped Real

namespace Work.FTS.StrongPersist.N6Trans.L6FBound

/-- The Bell numbers of the rows `0 ≤ n ≤ 6` are `1, 1, 2, 5, 15, 52, 203`, all of them
well below `1000`. -/
theorem bell_le_six (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-- `|f|_{𝒲^{6,∞}} ≥ 0`. -/
theorem WlInf6_nonneg {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 6 f) :
    0 ≤ Work.Spaces.WlInf α 6 f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α 6 f hmem)
    (Work.Spaces.wlThSum_nonneg α 6 f hmem)

/-- `|z^j ∂_z^j (D_θ^a f)| ≤ |f|_𝒲 · sin(2θ)^{α/5}(α+sin 2θ)` for `1 ≤ a`, `j + a ≤ 6`. -/
theorem zpz_Dth_le_WlInf6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.WlInfMem α 6 f) {a : ℕ} (ha : 1 ≤ a) {j : ℕ} (hja : j + a ≤ 6)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z ^ j * Work.Spaces.pzIter j (Work.Spaces.DthIter a f) z θ| ≤
      Work.Spaces.WlInf α 6 f * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by
  have hz0 : (0:ℝ) ≤ z := hz
  have hz1 : (0:ℝ) < z + 1 := by linarith
  have h := Work.Spaces.pz_Dth_sup_bound α hα 6 f hmem a j ha hja z θ hz hθ
  have hW := WlInf6_nonneg hmem
  have hnn : 0 ≤ (α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5) :=
    mul_nonneg (by linarith [Work.Spaces.sin_two_nonneg' hθ])
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθ) _)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  have hle1 : (z/(z+1))^j ≤ 1 :=
    pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
  calc z ^ j * |Work.Spaces.pzIter j (Work.Spaces.DthIter a f) z θ|
      ≤ z ^ j * (Work.Spaces.WlInf α 6 f / (z+1)^j
          * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = Work.Spaces.WlInf α 6 f
          * ((z/(z+1))^j * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) := by
        rw [div_pow]; ring
    _ ≤ Work.Spaces.WlInf α 6 f
          * (1 * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle1 hnn) hW
    _ = Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by ring

theorem mixed_le_WlInf6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 6 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 1000 * (Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb6 : b ≤ 6 := by omega
  -- the angular factor is nonnegative, and so is the whole bound
  have hsin0 : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hM : 0 ≤ Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_nonneg (WlInf6_nonneg hfm) hY
  -- the pointwise bound for the individual `z^k ∂_z^k (D_θ^a f)`-terms
  have hbound : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ|
      ≤ Work.Spaces.WlInf α 6 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k hk => zpz_Dth_le_WlInf6 hα hfm ha (by omega) hzI hθI
  -- the Stirling expansion of `D_z^b` in the genuine smooth order on `(0,∞)`
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter a f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hf a hθ
  rw [Work.Spaces.mixed,
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter a f) hsmooth b z hz]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
    (Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) hbound
  refine le_trans hsum ?_
  calc (Work.Spaces.bell b : ℝ)
        * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      ≤ 1000 * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le_six b hb6) hM

end Work.FTS.StrongPersist.N6Trans.L6FBound
