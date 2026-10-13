/-
# `WProd5/Pointwise5` — the pointwise `𝒲^{5,∞}`-bounds on the `f`-side

The level-five instances of the `𝒲^{5,∞}`-bounds on `D_z`- and mixed derivatives that the
slot lemmas of the level-five product rule consume:

* `zpz_le_WlInf5` — `|z^j ∂_z^j f| ≤ |f|_{𝒲^{5,∞}}` for `j ≤ 5`;
* `zpz_Dth_le_WlInf5` — `|z^j ∂_z^j D_θ^a f| ≤ |f|_{𝒲^{5,∞}} (α+sin 2θ) sin(2θ)^{α/5}`
  for `1 ≤ a`, `j + a ≤ 5`;
* `dzIter_le_WlInf5` — `|D_z^b f| ≤ 100 |f|_{𝒲^{5,∞}}` for `b ≤ 5` (open quadrant);
* `mixed_le_WlInf5` — `|D_z^b D_θ^a f| ≤ 100 |f|_{𝒲^{5,∞}} (α+sin 2θ) sin(2θ)^{α/5}`
  for `1 ≤ a`, `a + b ≤ 5` (open quadrant).

These are the level-five shifts of the proved level-four lemmas
`Work.FTS.OpenPkg.DzIter_le_WlInf_open` / `Work.FTS.OpenPkg.Mixed_le_WlInf_open` (and of the
Bell-number bound `Work.Spaces.bell_le`, here `bell_le_five`: `bell n ≤ 100` for `n ≤ 5`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.WProductRule

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.WProd5

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The Bell numbers of the rows `0 ≤ n ≤ 5` are `1, 1, 2, 5, 15, 52`, all below `100`. -/
theorem bell_le_five (n : ℕ) (hn : n ≤ 5) : Work.Spaces.bell n ≤ 100 := by
  interval_cases n <;> decide

/-- `|z^j ∂_z^j f| ≤ |f|_{𝒲^{5,∞}}` for `j ≤ 5`, on the domain. -/
theorem zpz_le_WlInf5 {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 5 f)
    {j : ℕ} (hj : j ≤ 5) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |z ^ j * pzIter j f z θ| ≤ WlInf α 5 f := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h := pz_sup_bound α 5 f hmem j hj z θ hz hθ
  have hW := WlInf_nonneg α 5 f hmem
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  calc z ^ j * |pzIter j f z θ| ≤ z ^ j * (WlInf α 5 f / (z + 1) ^ j) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = WlInf α 5 f * (z / (z + 1)) ^ j := by rw [div_pow]; ring
    _ ≤ WlInf α 5 f * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        exact pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
    _ = WlInf α 5 f := mul_one _

/-- `|z^j ∂_z^j (D_θ^a f)| ≤ |f|_{𝒲^{5,∞}} (α+sin 2θ) sin(2θ)^{α/5}` for `1 ≤ a`,
`j + a ≤ 5`, on the domain. -/
theorem zpz_Dth_le_WlInf5 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 5 f)
    {a : ℕ} (ha : 1 ≤ a) {j : ℕ} (hja : j + a ≤ 5) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |z ^ j * pzIter j (DthIter a f) z θ| ≤
      WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h := pz_Dth_sup_bound α hα 5 f hmem a j ha hja z θ hz hθ
  have hW := WlInf_nonneg α 5 f hmem
  have hnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith [sin_two_nonneg' hθ]) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  have hle1 : (z / (z + 1)) ^ j ≤ 1 :=
    pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
  calc z ^ j * |pzIter j (DthIter a f) z θ|
      ≤ z ^ j * (WlInf α 5 f / (z + 1) ^ j
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = WlInf α 5 f * ((z / (z + 1)) ^ j
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        rw [div_pow]; ring
    _ ≤ WlInf α 5 f * (1 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle1 hnn) hW
    _ = WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring

/-- `|D_z^b f| ≤ 100 |f|_{𝒲^{5,∞}}` on the open quadrant, for `b ≤ 5`. -/
theorem dzIter_le_WlInf5 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : WlInfMem α 5 f)
    {b : ℕ} (hb : b ≤ 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |DzIter b f z θ| ≤ 100 * WlInf α 5 f := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_slice_z hf hθ
  have hDz : DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (scoef b k : ℝ) * (z ^ k * pzIter k f z θ) :=
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hslice b z hz'
  have hsum := abs_sum_scoef_mul_le b (WlInf α 5 f)
    (fun k => z ^ k * pzIter k f z θ)
    (fun k hk => zpz_le_WlInf5 hfm (le_trans hk hb) hzI hθI)
  have hbell : (bell b : ℝ) ≤ 100 := by exact_mod_cast bell_le_five b hb
  have hW := WlInf_nonneg α 5 f hfm
  calc |DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1),
          (scoef b k : ℝ) * (z ^ k * pzIter k f z θ)| := by rw [hDz]
    _ ≤ (bell b : ℝ) * WlInf α 5 f := hsum
    _ ≤ 100 * WlInf α 5 f := mul_le_mul_of_nonneg_right hbell hW

/-- `|D_z^b D_θ^a f| ≤ 100 |f|_{𝒲^{5,∞}} (α+sin 2θ) sin(2θ)^{α/5}` on the open quadrant,
for `1 ≤ a`, `a + b ≤ 5`. -/
theorem mixed_le_WlInf5 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : WlInfMem α 5 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 5) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |mixed b a f z θ| ≤ 100 * (WlInf α 5 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb5 : b ≤ 5 := by omega
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hW := WlInf_nonneg α 5 f hfm
  have hM : 0 ≤ WlInf α 5 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := mul_nonneg hW hY
  have hbound : ∀ k ≤ b, |z ^ k * pzIter k (DthIter a f) z θ|
      ≤ WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k hk => zpz_Dth_le_WlInf5 hα hfm ha (by omega) hzI hθI
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => DthIter a f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hf a hθ
  rw [mixed,
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := DthIter a f) hsmooth b z hz]
  have hsum := abs_sum_scoef_mul_le b
    (WlInf α 5 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * pzIter k (DthIter a f) z θ) hbound
  refine le_trans hsum ?_
  calc (bell b : ℝ) * (WlInf α 5 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      ≤ 100 * (WlInf α 5 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le_five b hb5) hM

end Work.FTS.StrongEps.H5.WProd5
