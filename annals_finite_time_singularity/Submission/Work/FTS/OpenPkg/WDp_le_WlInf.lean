/-
Copyright: work module for the Elgindi finite-time singularity project.

# `OpenPkg/WDp_le_WlInf` — the `𝒲^{4,∞}`-norm controls the open-quadrant `D`-sup norm `WDp`

`Work.FTS.VocabO.WDp 4 f` is the sum of the suprema over the *open* quadrant of the mixed
derivatives `D_z^b D_θ^j f` with `b + j ≤ 4`, while `Work.Spaces.WlInf α 4 f` is the paper's
`𝒲^{4,∞}`-norm: the suprema of `(z+1)^k ∂_z^k f` (`k ≤ 4`) together with the angular-weighted
suprema of `(z+1)^k ∂_z^k D_θ^j f` (`1 ≤ j`, `k + j ≤ 4`).

The lemma proved here is the comparison promised in `Submission/Work/FTS/VocabO.lean`
("`WDp α l f ≤ C_l · WlInf α l f` on `SmoothOpen`"): there is a *universal* constant `C`
(independent of `α`) with `WDp 4 f ≤ C · WlInf α 4 f` for every `SmoothOpen` function of class
`WlInfMem α 4 f` and every `0 < α ≤ 1`.

The mathematical content is the Stirling expansion `D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k`
(`Submission/Work/FTS/OpenPkg/ScoefOpen.lean`, valid on the *open* half-line `(0,∞)` where the
`z`-slice is smooth — which is all the class `SmoothOpen` supplies), the two pointwise bounds
`|D_z^b D_θ^j f| ≤ 100 |f|_𝒲` (`DzIter_le_WlInf_open`) resp.
`|D_z^b D_θ^j f| ≤ 100 |f|_𝒲 · (α + sin 2θ) sin(2θ)^{α/5}` for `j ≥ 1`
(`Mixed_le_WlInf_open`, whose angular factor is `≤ 2` for `0 < α ≤ 1`), and the bookkeeping
lemma `WDp_le_of_pointwise` which turns pointwise bounds into the `WDp` estimate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity of the `𝒲^{4,∞}`-norm -/

/-- `WlInf α 4 f` is nonnegative as soon as its finitely many suprema are honest
(`WlInfMem α 4 f`): it is a sum of `supAbs`s, each of which is `≥ 0` under the honesty
hypotheses. -/
theorem wlInf_nonneg_of_mem {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    0 ≤ Work.Spaces.WlInf α 4 f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hmem) (Work.Spaces.wlThSum_nonneg α 4 f hmem)

/-! ## The pointwise bound with the universal constant `200` -/

/-- **Every mixed `D`-derivative of total order `≤ 4` of a `SmoothOpen`, `𝒲^{4,∞}`-function is
bounded by `200 |f|_{𝒲^{4,∞}}` inside the open quadrant.**

For `j = 0` this is the `D_z`-only bound (`DzIter_le_WlInf_open`); for `j ≥ 1` it is
`Mixed_le_WlInf_open` combined with the elementary bound
`(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2` (`0 < α ≤ 1`, `sin 2θ ≤ 1`). -/
theorem mixed_le_WlInf_200 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.WlInfMem α 4 f)
    {b j : ℕ} (hbj : b + j ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b j f z θ| ≤ 200 * Work.Spaces.WlInf α 4 f := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := wlInf_nonneg_of_mem hmem
  obtain rfl | hj := Nat.eq_zero_or_pos j
  · rw [Work.Spaces.mixed_zero_right]
    calc |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
          DzIter_le_WlInf_open hf hmem (by omega) hz hθ
      _ ≤ 200 * Work.Spaces.WlInf α 4 f := by linarith
  · have hs0 : 0 ≤ Real.sin (2 * θ) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hα5 : 0 ≤ α / 5 := by linarith
    have hΦ1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 hα5
    have hΦ2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [hΦ1, Real.rpow_nonneg hs0 (α / 5), hs0, hα]
    calc |Work.Spaces.mixed b j f z θ|
        ≤ 100 * (Work.Spaces.WlInf α 4 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Mixed_le_WlInf_open hα hf hmem hj (by omega) hz hθ
      _ ≤ 100 * (Work.Spaces.WlInf α 4 f * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ2 hW) (by norm_num)
      _ = 200 * Work.Spaces.WlInf α 4 f := by ring

/-! ## The comparison of the two norms -/

/-- **`WDp` is dominated by the `𝒲^{4,∞}`-norm**: there is a universal constant `C` with
`WDp 4 f ≤ C · WlInf α 4 f` for every `0 < α ≤ 1` and every `SmoothOpen` function
`f` of class `WlInfMem α 4 f`.

The constant is `25 · 200 = 5000`: the `WDp`-grid has `25` entries and
`mixed_le_WlInf_200` bounds each of them by `200 |f|_𝒲`. -/
theorem WDp_le_WlInf :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.WDp 4 f ≤ C * Work.Spaces.WlInf α 4 f := by
  refine ⟨5000, by norm_num, fun α f hα hα1 hf hmem => ?_⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := wlInf_nonneg_of_mem hmem
  have hM : (0 : ℝ) ≤ 200 * Work.Spaces.WlInf α 4 f := by positivity
  have hgrid := WDp_le_of_pointwise (α := α) (M := 200 * Work.Spaces.WlInf α 4 f) (f := f) hM
    (fun b j hbj z θ hz hθ hθ' => mixed_le_WlInf_200 hα hα1 hf hmem hbj hz ⟨hθ, hθ'⟩)
  calc Work.FTS.VocabO.WDp 4 f ≤ 25 * (200 * Work.Spaces.WlInf α 4 f) := hgrid
    _ = 5000 * Work.Spaces.WlInf α 4 f := by ring

end Work.FTS.OpenPkg
