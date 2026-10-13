/-
# `FTS/PhiStar/Honesty/ellWeakPos_psiSeries_of_cptQ` — the weak-class node for compact sources

**The theorem.**  For a source `G` which is `C^∞` on `ℝ²`, supported in a rectangle
`[a,b] × [c,d]` with `0 < a`, `0 < c < d < π/2` (`SmoothCptQ G`), whose angular moment vanishes
on `z > 0` (`F_* G ≡ 0`), and for `0 < α ≤ 1/4`, the mode series `psiSeries α G` is an honest
solution of the elliptic node at *every* level `K`:

  `TT.EllWeakPos α K G (psiSeries α G) ∧ IsBslSol α G (psiSeries α G)`.

**Why compact support matters.**  `CptQ` gives (i) every slice `G z ·` vanishes identically near
both angular endpoints, for *every* `z`, which is what makes the mode coefficients
`cmode m G z` decay faster than every power of `m`, *uniformly in* `z`
(`Honesty.cmode_decay_of_cptQ`, from the iterated angular engine
`Honesty.abs_cmode_le_lzero_iter_fix`); and (ii) every weighted derivative is bounded on the
support rectangle, so `G ∈ ℋ^k` for every `k` with no decay hypothesis
(`Honesty.smoothCptQ_hkMem`).  With super-polynomial modal decay the ℓ¹/Minkowski sums of the
level-`K` grid majorant converge *unconditionally*, so the two slot families `hσ` (`HkMem α 0` of
`D_z^l∂_θ^m Ψ`, `l ≤ K+2`, `m ≤ 2`) and `hV` (the vanishing-weight angular slots) are available —
this is exactly the case where the general-source route of `NOTES_hsigma_hV_K8.md` fails.

**Assembly.**  `slots_psiSeries_of_cptQ` supplies `(hσ, hV)`;
`psiSeries_smooth_of_cptQ` the open-quadrant smoothness;
`psiSeries_bslOp_of_cptQ` the equation; `hcoef_psiSeries` + `smoothCptQ_hkMem` the coefficient
summability and the `ℋ^K`-membership of the source; then
`ellWeakPos_K_psiSeries_of_level0` produces `TT.EllWeakPos`.  The `IsBslSol` half is
`isBslSol_psiSeries_of_cptQ` (equation + Dirichlet traces + decay at `z → ∞`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.PhiStar.Honesty.hcoef_psiSeries
import Submission.Work.FTS.PhiStar.Honesty.slots_psiSeries_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_smooth_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_bslOp_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.isBslSol_psiSeries_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_K_psiSeries_of_level0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The elliptic node for a compactly supported `C^∞` source, at every level.** -/
theorem ellWeakPos_psiSeries_of_cptQ (K : ℕ) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℝ → ℝ → ℝ} (hG : SmoothCptQ G)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α K G (Work.FTS.PhiStar.Series.psiSeries α G) ∧
      Work.Elliptic.IsBslSol α G (Work.FTS.PhiStar.Series.psiSeries α G) := by
  have hγ : Work.Spaces.gam α ≤ 3 / 2 := by
    simp only [Work.Spaces.gam]
    linarith
  obtain ⟨hσ, hV⟩ := slots_psiSeries_of_cptQ K hα hα4 hG hFs
  refine ⟨ellWeakPos_K_psiSeries_of_level0 K hα hα4 hγ (smoothCptQ_hkMem hG K)
    (psiSeries_smooth_of_cptQ hα hα4 hG)
    (fun z hz θ hθ hθ2 => psiSeries_bslOp_of_cptQ hα hα4 hG hFs z hz θ hθ hθ2)
    hFs (hcoef_psiSeries hα hα4 hG.smoothOpen (smoothCptQ_hkMem hG 0)) hσ hV, ?_⟩
  exact isBslSol_psiSeries_of_cptQ hα hα4 hG hFs

end Work.FTS.PhiStar.Honesty
