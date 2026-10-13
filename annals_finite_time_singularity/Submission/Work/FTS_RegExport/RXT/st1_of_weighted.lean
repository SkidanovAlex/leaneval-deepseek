/-
# `Work.FTS_RegExport.RXT.st1_of_weighted` — RX-St1, leaf S9

`St1Class α S (gS α (tauExt g))` from the weighted bound
`|D_z^jD_θ^i g(·,·,τ)| ≤ K·ω` on the six slots
`(j,i) ∈ {(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)}` (`RXT.idx`).

The four fields are proved in the sibling modules of this directory:

* `st1_stdata.st1_dthvan`, `st1_stdata.st1_quad` — the pointwise data (`dthvan`, `quad`);
* `st1_stdata2.st1_quad2` — the second `z`-derivative at the origin (`quad2`);
* `st1_angle.st1_hhθ`, `st1_angle.st1_hhθp` — the two `α`-Hölder angular moduli.

This file only assembles them (the constant `K` is first seen to be nonnegative, `st1_K_nonneg`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.st1_prelim
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXT.st1_angle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

theorem st1_of_weighted {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    {S K : ℝ} (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) := by
  have hK0 : 0 ≤ K := st1_K_nonneg (α := α) (g := g) (S := S) (K := K) hα hS hw
  exact ⟨⟨st1_dthvan (α := α) (g := g) (S := S) (K := K) hα hmin hS hw,
      st1_quad (α := α) (g := g) (S := S) (K := K) hα hmin hS hK0 hw⟩,
    ⟨st1_quad2 (α := α) (g := g) (S := S) (K := K) hα hmin hS hK0 hw⟩,
    st1_hhθ (α := α) (g := g) (S := S) (K := K) hα hα13 hmin hS hK0 hw,
    st1_hhθp (α := α) (g := g) (S := S) (K := K) hα hα13 hmin hS hK0 hw⟩

end Work.FTS_RegExport.RXT
