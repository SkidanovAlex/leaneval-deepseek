/-
# `Work.FTS.StrongPersist.H6Rows.wprod6` — the `𝒲^{6,∞}`-priced product rule at level six

The level-six shift of `Work.FTS.OpenPkg.wprod_field_winf` (the `wprod` clause of the primed
norm interface `OpenPkg.N4Norm'`, Elgindi's `WProductRule`, tex 1086, in the open-quadrant
class):

```
∃ C > 0, ∀ α ∈ (0,1], SmoothOpen f → WlInfMem α 6 f → HQo α 6 g →
    HkMem α 6 (f·g) ∧ |f·g|_{ℋ⁶} ≤ C α^{-1/2} |f|_{𝒲^{6,∞}} |g|_{ℋ⁶}.
```

The coefficient `f` is priced by the *weighted* norm `𝒲^{6,∞}` (`WlInf`/`WlInfMem`), so that it
need not lie in `ℋ⁶` — this is the form the level-six rows of the nonlinear estimate need for
the coefficients `F_*`, `D_θF_*`, `D_zF_*`.

The proof is assembled from
`WProd6/Gmaj6` (the pointwise majorant `GmajW6` and its integral estimates),
`WProd6/Majorant6` (the pointwise sum of the slots), the three slot lemmas
`WProd6/zslot_le_winf6`, `WProd6/dzIter_w_mean_le6`, `WProd6/mslot_le_winf6`, and
`WProd6/Assembly6` (`wprod6_of_slots`, the measure-theoretic assembly).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows

theorem wprod6 : ∃ Ci α₂ : ℝ, 0 < Ci ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.HQo α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g :=
  Work.FTS.StrongPersist.H6Rows.WProd6.wprod6_of_slots
    Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
    Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6
    Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6

end Work.FTS.StrongPersist.H6Rows
