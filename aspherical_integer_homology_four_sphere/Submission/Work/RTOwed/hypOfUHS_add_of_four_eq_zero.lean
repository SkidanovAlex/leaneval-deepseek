import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfKlein_injOn
import Submission.Work.HypModel.hypOfKlein_kleinOfHyp
import Submission.Work.HypModel.hypOfKlein_diagonal
import Submission.Work.HypModel.hypOfKlein_segment_pos_combo
import Submission.Work.HypModel.hypOfUHS_injOn
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.isLorentzMat_uhsTranslation
import Submission.Work.HypModel.kleinOfHyp_hypOfKlein
import Submission.Work.HypModel.kleinOfHyp_mem_ball
import Submission.Work.HypModel.mobiusKlein_isometry
import Submission.Work.HypModel.mobiusKlein_mem
import Submission.Work.HypModel.mobiusKlein_mul
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS
import Submission.Work.HypModel.mobius_isometry
import Submission.Work.HypModel.mobius_mul
import Submission.Work.HypModel.mobius_one
import Submission.Work.HypModel.mobius_uhsTranslation
import Submission.Work.HypModel.polarToUHS_isometry
import Submission.Work.HypModel.tangent_hypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The horospherical translation `x ↦ x + b` of the upper half space model acts by `uhsTranslation`

For `b : E4` with `b 3 = 0` — so that `b` is a purely horizontal translation vector — and for a
point `q` of the upper half space (`0 < q 3`), the chart point `q + b` (whose height is again
`q 3`) is the image of the chart point `q` under the Lorentz matrix `uhsTranslation b`:

`hypOfUHS (q + b) = (uhsTranslation b) *ᵥ hypOfUHS q`.

The proof identifies the right hand side as `hypOfUHS (uhsOfHyp ·)` of itself (both `uhsTranslation b`
is Lorentz, so it maps the upper sheet to itself, and `hypOfUHS ∘ uhsOfHyp` is the identity on the
upper sheet), and then uses `mobius_uhsTranslation`, which computes that `uhsOfHyp` of the image is
the horizontal translate `(q₀+b₀, q₁+b₁, q₂+b₂, q₃) = q + b`.
-/

namespace Work.RTOwed

open scoped Matrix InnerProductSpace

theorem hypOfUHS_add_of_four_eq_zero (b q : Work.HypModel.E4) (hb : b 3 = 0) (hq : 0 < q 3) :
    Work.HypModel.hypOfUHS (q + b) = (Work.HypModel.uhsTranslation b).mulVec (Work.HypModel.hypOfUHS q) := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  -- `uhsTranslation b` is a Lorentz matrix, so it preserves the upper sheet
  have hPmem : (Work.HypModel.uhsTranslation b).mulVec (Work.HypModel.hypOfUHS q) ∈
      Work.HypModel.upperSheet :=
    Work.HypModel.mulVec_mem_upperSheet (Work.HypModel.isLorentzMat_uhsTranslation b)
      ⟨Work.HypModel.lorentz_hypOfUHS_self hq3, Work.HypModel.hypOfUHS_four_pos hq⟩
  -- with `b 3 = 0`, the translation `q + b` has the same shape as the horizontal translate
  have hqb : q + b = !₂[q 0 + b 0, q 1 + b 1, q 2 + b 2, q 3] := by
    ext i
    fin_cases i <;> simp [hb]
  rw [hqb, ← Work.HypModel.hypOfUHS_uhsOfHyp hPmem]
  congr 1
  exact (Work.HypModel.mobius_uhsTranslation b hq).symm

end Work.RTOwed
