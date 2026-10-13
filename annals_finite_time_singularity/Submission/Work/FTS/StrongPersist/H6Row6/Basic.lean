/-
# `H6Row6/Basic` — the star-slot pairing lemma for the level-six `N`-row

This module contains the one *symmetric* form of the level-six Cauchy–Schwarz pairing that the
`N`-row assembly needs: `PieceStarBnd` prices the product `Aa · Ba` when `Aa` carries a
`𝒲^{6,∞}`-bound and `Ba` an `ℋ⁶`-bound; the star slots `F_*`, `D_θF_*`, `D_zF_*` of the row
carry the `𝒲^{6,∞}`-bound while the residual coefficients carry the `ℋ⁶`-bound, i.e. the two
roles are *swapped*.  `ip6_mul_starjet` is that swap, by commutativity of the product and
`IP6_congr`.

Everything here rests on the proved `PieceStarBnd` (`H6Rows/Npair6SupAux/PieceStarBnd.lean`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PieceStarBnd
import Submission.Work.FTS.StrongPersist.IP6Clauses
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.DzFstar_W6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The star-slot pairing: an `ℋ⁶`-priced coefficient against a `𝒲^{6,∞}`-priced slot.**

For `A` of class `ℋ⁶` (`C⁶` on the open quadrant, honest `ℋ⁶`, `|A|_{ℋ⁶} ≤ KB`) and `G` of
class `𝒲^{6,∞}` (`C⁶` on the open quadrant, `|G|_{𝒲^{6,∞}} ≤ KG`),

`|IP6 α (A·G) f| ≤ C α^{-1/2} KG · KB · |f|_{ℋ⁶}`.

This is the swap of `PieceStarBnd` (which prices `G·A` with `G` the `𝒲^{6,∞}` factor); the two
products agree pointwise, so `IP6_congr` on the open quadrant transfers the bound. -/
theorem ip6_mul_starjet : ∃ C : ℝ, 0 < C ∧
    ∀ {α KG KB : ℝ} {A G f : Fn},
    0 < α → α ≤ 1 → 0 ≤ KG → 0 ≤ KB →
    ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkNorm α 6 A ≤ KB →
    ContDiffOn ℝ 6 (Function.uncurry G) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.WlInfMem α 6 G → Work.Spaces.WlInf α 6 G ≤ KG →
    Work.FTS.StrongPersist.H6Adm α f →
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => A z θ * G z θ) f|
      ≤ C * α ^ (-(1 / 2 : ℝ)) * KG * KB * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PieceStarBnd
  refine ⟨C0, hC0pos, ?_⟩
  intro α KG KB A G f hα hα1 hKG hKB hAcd hAm hAnb hGcd hGwl hGnb hf
  -- `PieceStarBnd` with the roles of the two factors exchanged
  have hstar := hC0 (α := α) (KA := KG) (KB := KB) (Aa := G) (Ba := A) (f := f)
    hα hα1 hKG hKB hGcd hGwl hGnb hAcd hAm hAnb hf
  -- `A · G = G · A` pointwise, so the two pairings agree
  have hcongr : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      (fun z θ => A z θ * G z θ) f
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (fun z θ => G z θ * A z θ) f :=
    Work.FTS.StrongPersist.IP6_congr 1 1 1 1 1 1 1 1 1 1 α hα
      (fun z θ _ => by ring)
  rw [hcongr]
  exact le_trans hstar (le_of_eq (by ring))

end Work.FTS.StrongPersist.H6Row6
