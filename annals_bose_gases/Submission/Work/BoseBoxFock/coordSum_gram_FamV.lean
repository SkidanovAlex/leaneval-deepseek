import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.GramVDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.coordSum_gram_FamV` — the coordinate Gram row identity

`CoordV i` is, by `CoordV_eq_row`, the row `ℓ^{3/2} · CoordRow i` with `ℓ = ellH v μ`
a *real* row coerced to `ℂ`.  Hence the complex Gram matrix of `CoordV` is
`ℓ³` times the real Gram matrix `Work.BoseB4.gram = ∑ l, f l * g l` of the rows
`CoordRow i`, `CoordRow j` — the arithmetic rewriting that turns the physical
Gram comparison `Work.BoseBoxFock.gramFamV` into a statement about the coordinate
rows of the honest model.
-/

namespace Work.BoseBoxFock

theorem coordSum_gram_FamV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i j : Lab HM.N ⊕ Lab HM.N) :
    (∑ l : Fin HM.m, (starRingEnd ℂ) (CoordV v μ HM i l) * CoordV v μ HM j l)
      = ((((ellH v μ) ^ 3) * Work.BoseB4.gram (CoordRow v μ HM i) (CoordRow v μ HM j) : ℝ) : ℂ) := by
  -- every row of `CoordV` is a real row scaled by `ℓ^{3/2}`, so the term at `l` is
  -- `↑(ℓ³ · (CoordRow i l · CoordRow j l))`
  have hterm : ∀ l : Fin HM.m,
      (starRingEnd ℂ) (CoordV v μ HM i l) * CoordV v μ HM j l
        = (((ellH v μ) ^ 3 * (CoordRow v μ HM i l * CoordRow v μ HM j l) : ℝ) : ℂ) := by
    intro l
    rw [CoordV_eq_row, CoordV_eq_row, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_inj, ← ellH_prod]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Complex.ofReal_sum, Complex.ofReal_inj,
    Work.BoseB4.gram, Finset.mul_sum]

end Work.BoseBoxFock
