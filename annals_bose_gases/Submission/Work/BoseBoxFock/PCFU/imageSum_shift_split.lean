import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.int_imageSum_eq_lowKer_add
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.imageSum_shift_split`

The `d = 0` split of the lattice image sum of the low-momentum kernel, at an **arbitrary** shift
`b : E3` (rather than at a coordinate `x j` of the configuration):

    Σ'_d Κ(u - b + ℓ•latVec d) = Κ(b - u) + Σ'_d (if d = 0 then 0 else Κ(u - b + ℓ•latVec d)) ,

integrated against the bounded measurable test function `u ↦ ψ(x[j ↦ u])`.

The `d = 0` term is the kernel with the reversed argument, which is `Κ(b - u)` because `Κ` is even
(`lowKer_neg`).

**Proof.**  This is the already-proved `int_imageSum_eq_lowKer_add` — the same identity at the
shift `x j` — applied to the configuration `x' = Function.update x j b`.  For that configuration
`x' j = b` and, for every `u`, `Function.update x' j u = Function.update x j u`
(`Function.update_idem`), so every occurrence of `x j` in the instance is literally `b`; the two
sides are then the two sides of the target.  (`int_imageSum_eq_lowKer_add` supplies the required
boundedness of the image sum on the box from `lowKer_imageSum_bound`.)
-/

namespace Work.BoseBoxFock.PCFU

theorem imageSum_shift_split (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ)
    (hψm : Measurable ψ) (hψb : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C) (x : Submission.BoseGases.X n)
    (b : EuclideanSpace ℝ (Fin 3)) :
    (∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = (∫ u in Submission.BoseGases.acube ℓ,
            ((Work.BoseBoxFock.PCFU.lowKer fc κ (b - u) : ℝ) : ℂ)
              * ((ψ (Function.update x j u) : ℝ) : ℂ))
        + ∫ u in Submission.BoseGases.acube ℓ,
            (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                  (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
  have h := int_imageSum_eq_lowKer_add fc hκ hℓ j ψ hψm hψb (Function.update x j b)
  simpa [Function.update_self, Function.update_idem] using h

end Work.BoseBoxFock.PCFU
