import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.ReflSymm
import Submission.Work.BoseBoxFock.coordSum_gram_FamV
import Submission.Work.BoseBoxFock.integrable_conj_FamV
import Submission.Work.BoseBoxFock.realIP_FamV_inl_inl
import Submission.Work.BoseBoxFock.realIP_FamV_inl_inr
import Submission.Work.BoseBoxFock.realIP_FamV_inr_inl
import Submission.Work.BoseBoxFock.realIP_FamV_inr_inr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.gramFamV` — the complex Gram matrix of the physical mode family

The honest box model of `Work.BoseBoxFock.Defs` pins the *real* pairings
`realIP f g = ∫ Re(conj f · g)` of the physical mode family `FamV` (the χ-modes
`Q(e^{ikx}χ_Λ)` on `Sum.inl`, the θ-modes `e^{isx}θ_Λ` on `Sum.inr`) through the
coordinate rows `f`, `g` of `HonestModes` (`hphys`, `hg`, `hcross`).  The model
basis however needs the **complex** Gram matrix
`∫ x, conj (V i x) · V j x`, and this module computes it: it is `ℓ³` times the
real `gram` pairing of the rows `CoordRow i`, `CoordRow j`, and therefore equals
the Gram matrix

  `∑ l, conj (CoordV i l) · CoordV j l`

of the coordinate vectors `CoordV i` of `ModeFam.lean`.

## The argument (three steps)

1. **The complex pairing is the complexification of the real one**
   (`cIP_FamV_eq_realIP`).  Every corpus mode is *real up to the reflection*
   `x ↦ -x` (`Work.BoseBoxFock.ReflSymm`), so the imaginary part of
   `conj (V i x) · V j x` is odd, and the substitution `x ↦ -x` (the Lebesgue
   measure is negation invariant) shows the integral is fixed by complex
   conjugation.  This needs integrability of the product, which is
   `Work.BoseBoxFock.integrable_conj_FamV`.

2. **The `realIP` Gram matrix of `FamV` is the `gram` Gram matrix of the rows
   `CoordRow`** (`realIP_FamV_gram`), assembled from the four row computations
   `realIP_FamV_inl_inl` (the χ-row, `HonestModes.hphys`), `realIP_FamV_inl_inr`
   and `realIP_FamV_inr_inl` (the mixed rows, `HonestModes.hcross` and
   `corpusBox_gram_values`), and `realIP_FamV_inr_inr` (the θ-row,
   `HonestModes.hg`/`hg0` and `corpusBox_gram_values`).  The uniform row
   `CoordRow` — the θ-fibre row `GRow`, which is `g s` for `s ≠ 0` and the
   condensate row `δ_0` for the label `0` — is what makes the label `0` (where
   `FamV (inr 0)` is the condensate `θ_Λ`) fit the same formula.

3. **The coordinate Gram matrix** (`coordSum_gram_FamV`): `CoordV i = ℓ^{3/2} ·
   CoordRow i` with `ℓ^{3/2}` a *real* scalar, so its complex Gram matrix is `ℓ³`
   times the real `gram` matrix of the rows.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **The complex pairing of two physical modes is the complexification of their
`realIP` pairing.**  Each mode of `FamV` is real up to the reflection
`x ↦ -x` (`Work.BoseBoxFock.ReflSymm`), so the imaginary part of the integrand is
an odd function and the pairing is fixed by complex conjugation. -/
theorem cIP_FamV_eq_realIP (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i j : Lab HM.N ⊕ Lab HM.N) :
    (∫ x, (starRingEnd ℂ) (FamV v μ HM i x) * FamV v μ HM j x)
      = ((Work.BoseK15.corpusBox.realIP (FamV v μ HM i) (FamV v μ HM j) : ℝ) : ℂ) := by
  have hsymm : ∀ k : Lab HM.N ⊕ Lab HM.N,
      ∀ x, (starRingEnd ℂ) (FamV v μ HM k (-x)) = FamV v μ HM k x := by
    intro k x
    rcases k with c | c
    · exact conj_qVec (ellH v μ) (kmomLab (ellH v μ) HM.N c) x
    · exact conj_thetaExp (ellH v μ) (kmomLab (ellH v μ) HM.N c) x
  rw [Work.BoseB4.BoxData.realIP_apply]
  exact integral_conj_reflsymm _ _ (hsymm i) (hsymm j) (integrable_conj_FamV v μ HM i j)

/-- **The `realIP` Gram matrix of the physical mode family** is `ℓ³` times the real
`gram` matrix of the coordinate rows `CoordRow`. -/
theorem realIP_FamV_gram (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i j : Lab HM.N ⊕ Lab HM.N) :
    Work.BoseK15.corpusBox.realIP (FamV v μ HM i) (FamV v μ HM j)
      = (ellH v μ) ^ 3 * Work.BoseB4.gram (CoordRow v μ HM i) (CoordRow v μ HM j) := by
  rcases i with k | s <;> rcases j with k' | t
  · exact realIP_FamV_inl_inl v μ HM k k'
  · exact realIP_FamV_inl_inr v μ HM k t
  · exact realIP_FamV_inr_inl v μ HM s k'
  · exact realIP_FamV_inr_inr v μ HM s t

theorem gramFamV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (HM : Work.BoseBoxFock.HonestModes v μ)
    (i j : Work.BoseBoxFock.Lab HM.N ⊕ Work.BoseBoxFock.Lab HM.N) :
    (∫ x, (starRingEnd ℂ) (Work.BoseBoxFock.FamV v μ HM i x)
        * Work.BoseBoxFock.FamV v μ HM j x)
      = ∑ l : Fin HM.m, (starRingEnd ℂ) (Work.BoseBoxFock.CoordV v μ HM i l)
          * Work.BoseBoxFock.CoordV v μ HM j l := by
  rw [cIP_FamV_eq_realIP v μ HM i j, realIP_FamV_gram v μ HM i j]
  exact (coordSum_gram_FamV v μ HM i j).symm

end Work.BoseBoxFock
