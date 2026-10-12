import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imgFibre2Aux
import Submission.Work.BoseBoxFock.sq_integral_boxPiSet_boxL_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre2_sq_le`

The **Cauchy–Schwarz bound for the mirror fibre** `imgFibre₂`.  Since

    imgFibre₂ ℓ p F G u v = (ℓ³)⁻¹ ∫_{x'} ∫_{s ∈ boxL} F (ins p u s x') · G (ins p u v x'),

the assertion is exactly the Cauchy–Schwarz inequality

    (∫_{x'}∫_s f · g)² ≤ (∫_{x'}∫_s f²) · (∫_{x'}∫_s g²)

for the two continuous functions `f (x', s) = F (ins p u s x')`,
`g (x', s) = G (ins p u v x')` on the compact box
`boxPiSet (pairFib2 n p) ℓ × boxL ℓ`, multiplied by the nonnegative constant `((ℓ³)⁻¹)²`.

The `L²`-Cauchy–Schwarz inequality over the product measure is the PROVED
`Work.BoseBoxFock.sq_integral_boxPiSet_boxL_le`; the only extra input is the continuity of the two
inserted factors, obtained from `contDiff_insertCoord2_comp` of `boxSmoothAux`.

`sorry`-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem imgFibre2_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F G : Submission.BoseGases.X n → ℝ} (hF : Continuous F) (hG : Continuous G)
    (u v : EuclideanSpace ℝ (Fin 3)) :
    (Work.BoseBoxFock.imgFibre₂ ℓ p F G u v) ^ 2
      ≤ ((ℓ ^ 3)⁻¹) ^ 2
        * (∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib2 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
              (F (Work.BoseBoxFock.insertCoord2 p u s x')) ^ 2)
        * (∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib2 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
              (G (Work.BoseBoxFock.insertCoord2 p u v x')) ^ 2) := by
  -- the two inserted factors are continuous on the compact box
  have hf : Continuous (fun z : (pairFib2 n p → E3) × E3 => F (insertCoord2 p u z.2 z.1)) :=
    hF.comp ((contDiff_insertCoord2_comp (p := p)
      (w₀ := fun _ : (pairFib2 n p → E3) × E3 => u)
      (w₁ := fun z : (pairFib2 n p → E3) × E3 => z.2)
      (x' := fun z : (pairFib2 n p → E3) × E3 => z.1)
      contDiff_const contDiff_snd contDiff_fst).continuous)
  have hg : Continuous (fun z : (pairFib2 n p → E3) × E3 => G (insertCoord2 p u v z.1)) :=
    hG.comp ((contDiff_insertCoord2_comp (p := p)
      (w₀ := fun _ : (pairFib2 n p → E3) × E3 => u)
      (w₁ := fun _ : (pairFib2 n p → E3) × E3 => v)
      (x' := fun z : (pairFib2 n p → E3) × E3 => z.1)
      contDiff_const contDiff_const contDiff_fst).continuous)
  -- Cauchy–Schwarz over the product of the two boxes
  have hCS := sq_integral_boxPiSet_boxL_le (ι := pairFib2 n p) hℓ hf hg
  have hmain : (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
        F (insertCoord2 p u s x') * G (insertCoord2 p u v x')) ^ 2
      ≤ (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
            (F (insertCoord2 p u s x')) ^ 2)
        * (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
            (G (insertCoord2 p u v x')) ^ 2) := hCS
  have hdef : imgFibre₂ ℓ p F G u v = (ℓ ^ 3)⁻¹ *
      (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
        F (insertCoord2 p u s x') * G (insertCoord2 p u v x')) := rfl
  rw [hdef]
  calc (((ℓ ^ 3)⁻¹) * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
            F (insertCoord2 p u s x') * G (insertCoord2 p u v x'))) ^ 2
      = ((ℓ ^ 3)⁻¹) ^ 2 * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
            F (insertCoord2 p u s x') * G (insertCoord2 p u v x')) ^ 2 := by ring
    _ ≤ ((ℓ ^ 3)⁻¹) ^ 2 * ((∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, (F (insertCoord2 p u s x')) ^ 2)
        * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, (G (insertCoord2 p u v x')) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = ((ℓ ^ 3)⁻¹) ^ 2 * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, (F (insertCoord2 p u s x')) ^ 2)
        * (∫ x' in boxPiSet (pairFib2 n p) ℓ,
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, (G (insertCoord2 p u v x')) ^ 2) := by ring

end Work.BoseBoxFock
