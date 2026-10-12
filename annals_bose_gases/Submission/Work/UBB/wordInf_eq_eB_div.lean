import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.UBB

open Work.UBB Submission.BoseGases BoseGases MeasureTheory

/-- **`wordInf` is the per-box canonical infimum per unit volume.**

`wordInf` is the infimum of the shifted energy *density*
`WordDens = sboxE / (L³·∫ Φ²)` over `CSBox N L`, while `eB` is the infimum of
the shifted energy `sboxE / ∫ Φ²` (no volume normalisation).  Since
`a / (L³·b) = (a/b)/L³` and `L³ > 0`, the two infima differ exactly by the
factor `L³`: `wordInf = eB / L³`.

The pointwise identity uses `L³·b ≠ 0` (`b = ∫_{abox} Φ² > 0` by
`CSBox.sq_pos`), and the passage through the infimum is the order isomorphism
`x ↦ x·(L³)⁻¹` (`OrderIso.mulRight₀`); the hypothesis `BddBelow` of the
statement is exactly the conditional-boundedness side condition of
`OrderIso.map_ciInf`. -/
theorem wordInf_eq_eB_div {N : ℕ} {L μ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ScatSol v) (hL : 0 < L)
    (hbd : BddBelow (Set.range (fun Φ : CSBox N L =>
      (sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)))) :
    wordInf N L μ v h = eB N L μ v h / L ^ 3 := by
  have hLpos : (0 : ℝ) < L := hL
  haveI : Nonempty (CSBox N L) := nonempty_CSBox N hLpos
  -- Pointwise: the volume normalisation is a division by the constant `L³`.
  have hpt : ∀ Φ : CSBox N L, WordDens N L μ v h (Φ : X N → ℝ) =
      ((sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)) / L ^ 3 := by
    intro Φ
    unfold WordDens
    rw [mul_comm (L ^ 3) (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2), div_div]
  have hword : wordInf N L μ v h =
      ⨅ Φ : CSBox N L, ((sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)) / L ^ 3 := by
    unfold wordInf
    exact iInf_congr hpt
  have heB : eB N L μ v h =
      ⨅ Φ : CSBox N L, (sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2) := rfl
  rw [hword, heB]
  -- Division by the positive constant `L³` commutes with the infimum.
  simp only [div_eq_mul_inv]
  exact ((OrderIso.mulRight₀ ((L ^ 3)⁻¹) (inv_pos.mpr (by positivity))).map_ciInf hbd).symm

end Work.UBB
