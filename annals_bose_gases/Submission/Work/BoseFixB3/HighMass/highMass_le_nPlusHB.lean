import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.highMass_le_nPlusHB`

FS `eq:QLs_giveNplusH`: the `Q̄_L`-mass `Σᵢ∫_{Λⁿ}(Q̄_{L,i}Q_iΦ)² = highMass` is
dominated by the normalised high-momentum word
`n₊^H = ℓ⁻³Σᵢ∫_{Λⁿ}1_{Λ(0)}(xᵢ)·momForm(fibreᵢΦ x) = nPlusHB`,
at the FS cut-off `κ = (d²ℓ)⁻¹`.

The proof is the slot-by-slot inequality `slot_le_momForm` of `...HighMass.Core`
summed over `i : Fin n` (the case `n = 0` is the empty sum).
-/

namespace Work.BoseFixB3.HighMass

theorem highMass_le_nPlusHB {fc : Work.BoseBoxFix.LowCut} {κ ℓ d : ℝ}
    (hκ : κ = (d ^ 2 * ℓ)⁻¹) (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Work.BoseFixB3.highMass fc κ ℓ Φ ≤ Work.BoseBoxFix.nPlusHB ℓ d Φ := by
  rcases n with _ | m
  · simp [Work.BoseFixB3.highMass, Work.BoseBoxFix.nPlusHB]
  · rw [Work.BoseFixB3.highMass, Work.BoseBoxFix.nPlusHB, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => slot_le_momForm (fc := fc) hκ hℓ i hΦ)

end Work.BoseFixB3.HighMass
