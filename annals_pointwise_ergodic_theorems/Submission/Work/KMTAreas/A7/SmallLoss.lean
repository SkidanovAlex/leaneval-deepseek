import Mathlib
import Submission.Work.KMTAreas.A7.SmallLossOfBounds
import Submission.Work.KMTAreas.A7.SmallModelVar
import Submission.Work.KMTAreas.A7.SmallExcBound

namespace Work.KMTAreas.A7

/-- **Area A7, small scales** (Krause--Mirek--Tao, Annals 195 (2022), §7, at the exponents
`(p₁,p₂) ≠ (2,2)`): the §5 paraproduct columns restricted to the scales
`N ≤ splitCut ρ (max (max l₁ l₂) (max k₁ k₂))` obey the estimate with the loss
`2^{Aρ·max(max l₁ l₂)(max s₁ s₂)}`, using only the Ionescu--Wainger multiplier theorem `AreaA1`.

The proof splits the small-scale column family into the §6 model tuple, the model-approximation
error and the exceptional scales (`smallColTuple_eq_sum`) and combines the three estimates:

* `SmallModApprox` — the §6 model approximation `smallMainPart − smallModelTuple` (Proposition
  `mod-approx` + the functional calculus `bn-ident`, summed over the lacunary scales);
* `SmallModelVar` — the §7 variational estimate for the model tuple (two-dimensional
  Rademacher--Menshov + the single-scale bound `ssu`, via the shifted Calderón--Zygmund theorem);
* `SmallExcBound` — the crude single-scale bound for the exceptional small scales (whose
  parameters are bounded by `SmallExcSupport` as soon as `ρ ≤ 1/(8C₀)`);

glued by the assembly `SmallLossOfBounds`. -/
theorem SmallLoss :
    ∀ (P : Polynomial ℤ) (p₁ p₂ : ENNReal), 2 ≤ P.natDegree → 1 < p₁ → p₁ < ⊤ → 1 < p₂ → p₂ < ⊤ →
      p₁⁻¹ + p₂⁻¹ ≤ 1 → (p₁ ≠ 2 ∨ p₂ ≠ 2) → Work.KMTContract.AreaA1 →
      Work.KMTAreas.A7.VarpLossSmall P p₁ p₂ := by
  intro P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum _hneq hA1
  exact SmallLossOfBounds P p₁ p₂ hsum
    (SmallModApprox P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (SmallModelVar P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (SmallExcBound P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum)

end Work.KMTAreas.A7
