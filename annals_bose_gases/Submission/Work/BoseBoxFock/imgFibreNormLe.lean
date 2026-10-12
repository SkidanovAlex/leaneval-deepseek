import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.imagesFibre
import Submission.Work.BoseFixB1.nPlusCrossSqBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreNormLe` — the `L²`-contraction of the sector projections

On the centred box `abox n ℓ` the "condensate mean in slot `i`"

    `aP ℓ i F x = ℓ⁻³ ∫_{y ∈ acube ℓ} F (update x i y)`

is the *conditional expectation* of `F` with respect to the σ-algebra of functions that are
constant in the `i`-th slot; equivalently `aP ℓ i` is the orthogonal projection of `L²(abox n ℓ)`
onto that subspace, and `aQ ℓ i = 1 - aP ℓ i` is the complementary projection.  Both are therefore
`L²`-contractions, which is exactly the statement of the target:

    `imgFibreN ℓ (aP ℓ i F) ≤ imgFibreN ℓ F`,   `imgFibreN ℓ (aQ ℓ i F) ≤ imgFibreN ℓ F`,

where `imgFibreN ℓ G = ∫_{abox n ℓ} (G x)²`.

Both halves are already available in the corpus, since `imgFibreN` is *definitionally* the box
integral of the square:

* the `P`-half is `Submission.BoseGases.aP_sq_le` (`Submission/Q0Sector.lean`), the Jensen /
  Cauchy–Schwarz contraction `‖PᵢΦ‖² ≤ ‖Φ‖²`;
* the `Q`-half is `Work.BoseFixB1.aQ_sq_le` (`Submission/Work/BoseFixB1/nPlusCrossSqBound.lean`),
  which is the orthogonality algebra `∫(QᵢΦ)² = ∫Φ² − ∫(PᵢΦ)²` (`Submission.BoseGases.sq_norm_decomp`)
  together with the nonnegativity of `∫(PᵢΦ)²`.

No new mathematics is needed here: the target is the pointwise-combination wrapper.
-/

noncomputable section

namespace Work.BoseBoxFock

/-- Both sector projections contract the `L²` norm on the centred box. -/
theorem imgFibreNormLe {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i : Fin n}
    {F : Submission.BoseGases.X n → ℝ} (hF : Continuous F) :
    (Work.BoseBoxFock.imgFibreN ℓ (Submission.BoseGases.aP ℓ i F)
        ≤ Work.BoseBoxFock.imgFibreN ℓ F) ∧
    (Work.BoseBoxFock.imgFibreN ℓ (Submission.BoseGases.aQ ℓ i F)
        ≤ Work.BoseBoxFock.imgFibreN ℓ F) :=
  ⟨Submission.BoseGases.aP_sq_le hℓ i hF, Work.BoseFixB1.aQ_sq_le hℓ i hF⟩

end Work.BoseBoxFock
