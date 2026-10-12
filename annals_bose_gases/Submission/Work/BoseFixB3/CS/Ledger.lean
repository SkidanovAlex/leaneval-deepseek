import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Quant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB3.CS.Ledger` — the scalar ledger of the `CS` extraction

The `CS` step (`B3CSRoot`) is closed by the following accounting (see the analysis in
`CS/B3CSRoot_ANALYSIS.md` and this session's note): the two `3Q` words decompose as

    q3barWord + q3omWord
      = 2·Σ_p∫ F'_p·(q4B_p − ω_p·S_p)·w₁  +  2·leakCoupl·ppMass ,

and the leakage `2·leakCoupl·ppMass` is paid from the `4Q`-square `Σ_p∫(q4B_p)²·w` via the
**slot-constancy of `X_p = aP_{p.1}(aP_{p.2}Φ)`**: the identity

    q4B_p = ω_p·X_p + Y_p ,     Y_p = aQ_{p.2}(aQ_{p.1}Φ) + ω_p·S_p

multiplied by `ω_p·X_p` and integrated over the box gives, after Cauchy–Schwarz in `L²(w)`
and over the pair index,

    omegaSqCoupl·ppMass ≤ 2·q4Mass + 4·cMass + 4·sMassOm

(`extract_ppMass_le`), so that a super-polynomially small `leakCoupl` cannot contribute.

This module only fixes the vocabulary; the estimates live in `CS/Pieces/`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixB3.CS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

/-- The `4Q`-square of the pair bracket: `Σ_{p}∫_{Λ}(q4B_p)²·wgt(x_{p.1},x_{p.2})`. -/
def q4Mass (ℓ : ℝ) (om wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.q4B ℓ om Φ p x) ^ 2 * wgt (x p.1) (x p.2)

/-- The double-`Q` pair mass `Σ_p∫(Q_{p.2}Q_{p.1}Φ)²·wgt(x_{p.1},x_{p.2})`. -/
def cMass (ℓ : ℝ) (wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) ^ 2
      * wgt (x p.1) (x p.2)

/-- The `(P Q + Q P)`-pair mass with the `ω²`-weight inserted:
`Σ_p∫(P_{p.2}Q_{p.1}Φ + Q_{p.2}P_{p.1}Φ)²·(om(x_{p.1},x_{p.2}))²·wgt(x_{p.1},x_{p.2})`. -/
def sMassOm (ℓ : ℝ) (om wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
        + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
      * (om (x p.1) (x p.2)) ^ 2 * wgt (x p.1) (x p.2)

/-- The slot-constancy factorisation member appearing in `extract_ppMass_le`:
`Σ_p∫(P_{p.1}P_{p.2}Φ)²·(om)²·wgt` (equal to `omegaSqCoupl·ppMass` by `pp_sq_factor`). -/
def ppMassW (ℓ : ℝ) (om wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
      * (om (x p.1) (x p.2)) ^ 2 * wgt (x p.1) (x p.2)

end Work.BoseFixB3.CS
