import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1B.pairRung.winModeContentLeWord
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.term2a` — step 2 of the chain: the `[|q|-c]₊²` half of Term 2

`Submission/Work/BoseFixB1S/chainIntegralQdep` bounds the pairing word by

    boxA2 ≥ -S·X·(2π)⁻³∫ B q ²/(2𝒜 q)  -  (2π)⁻³∫ 𝒜 q · boxWinModePGen q ,

where `𝒜 q = [1/(n+1)]·[|q|-c]₊² + 2K_s(a v)/V`.  This module disposes of the **first half** of
the second term,

    [1/(n+1)]·(2π)⁻³ ∫ q, [|q|-c]₊² · boxWinModePGen a volA Ac χ Ψ q
      ≤ tBwordKinInd a Ac volA χ c Ψ ,

i.e. exactly the target's first right-hand row.  The only inputs are the sharp Cauchy–Schwarz
`Work.BoseFixB1B.pairRung.winModeContentLeWord`

    (2π)⁻³ ∫ q, [|q|-c]₊² · boxWinModePGen a volA Ac χ Ψ q ≤ N · tBdiagFormInd a Ac volA χ (fsKinCoeff c) Ψ

and the nonnegativity of the kinetic word (`Work.BoseFixB1.tBwordKinInd_nonneg`); the
`1/(N+1)` prefactor is absorbed by the trivial `N/(N+1) ≤ 1`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Term 2a of the chain.**  The `[|q|-c]₊²/(N+1)` half of the frame term is paid by the
kinetic word `tBwordKinInd` itself. -/
theorem term2a_le_word {N : ℕ} {a volA c : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    (hc : 0 < c) {hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ} :
    (1 / ((N : ℝ) + 1)) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
        Submission.BoseGases.fsKinCoeff c ‖q‖ * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ Work.UBBInputs8.tBwordKinInd a Ac volA χ c Ψ := by
  have h := winModeContentLeWord (n := N) ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp hχnn hc hΨc
  rw [Work.UBBInputs8.tBwordKinInd]
  have hW0 : 0 ≤ Work.UBBInputs8.tBdiagFormInd a Ac volA χ
      (Submission.BoseGases.fsKinCoeff c) Ψ := by
    have h1 := Work.BoseFixB1.tBwordKinInd_nonneg (a := a) (A := Ac) (volA := volA)
      (χ := χ) (c := c) (N := N) Ψ
    rwa [Work.UBBInputs8.tBwordKinInd] at h1
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  calc (1 / ((N : ℝ) + 1)) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          Submission.BoseGases.fsKinCoeff c ‖q‖ * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (1 / ((N : ℝ) + 1)) * ((N : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c) Ψ) := mul_le_mul_of_nonneg_left h hpos
    _ = ((N : ℝ) / ((N : ℝ) + 1)) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c) Ψ := by ring
    _ ≤ 1 * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c) Ψ := by
        rw [one_mul]
        have h1 : (1 : ℝ) - (N : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) := by
          field_simp
          ring
        have h2 : (0 : ℝ) ≤ (1 : ℝ) - (N : ℝ) / ((N : ℝ) + 1) := by
          rw [h1]; positivity
        nlinarith [mul_nonneg hW0 h2]
    _ = Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c) Ψ := one_mul _

end Work.BoseFixB1B.pairRung
