import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

/-- The FS bookkeeping factor `1 + π⁻²` is positive (and in fact `≥ 1`). -/
private lemma one_add_pi_sq_inv_pos : (0 : ℝ) < 1 + (Real.pi ^ 2)⁻¹ := by positivity

/-- **The regularity hypothesis of `eq:appgapestimate` absorbs the excited
penalty into the `𝒯_B` gap coefficient.**

In FS's regime, the box kinetic energy scale `ε_T` is fixed so large that

    `ε_T ≥ 2(1+π⁻²)·(dℓ)²·C'²·μ·av`   (here `ε` is `ε_T` and `s = dℓ`),

which is precisely the hypothesis that the gap coefficient
`½ε_T(1+π⁻²)⁻¹(dℓ)⁻² = tbGapCoeff s ε` of `eq:appTB` dominates the
condensate-energy coefficient `C'²μ·av` of the excited count `n₊(B)`.
Combined with `tBword_gap_absorbs`, this is what lets `𝒯_B` pay for the whole
excited part of the box energy. -/
theorem gapCoeff_absorbs {s ε μ av C' : ℝ} (hav : 0 ≤ av) (hμ : 0 ≤ μ)
    (hC' : 0 ≤ C') (hε : 0 < ε) (hs : 0 < s)
    (hreg : 2 * (1 + (Real.pi ^ 2)⁻¹) * (s * C' * Real.sqrt (μ * av)) ^ 2 ≤ ε) :
    C' ^ 2 * μ * av ≤ Work.SmallBoxTBWord.tbGapCoeff s ε := by
  -- `P := 1 + π⁻²` is the reciprocal of the bookkeeping factor `tbPiFactor`,
  -- and `μ·av ≥ 0`, so `(s C' √(μ av))² = s² C'² μ av`.
  have hsq : (s * C' * Real.sqrt (μ * av)) ^ 2 = s ^ 2 * (C' ^ 2 * (μ * av)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hμ hav)]
    ring
  -- The regularity hypothesis, in the form `2 P s² (C'²μ av) ≤ ε`.
  have h2 : 2 * (1 + (Real.pi ^ 2)⁻¹) * (s ^ 2 * (C' ^ 2 * (μ * av))) ≤ ε := by
    rw [← hsq]; exact hreg
  have hD : 0 < 2 * (1 + (Real.pi ^ 2)⁻¹) * s ^ 2 := by
    have := one_add_pi_sq_inv_pos
    positivity
  -- Divide by the (positive) prefactor `2P s²`.
  have hmain : C' ^ 2 * μ * av ≤ ε / (2 * (1 + (Real.pi ^ 2)⁻¹) * s ^ 2) := by
    rw [le_div_iff₀ hD]
    nlinarith [h2]
  calc C' ^ 2 * μ * av
      ≤ ε / (2 * (1 + (Real.pi ^ 2)⁻¹) * s ^ 2) := hmain
    _ = Work.SmallBoxTBWord.tbGapCoeff s ε := by
        rw [tbGapCoeff, tbPiFactor]
        field_simp

end Work.SmallBoxTBWord
