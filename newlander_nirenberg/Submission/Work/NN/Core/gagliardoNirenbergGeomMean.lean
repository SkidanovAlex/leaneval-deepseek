import Mathlib
import Submission.Work.NN.Core.CnPert

/-!
# The Gagliardo–Nirenberg inequality in "geometric mean" form on `ℂⁿ`

For `n ≥ 1` there is a constant `C > 0` such that every compactly supported `C¹` function
`W : ℂⁿ → ℂ` satisfies

  `‖W‖_{L^q}² ≤ C · ‖W‖_{L²} · ‖∇W‖_{L²}`,   `q = 2 · (2n)' = 4n/(2n-1)`,

where `(2n)'` is the conjugate exponent of `2n = dim_ℝ ℂⁿ`.  Equivalently
`‖W‖_{L^q} ≤ √C · ‖W‖_{L²}^{1/2} ‖∇W‖_{L²}^{1/2}`.

## Proof

Write `d = 2n = dim_ℝ ℂⁿ` and `q₀ = d' = d/(d-1)`, so that the target exponent is `q = 2 q₀`.
The Gagliardo–Nirenberg–Sobolev inequality of Mathlib
(`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`) in the case `p = 1` reads

  `‖v‖_{L^{q₀}} ≤ C₀ ‖∇v‖_{L¹}`.

Applying it to the real valued function `v = ‖W‖²` turns the left hand side into
`‖W‖²_{L^{q₀}} = ‖W‖_{L^{2q₀}}²` and, since `∇‖W‖² = 2 Re(conj(W) ∇W)`, the right hand side into
`2 C₀ ∫ ‖W‖ ‖∇W‖ ≤ 2 C₀ ‖W‖_{L²} ‖∇W‖_{L²}` by Cauchy–Schwarz.  This is the claim.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Work.NN.Core

/-- `‖f‖_{L²} = (∫ ‖f‖ ^ 2)^{1/2}`, in the `ℝ≥0∞`-valued form used by `ENNReal.lintegral_mul_le_Lp_mul_Lq`. -/
private theorem eLpNorm_two_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {β : Type*} [NormedAddCommGroup β] {f : α → β} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := by
  have h := eLpNorm_nnreal_eq_lintegral (p := (2:NNReal)) (by norm_num) (μ := μ) hf
  simpa using h

theorem gagliardoNirenbergGeomMean {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : Cn n → ℂ, ContDiff ℝ 1 W → HasCompactSupport W →
      (MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))) ^ 2 ≤
        ENNReal.ofReal C * MeasureTheory.eLpNorm W 2 MeasureTheory.volume *
          MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume := by
  classical
  -- `dim_ℝ ℂⁿ = 2n`.
  have hfin : Module.finrank ℝ (Cn n) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const, Fintype.card_fin, mul_comm]
  -- `q₀ = (2n)' = (dim_ℝ ℂⁿ)'`.
  set q : ℝ≥0 := NNReal.conjExponent (2 * n) with hq
  -- the constant of the `L¹`-Gagliardo–Nirenberg–Sobolev inequality on `ℂⁿ`.
  set G : ℝ≥0 := MeasureTheory.eLpNormLESNormFDerivOneConst (volume : Measure (Cn n)) (q:ℝ)
  refine ⟨2 * (G:ℝ) + 1, by positivity, ?_⟩
  intro W hW h2W
  have hq2 : (2 : ℝ≥0) * (n : ℝ≥0) = ((Module.finrank ℝ (Cn n) : ℕ) : ℝ≥0) := by
    rw [hfin]; push_cast; ring
  -- the Hölder conjugacy `(dim_ℝ ℂⁿ).HolderConjugate q₀`
  have hpq : ((Module.finrank ℝ (Cn n) : ℕ) : ℝ≥0).HolderConjugate q := by
    rw [hq, ← hq2]
    refine NNReal.HolderConjugate.conjExponent ?_
    rw [← NNReal.coe_lt_coe]; push_cast
    exact_mod_cast (by omega : 1 < 2 * n)
  -- `v = ‖W‖² : ℂⁿ → ℝ` is `C¹` with compact support.
  have hg : ContDiff ℝ 1 (fun z : Cn n => ‖W z‖ ^ (2:ℝ)) := hW.norm_rpow (by norm_num)
  have h2g : HasCompactSupport (fun z : Cn n => ‖W z‖ ^ (2:ℝ)) :=
    h2W.norm.rpow_const (by norm_num : (2:ℝ) ≠ 0)
  -- Gagliardo–Nirenberg–Sobolev with `p = 1` applied to `v`.
  have hGN := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one (volume : Measure (Cn n)) hg h2g hpq
  -- `‖v‖_{L^{q₀}} = ‖W‖_{L^{2q₀}}²`.
  have hA : eLpNorm (fun z : Cn n => ‖W z‖ ^ (2:ℝ)) (↑q) volume =
      (eLpNorm W ((2:ENNReal) * (q:ENNReal)) volume)^2 := by
    have h := MeasureTheory.eLpNorm_norm_rpow (μ := volume) W hW.continuous.aestronglyMeasurable
      (p := (q:ENNReal)) (q := (2:ℝ)) (by norm_num)
    rw [show (↑q * ENNReal.ofReal (2:ℝ)) = (2:ENNReal) * (↑q) from by
        rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num, mul_comm]] at h
    simpa using h
  -- `‖∇v‖_{L¹} ≤ 2 ‖W‖_{L²} ‖∇W‖_{L²}`.
  have hB : eLpNorm (fderiv ℝ (fun z : Cn n => ‖W z‖ ^ (2:ℝ))) 1 volume ≤
      2 * eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume := by
    have hmeasW : AEStronglyMeasurable W volume := hW.continuous.aestronglyMeasurable
    have hmeasdW : AEStronglyMeasurable (fderiv ℝ W) volume :=
      (hW.continuous_fderiv one_ne_zero).aestronglyMeasurable
    have hmeasg : AEStronglyMeasurable (fderiv ℝ (fun z : Cn n => ‖W z‖ ^ (2:ℝ))) volume :=
      (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hmeasg,
        eLpNorm_two_eq_lintegral hmeasW, eLpNorm_two_eq_lintegral hmeasdW]
    calc ∫⁻ z, ‖fderiv ℝ (fun z : Cn n => ‖W z‖ ^ (2:ℝ)) z‖ₑ ∂volume
        ≤ ∫⁻ z, 2 * (‖W z‖ₑ * ‖fderiv ℝ W z‖ₑ) ∂volume := by
          refine lintegral_mono fun z => ?_
          have h := enorm_fderiv_norm_rpow_le (f := W) (hW.differentiable one_ne_zero) (x := z)
            (p := (2:NNReal)) (by norm_num : (1:NNReal) < 2)
          have h' : (((2:NNReal):ℝ) - 1) = 1 := by norm_num
          rw [h', ENNReal.rpow_one, mul_assoc] at h
          exact h
      _ = 2 * ∫⁻ z, ‖W z‖ₑ * ‖fderiv ℝ W z‖ₑ ∂volume := lintegral_const_mul' 2 _ (by norm_num)
      _ ≤ 2 * ((∫⁻ z, ‖W z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) *
               (∫⁻ z, ‖fderiv ℝ W z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) := by
          gcongr 1
          exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume
            (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hmeasW.enorm hmeasdW.enorm
      _ = 2 * (∫⁻ z, ‖W z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) *
          (∫⁻ z, ‖fderiv ℝ W z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) := by rw [mul_assoc]
  -- `ofReal C = 2 * G + 1`.
  have hC : ENNReal.ofReal (2 * (G:ℝ) + 1) = 2 * (↑G : ENNReal) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_coe_nnreal, show ENNReal.ofReal (2:ℝ) = 2 by norm_num, ENNReal.ofReal_one]
  have hkey : (eLpNorm W ((2:ENNReal) * (q:ENNReal)) volume)^2 ≤
      ENNReal.ofReal (2 * (G:ℝ) + 1) * eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume := by
    calc (eLpNorm W ((2:ENNReal) * (q:ENNReal)) volume)^2
        = eLpNorm (fun z : Cn n => ‖W z‖ ^ (2:ℝ)) (↑q) volume := hA.symm
      _ ≤ ↑G * eLpNorm (fderiv ℝ (fun z : Cn n => ‖W z‖ ^ (2:ℝ))) 1 volume := hGN
      _ ≤ ↑G * (2 * eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume) := by gcongr
      _ = (2 * (↑G : ENNReal)) * (eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume) := by ring
      _ ≤ (2 * (↑G : ENNReal) + 1) * (eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume) := by
          gcongr; exact le_add_right le_rfl
      _ = ENNReal.ofReal (2 * (G:ℝ) + 1) * eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume := by
          rw [hC, mul_assoc]
  simpa [hq] using hkey

end Work.NN.Core
