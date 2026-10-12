import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPairIntGenC2
import Submission.Work.BoseFixB1S.boxC2SumC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.boxPairDensFourier_re_eqC0`

The **real part** of the momentum-space box pair content is the `volA⁻¹`-multiple of the box
windowed pairing content, for a merely *continuous* window `χ` (vanishing off the measurable box
`A ⊆ acube ℓ`) and a merely *continuous* state `Φ`:

`(boxPairDensFourier volA ℓ A χ Φ q).re = volA⁻¹ · boxWinModeRGen ℓ volA A χ Φ q`.

The proof combines two ingredients:

* `Work.BoseFixB1S.boxC2SumC` — the box `(c2)` sum identity with weak (continuous) hypotheses:
  the double creation word at the mean-free windowed mode equals `volA` times `boxPairDensFourier`;
* `Work.BoseFixB1.boxTauPairingReduction_core` — the `τ`-side pairing reduction, which collapses
  the (complex) double creation at the anti-diagonal pair `(w, w̄)` onto the two *real* same-mode
  creations and yields `((boxWinModeRGen … : ℝ) : ℂ)`.

Combining the two (and using `boxWinModeC χ (-q) = conj (boxWinModeC χ q)`) shows that
`volA · boxPairDensFourier` is the real number `boxWinModeRGen`; taking real parts and cancelling
`volA ≠ 0` gives the claim.
-/

namespace Work.BoseFixB1B

theorem boxPairDensFourier_re_eqC0 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Φ q).re
      = volA⁻¹ * Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Φ q := by
  -- the box `(c2)` sum identity, at a merely continuous window and state
  have hC2 := Work.BoseFixB1S.boxC2SumC hA hℓ hAc hvolA hvolpos hχc hχs hχsupp hΦ q
  -- the `τ`-side pairing reduction
  have hred := Work.BoseFixB1.boxTauPairingReduction_core (volA := volA) (A := A)
    hA hℓ hAc hχc hχs hΦ q
    (fun x hx => Work.BoseFixB1.boxTauDagGen_comm_smooth hA hℓ hAc
      (Work.BoseFixB1.continuous_boxWinModeImSmooth volA A hχc q)
      (Work.BoseFixB1.continuous_boxWinModeReSmooth volA A hχc q)
      (Work.BoseFixB1.integral_boxWinModeImSmooth_eq_zero hℓ hAc hvolA hvolpos hχc hχs q)
      (Work.BoseFixB1.integral_boxWinModeReSmooth_eq_zero hℓ hAc hvolA hvolpos hχc hχs q)
      hΦ x hx)
    (Work.BoseFixB1.boxTauDagGen_pairing_integral hA hℓ hAc hvolpos
      (Work.BoseFixB1.continuous_boxWinModeReSmooth volA A hχc q) hΦ)
    (Work.BoseFixB1.boxTauDagGen_pairing_integral hA hℓ hAc hvolpos
      (Work.BoseFixB1.continuous_boxWinModeImSmooth volA A hχc q) hΦ)
  -- `volA · boxPairDensFourier` is the real number `boxWinModeRGen`
  have hval : (volA : ℂ) * Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Φ q
      = ((Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Φ q : ℝ) : ℂ) := by
    rw [← hC2, Work.BoseFixB1.boxWinModeC_neg_eq_star]
    exact hred
  have hre := congrArg Complex.re hval
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.ofReal_re] at hre
  rw [← hre, inv_mul_cancel_left₀ (ne_of_gt hvolpos)]

end Work.BoseFixB1B
