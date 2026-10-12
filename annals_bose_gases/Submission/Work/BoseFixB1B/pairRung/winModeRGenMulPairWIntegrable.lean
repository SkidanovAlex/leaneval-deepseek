import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB1B.pairRung.boxWinModeRGen_one
import Submission.Work.BoseFixB1B.wMR_memLp_one_contDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.winModeRGenMulPairWIntegrable`

The `hintR` input of the `pairingRungBox` chain (`Work.BoseFixB1S.chainIntegralQdep`,
`Work.BoseFixB1S.chainCore.chain_integral`) at the regularity the sliding window actually
has, namely **`χ ∈ C²`** (the sliding window `chiSmallB M ℓ d u` is only `C^{M-1}`) and a
smooth state `Ψ`.

## The mathematical content (and why the decisive input is the *two-factor* Fourier picture)

`pairW 𝒲 : E3 → ℝ` is the (real part of the) Fourier transform of the `L¹` kernel `𝒲` at the
rescaled momentum `(2π)⁻¹q`; it is therefore only **bounded** (`|pairW 𝒲 q| ≤ ∫|𝒲|`), and in
general it is *not* `L¹`.  The momentum integral is finite because the windowed pairing
content `boxWinModeRGen` is *itself* a decaying Fourier object:

* `boxWinModeRGen = boxModeRGen (winModeReGen) + boxModeRGen (winModeImGen)` and
  `boxModeRGen g = ∫_{abox} (τ†a(g)Ψ)(τ†a₀(g)Ψ)`, a pairing of the two windowed amplitudes;
* the mean-free window `winModeReGen` makes the *annihilation* amplitude
  `∫_A g_q(z)Ψ(x_{i←z})dz` a compactly supported Fourier transform of a `C²` fibre, hence of
  size `(1+‖q‖)^{-2}`, and the *creation* amplitude acquires the same decay after the box
  mean is removed, so the pairing content decays like `(1+‖q‖)^{-4}` — integrable in
  dimension three;
* equivalently, and this is the version formalised here, `boxWinModeRGen` is (a multiple of)
  the real part of the Fourier transform of the box pair *density* `boxPairDensSum`, which
  for `χ ∈ C²` is a `C²` compactly supported function of the relative coordinate.  Its
  Fourier transform belongs to `L¹` in dimension three (`fourier_memLp_one_of_contDiff_two`
  via Plancherel + the weight `‖ξ‖⁴‖·‖²`), which is exactly the corpus's
  `Work.BoseFixB1B.wMR_memLp_one_contDiff` (whose hypotheses on `χ` are weaker than ours).

The product of the bounded factor `pairW 𝒲` with the `L¹` factor `boxWinModeRGen` is then
`L¹` (`Integrable.bdd_mul`), which is the target.

## Contents

* `boxWinModeRGen_integrableC2` — the `L¹` statement for the pairing content, in all
  dimensions (`n = 0` the slot sums are empty, `n = 1` the content vanishes identically
  (`boxWinModeRGen_one`), `n = N+2` it is `wMR_memLp_one_contDiff`);
* `pairW_bdd_and_aesm` — `pairW 𝒲` is bounded by `∫|𝒲|` and (a.e.) strongly measurable;
* `winModeRGenMulPairWIntegrable` — the target.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **The windowed pairing content is integrable in the momentum** for a continuous compactly
supported window `χ` vanishing off the measurable box `Ac ⊆ acube a` and a smooth state `Ψ`.

This is the `R`-half of `Work.BoseFixB1B.pairRung.winModeIntegrable`, with the `C^∞`-regularity
of `χ` weakened to continuity (all that `Work.BoseFixB1B.wMR_memLp_one_contDiff` needs), stated
for an arbitrary number `n` of particles:

* `n = 0`: the slot sums are empty, so the content vanishes;
* `n = 1`: the content vanishes identically in `q` (`boxWinModeRGen_one`);
* `n = N + 2`: `Work.BoseFixB1B.wMR_memLp_one_contDiff`. -/
theorem boxWinModeRGen_integrableC2 {n : ℕ} {a volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : E3 => Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
  rcases n with _ | m
  · -- `n = 0`: the slot sums are empty
    have h0 : ∀ q : E3, Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q = 0 := by
      intro q
      simp [Work.BoseFixB1.boxWinModeRGen, Work.BoseFixB1.boxModeRGen,
        Work.BoseFixB1.boxTauAnnGen, Work.BoseFixB1.boxTauDagGen]
    rw [funext h0]
    simp
  · rcases m with _ | k
    · -- `n = 1`: the content vanishes identically
      have h0 := boxWinModeRGen_one ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp hΨ.continuous
      have h0' : (fun q : E3 => Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
          = fun _ : E3 => (0 : ℝ) := funext (fun q => congrFun h0 q)
      rw [h0']
      simp
    · -- `n = k + 2`
      exact MeasureTheory.memLp_one_iff_integrable.mp
        (Work.BoseFixB1B.wMR_memLp_one_contDiff (N := k) hAcm ha hAcsub hvol hvolpos
          hχc hχs hχsupp hΨ)

/-- **The pairing weight `pairW 𝒲` is bounded by the `L¹` mass of the kernel, and is (a.e.)
strongly measurable** for every integrable `𝒲`.

Boundedness is `Submission.BoseGases.abs_pairW_le_integral_abs` (the Fourier transform of an
`L¹` function is dominated by its `L¹` norm); a.e. strong measurability follows from the
*continuity* of the Fourier transform of an `L¹` function
(`Submission.BoseGases.continuous_cfourier`). -/
theorem pairW_bdd_and_aesm {𝒲 : E3 → ℝ} (h𝒲 : MeasureTheory.Integrable 𝒲) :
    (∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ ∫ x : E3, |𝒲 x|)
      ∧ AEStronglyMeasurable (fun q : E3 => Submission.BoseGases.pairW 𝒲 q) := by
  have hbdd : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ ∫ x : E3, |𝒲 x| :=
    fun q => Submission.BoseGases.abs_pairW_le_integral_abs q
  have hcont : Continuous (fun q : E3 => Submission.BoseGases.pairW 𝒲 q) :=
    Complex.continuous_re.comp
      ((Submission.BoseGases.continuous_cfourier h𝒲).comp (continuous_const_smul _))
  exact ⟨hbdd, hcont.aestronglyMeasurable⟩

/-- The `hintR` input of `Work.BoseFixB1S.chainIntegralQdep` / `chainCore.chain_integral` at the
regularity the sliding window actually has: **`χ ∈ C²`** (`chiSmallB M ℓ d u` is `C^{M-1}`,
`M ≥ 3`) and `Ψ ∈ C^∞`, instead of `χ ∈ C^∞` (the corpus's `winModeIntegrableBox` /
`wMR_memLp_one_contDiff` at `n = N+2`).  Route: for the *windowed mean-free* modes
`g_q = 1_A(χ cos⟨q,·⟩ − mean)`, `1_A(χ sin⟨q,·⟩ − mean)` the slot amplitude
`∫_A g_q(z)Ψ(x_{i←z})dz` is a compactly-supported Fourier transform of a `C²` fibre, so it decays
like `(1+‖q‖)^{-2}`; the pairing content `boxWinModeRGen` is the sum of two *products* of two such
amplitudes, hence decays like `(1+‖q‖)^{-4}`, which is integrable in dimension three; `pairW 𝒲` is
bounded by `∫|𝒲|`.  (Note this genuinely needs the two-factor decay: `pairW 𝒲` is *not* `L¹` in
general, so boundedness of `boxWinModeRGen` alone would not do.) -/
theorem winModeRGenMulPairWIntegrable {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ2 : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) {κ : ℝ} (hκ : ∀ z, |χ z| ≤ κ)
    {𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ} (h𝒲 : MeasureTheory.Integrable 𝒲)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.pairW 𝒲 q * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
  obtain ⟨hbdd, haesm⟩ := pairW_bdd_and_aesm h𝒲
  exact (boxWinModeRGen_integrableC2 ha hAcm hAcsub hvol hvolpos hχ2.continuous hχs hχsupp
      hΨ).bdd_mul haesm
    (Filter.Eventually.of_forall (fun q => by rw [Real.norm_eq_abs]; exact hbdd q))

end Work.BoseFixB1B.pairRung
